/* Private to Darwin executable pins. Simple compiler distributions use thin
 * Mach-O units in lib/ next to the executable. Other pins retain their
 * existing main-image-only contract. */
#include <mach-o/loader.h>
#include <sys/clonefile.h>
#include <copyfile.h>

#define OWNED_BUNDLE_UNITS 4
static const char *const owned_unit_names[OWNED_BUNDLE_UNITS] = {
    "libsimple-app.dylib", "libsimple-compiler.dylib",
    "libsimple-compiler-common.dylib", "libsimple-std.dylib"
};
typedef struct {
    unsigned present;
    unsigned staged;
    int directory_created;
    struct stat images[OWNED_BUNDLE_UNITS];
} OwnedDarwinBundle;

typedef struct {
    unsigned needed;
    int unsupported;
    int lib_rpath;
    int install_id;
} OwnedDarwinImports;

static int owned_unit_index(const char *path) {
    if (strncmp(path, "@rpath/", 7)) return -1;
    for (int i = 0; i < OWNED_BUNDLE_UNITS; ++i)
        if (!strcmp(path + 7, owned_unit_names[i])) return i;
    return -1;
}

/* Inspect the frozen bytes, before publishing the handle. No dyld execution
 * or ambient search path is involved in selecting an image. */
static int owned_darwin_imports(int fd, int unit, OwnedDarwinImports *out) {
    struct mach_header_64 h;
    memset(out, 0, sizeof(*out)); out->install_id = -1;
    if (pread(fd, &h, sizeof(h), 0) != sizeof(h)) return 0;
    if (h.magic != MH_MAGIC_64) return unit < 0; /* existing universal main pin */
    if (h.filetype != (uint32_t)(unit < 0 ? MH_EXECUTE : MH_DYLIB) ||
        h.sizeofcmds > 1024 * 1024 || h.ncmds > h.sizeofcmds / sizeof(struct load_command)) return 0;
    uint8_t *commands = malloc(h.sizeofcmds ? h.sizeofcmds : 1);
    if (!commands) return 0;
    int ok = pread(fd, commands, h.sizeofcmds, sizeof(h)) == (ssize_t)h.sizeofcmds;
    size_t at = 0;
    for (uint32_t i = 0; ok && i < h.ncmds; ++i) {
        struct load_command lc;
        if (h.sizeofcmds - at < sizeof(lc)) { ok = 0; break; }
        memcpy(&lc, commands + at, sizeof(lc));
        if (lc.cmdsize < sizeof(lc) || lc.cmdsize % 8 || lc.cmdsize > h.sizeofcmds - at) { ok = 0; break; }
        uint8_t *cmd = commands + at; at += lc.cmdsize;
        if (lc.cmd == LC_DYLD_ENVIRONMENT) { out->unsupported = 1; continue; }
        if (lc.cmd != LC_RPATH && lc.cmd != LC_LOAD_DYLIB && lc.cmd != LC_LOAD_WEAK_DYLIB &&
            lc.cmd != LC_REEXPORT_DYLIB && lc.cmd != LC_LOAD_UPWARD_DYLIB &&
            lc.cmd != LC_LAZY_LOAD_DYLIB && lc.cmd != LC_ID_DYLIB && lc.cmd != LC_LOAD_DYLINKER) continue;
        size_t min = (lc.cmd == LC_RPATH || lc.cmd == LC_LOAD_DYLINKER)
            ? sizeof(struct rpath_command) : sizeof(struct dylib_command);
        uint32_t offset;
        if (lc.cmdsize < min) { ok = 0; break; }
        memcpy(&offset, cmd + sizeof(lc), sizeof(offset));
        if (offset < min || offset >= lc.cmdsize || !memchr(cmd + offset, 0, lc.cmdsize - offset)) { ok = 0; break; }
        const char *name = (const char *)(cmd + offset);
        if (lc.cmd == LC_RPATH) {
            if (!strcmp(name, "@executable_path/lib") || (unit < 0 && !strcmp(name, "@loader_path/lib")))
                out->lib_rpath = 1;
            else if (strcmp(name, "@loader_path") && strcmp(name, "@executable_path"))
                out->unsupported = 1;
        } else if (lc.cmd == LC_LOAD_DYLINKER) {
            if (strcmp(name, "/usr/lib/dyld")) out->unsupported = 1;
        } else if (lc.cmd == LC_ID_DYLIB) {
            out->install_id = owned_unit_index(name);
        } else {
            int index = owned_unit_index(name);
            if (index >= 0) out->needed |= 1u << index;
            else if ((strncmp(name, "/usr/lib/", 9) && strncmp(name, "/System/Library/", 16)) ||
                     strstr(name, "/../")) out->unsupported = 1;
        }
    }
    free(commands); return ok && at == h.sizeofcmds;
}

static int owned_darwin_same_file(const struct stat *a, const struct stat *b) {
    return a->st_dev == b->st_dev && a->st_ino == b->st_ino && a->st_size == b->st_size &&
        a->st_ctimespec.tv_sec == b->st_ctimespec.tv_sec && a->st_ctimespec.tv_nsec == b->st_ctimespec.tv_nsec;
}

static int owned_darwin_copy_unit(int source, int dest, const char *name) {
    if (fclonefileat(source, dest, name, CLONE_NOOWNERCOPY) != 0) {
        if (errno != EXDEV && errno != ENOTSUP) return -1;
        int writer = openat(dest, name, O_WRONLY | O_CREAT | O_EXCL | O_NOFOLLOW | O_CLOEXEC, 0600);
        if (writer < 0) return -1;
        int ok = fcopyfile(source, writer, NULL, COPYFILE_DATA) == 0;
        if (close(writer) || !ok) return -1;
    }
    int fd = openat(dest, name, O_RDONLY | O_CLOEXEC | O_NOFOLLOW);
    if (fd >= 0 && fchmod(fd, 0500)) { close(fd); return -1; }
    return fd;
}

static int owned_darwin_absent_at(int dir, const char *name) {
    struct stat st;
    return fstatat(dir, name, &st, AT_SYMLINK_NOFOLLOW) < 0 && errno == ENOENT;
}

static int owned_darwin_source_trusted(const struct stat *st) {
    return (st->st_uid == geteuid() || st->st_uid == 0) && !(st->st_mode & (S_IWGRP | S_IWOTH));
}

static int owned_darwin_stage_bundle(const char *source_path, const struct stat *main_source,
                                     const char *directory, int main_fd, OwnedDarwinBundle *bundle) {
    OwnedDarwinImports main;
    if (!owned_darwin_imports(main_fd, -1, &main)) return 0;
    if (!main.needed) return 1;
    if (main.unsupported || !main.lib_rpath || !owned_darwin_source_trusted(main_source)) return 0;
    char parent[PATH_MAX];
    const char *slash = strrchr(source_path, '/');
    size_t n = (size_t)(slash - source_path);
    if (n >= sizeof(parent)) return 0;
    memcpy(parent, source_path, n); parent[n] = 0;
    const int dir_flags = O_RDONLY | O_DIRECTORY | O_NOFOLLOW | O_CLOEXEC;
    int root = open(n ? parent : "/", dir_flags), lib = -1, pin = -1, dest = -1, ok = 0;
    struct stat src[OWNED_BUNDLE_UNITS], st, initial_root, initial_lib;
    if (root < 0 || fstat(root, &initial_root) || !owned_darwin_source_trusted(&initial_root) ||
        (lib = openat(root, "lib", dir_flags)) < 0 || fstat(lib, &initial_lib) ||
        !owned_darwin_source_trusted(&initial_lib) ||
        (pin = open(directory, dir_flags)) < 0 || mkdirat(pin, "lib", 0700)) goto done;
    bundle->directory_created = 1;
    if ((dest = openat(pin, "lib", dir_flags)) < 0) goto done;
    unsigned needed = main.needed;
    off_t remaining = OWNED_DARWIN_PIN_MAX_BYTES;
    while (needed != bundle->present) {
        int i = 0;
        while (!((needed & ~bundle->present) & (1u << i))) ++i;
        const char *name = owned_unit_names[i];
        if (!owned_darwin_absent_at(root, name)) goto done; /* ambiguous sibling */
        int source = openat(lib, name, O_RDONLY | O_NOFOLLOW | O_NONBLOCK | O_CLOEXEC);
        if (source < 0) goto done;
        int copy = -1;
        if (!fstat(source, &src[i]) && S_ISREG(src[i].st_mode) && owned_darwin_source_trusted(&src[i]) &&
            src[i].st_size > 0 && src[i].st_size <= remaining) {
            remaining -= src[i].st_size;
            bundle->staged |= 1u << i;
            copy = owned_darwin_copy_unit(source, dest, name);
        }
        close(source);
        if (copy < 0) goto done;
        OwnedDarwinImports imports;
        int valid = !fstat(copy, &bundle->images[i]) && bundle->images[i].st_size == src[i].st_size &&
            owned_darwin_imports(copy, i, &imports) && imports.install_id == i && !imports.unsupported;
        close(copy);
        if (!valid) goto done;
        needed |= imports.needed; bundle->present |= 1u << i;
    }
    /* Bind the whole set in one publication. Detect a concurrent replacement
     * of any source image, the lib directory or the executable during staging. */
    if (lstat(n ? parent : "/", &st) || !owned_darwin_same_file(&initial_root, &st) || fstatat(root, "lib", &st, AT_SYMLINK_NOFOLLOW) ||
        !owned_darwin_same_file(&initial_lib, &st) || lstat(source_path, &st) ||
        !owned_darwin_same_file(main_source, &st)) goto done;
    for (int i = 0; i < OWNED_BUNDLE_UNITS; ++i)
        if ((needed & (1u << i)) && (!owned_darwin_absent_at(root, owned_unit_names[i]) ||
            fstatat(lib, owned_unit_names[i], &st, AT_SYMLINK_NOFOLLOW) ||
            !owned_darwin_same_file(&src[i], &st))) goto done;
    ok = 1;
done:
    if (dest >= 0) close(dest);
    if (pin >= 0) close(pin);
    if (lib >= 0) close(lib);
    if (root >= 0) close(root);
    return ok;
}

static int owned_darwin_check_bundle(const char *directory, const OwnedDarwinBundle *bundle, int remove) {
    if (!bundle->directory_created) return 1;
    const int flags = O_RDONLY | O_DIRECTORY | O_NOFOLLOW | O_CLOEXEC;
    int root = open(directory, flags);
    if (root < 0) return 0;
    int dir = openat(root, "lib", flags);
    if (dir < 0) { int ok = remove && errno == ENOENT; close(root); return ok; }
    struct stat st;
    int ok = !fstat(dir, &st) && st.st_uid == geteuid() && (st.st_mode & 07777) == 0700;
    for (int i = 0; i < OWNED_BUNDLE_UNITS; ++i) {
        const char *name = owned_unit_names[i];
        if (remove) {
            if ((bundle->staged & (1u << i)) && unlinkat(dir, name, 0) < 0 && errno != ENOENT) ok = 0;
        } else if (bundle->present & (1u << i)) {
            if (!owned_darwin_absent_at(root, name) || fstatat(dir, name, &st, AT_SYMLINK_NOFOLLOW) ||
                !S_ISREG(st.st_mode) || st.st_nlink != 1 || st.st_uid != geteuid() ||
                (st.st_mode & 07777) != 0500 || !owned_darwin_same_file(&bundle->images[i], &st)) ok = 0;
        }
    }
    close(dir);
    if (remove && unlinkat(root, "lib", AT_REMOVEDIR)) ok = 0;
    close(root); return ok;
}
