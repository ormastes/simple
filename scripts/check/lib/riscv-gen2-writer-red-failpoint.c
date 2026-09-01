/* Test-only syscall interposer for the Gen2 qualification writer reds.
 *
 * The production Simple composer has no awareness of this library.  It can
 * only turn one named write/rename operation into EACCES; it cannot fabricate
 * a successful receipt or bypass provenance/input admission.
 */
#define _GNU_SOURCE
#include <dlfcn.h>
#include <errno.h>
#include <fcntl.h>
#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/syscall.h>
#include <unistd.h>

static int ends_with(const char *path, const char *suffix) {
    size_t path_len;
    size_t suffix_len;
    if (path == NULL || suffix == NULL) return 0;
    path_len = strlen(path);
    suffix_len = strlen(suffix);
    return path_len >= suffix_len &&
        memcmp(path + path_len - suffix_len, suffix, suffix_len) == 0;
}

static int deny_write(const char *path, int flags) {
    const char *kind = getenv("RISCV_GEN2_TEST_DENY_KIND");
    const char *suffix = getenv("RISCV_GEN2_TEST_DENY_SUFFIX");
    return kind != NULL && strcmp(kind, "write") == 0 &&
        (flags & (O_WRONLY | O_RDWR | O_CREAT | O_TRUNC)) != 0 &&
        ends_with(path, suffix);
}

static int deny_fopen_write(const char *path, const char *mode) {
    const char *kind = getenv("RISCV_GEN2_TEST_DENY_KIND");
    const char *suffix = getenv("RISCV_GEN2_TEST_DENY_SUFFIX");
    return kind != NULL && strcmp(kind, "write") == 0 && mode != NULL &&
        (strchr(mode, 'w') != NULL || strchr(mode, 'a') != NULL ||
            strchr(mode, '+') != NULL) && ends_with(path, suffix);
}

static int deny_rename(const char *path) {
    const char *kind = getenv("RISCV_GEN2_TEST_DENY_KIND");
    const char *suffix = getenv("RISCV_GEN2_TEST_DENY_SUFFIX");
    return kind != NULL && strcmp(kind, "rename") == 0 &&
        ends_with(path, suffix);
}

static void record_hit(const char *kind, const char *path) {
    const char *marker = getenv("RISCV_GEN2_TEST_FAILPOINT_MARKER");
    long fd;
    if (marker == NULL || marker[0] == '\0') return;
    fd = syscall(SYS_openat, AT_FDCWD, marker,
        O_WRONLY | O_CREAT | O_APPEND, 0600);
    if (fd >= 0) {
        static const char kind_prefix[] = "kind=";
        static const char path_prefix[] = " path=";
        static const char newline[] = "\n";
        (void)syscall(SYS_write, fd, kind_prefix, sizeof(kind_prefix) - 1);
        (void)syscall(SYS_write, fd, kind, strlen(kind));
        (void)syscall(SYS_write, fd, path_prefix, sizeof(path_prefix) - 1);
        (void)syscall(SYS_write, fd, path, strlen(path));
        (void)syscall(SYS_write, fd, newline, sizeof(newline) - 1);
        (void)syscall(SYS_close, fd);
    }
}

static int open_needs_mode(int flags) {
    if ((flags & O_CREAT) != 0) return 1;
#ifdef O_TMPFILE
    if ((flags & O_TMPFILE) == O_TMPFILE) return 1;
#endif
    return 0;
}

int open(const char *path, int flags, ...) {
    static int (*next_open)(const char *, int, ...) = NULL;
    mode_t mode = 0;
    if (open_needs_mode(flags)) {
        va_list args;
        va_start(args, flags);
        mode = (mode_t)va_arg(args, int);
        va_end(args);
    }
    if (deny_write(path, flags)) {
        record_hit("write", path); errno = EACCES; return -1;
    }
    if (next_open == NULL) next_open = dlsym(RTLD_NEXT, "open");
    return open_needs_mode(flags) ? next_open(path, flags, mode) :
        next_open(path, flags);
}

int open64(const char *path, int flags, ...) {
    static int (*next_open64)(const char *, int, ...) = NULL;
    mode_t mode = 0;
    if (open_needs_mode(flags)) {
        va_list args;
        va_start(args, flags);
        mode = (mode_t)va_arg(args, int);
        va_end(args);
    }
    if (deny_write(path, flags)) {
        record_hit("write", path); errno = EACCES; return -1;
    }
    if (next_open64 == NULL) next_open64 = dlsym(RTLD_NEXT, "open64");
    return open_needs_mode(flags) ? next_open64(path, flags, mode) :
        next_open64(path, flags);
}

int openat(int dirfd, const char *path, int flags, ...) {
    static int (*next_openat)(int, const char *, int, ...) = NULL;
    mode_t mode = 0;
    if (open_needs_mode(flags)) {
        va_list args;
        va_start(args, flags);
        mode = (mode_t)va_arg(args, int);
        va_end(args);
    }
    if (deny_write(path, flags)) {
        record_hit("write", path); errno = EACCES; return -1;
    }
    if (next_openat == NULL) next_openat = dlsym(RTLD_NEXT, "openat");
    return open_needs_mode(flags) ? next_openat(dirfd, path, flags, mode) :
        next_openat(dirfd, path, flags);
}

int openat64(int dirfd, const char *path, int flags, ...) {
    static int (*next_openat64)(int, const char *, int, ...) = NULL;
    mode_t mode = 0;
    if (open_needs_mode(flags)) {
        va_list args;
        va_start(args, flags);
        mode = (mode_t)va_arg(args, int);
        va_end(args);
    }
    if (deny_write(path, flags)) {
        record_hit("write", path); errno = EACCES; return -1;
    }
    if (next_openat64 == NULL) next_openat64 = dlsym(RTLD_NEXT, "openat64");
    return open_needs_mode(flags) ? next_openat64(dirfd, path, flags, mode) :
        next_openat64(dirfd, path, flags);
}

FILE *fopen(const char *path, const char *mode) {
    static FILE *(*next_fopen)(const char *, const char *) = NULL;
    if (deny_fopen_write(path, mode)) {
        record_hit("write", path); errno = EACCES; return NULL;
    }
    if (next_fopen == NULL) next_fopen = dlsym(RTLD_NEXT, "fopen");
    return next_fopen(path, mode);
}

FILE *fopen64(const char *path, const char *mode) {
    static FILE *(*next_fopen64)(const char *, const char *) = NULL;
    if (deny_fopen_write(path, mode)) {
        record_hit("write", path); errno = EACCES; return NULL;
    }
    if (next_fopen64 == NULL) next_fopen64 = dlsym(RTLD_NEXT, "fopen64");
    return next_fopen64(path, mode);
}

int rename(const char *old_path, const char *new_path) {
    static int (*next_rename)(const char *, const char *) = NULL;
    if (deny_rename(new_path)) {
        record_hit("rename", new_path); errno = EACCES; return -1;
    }
    if (next_rename == NULL) next_rename = dlsym(RTLD_NEXT, "rename");
    return next_rename(old_path, new_path);
}

int renameat(int old_dirfd, const char *old_path,
        int new_dirfd, const char *new_path) {
    static int (*next_renameat)(int, const char *, int, const char *) = NULL;
    if (deny_rename(new_path)) {
        record_hit("rename", new_path); errno = EACCES; return -1;
    }
    if (next_renameat == NULL) next_renameat = dlsym(RTLD_NEXT, "renameat");
    return next_renameat(old_dirfd, old_path, new_dirfd, new_path);
}

int renameat2(int old_dirfd, const char *old_path,
        int new_dirfd, const char *new_path, unsigned int flags) {
    static int (*next_renameat2)(int, const char *, int, const char *, unsigned int) = NULL;
    if (deny_rename(new_path)) {
        record_hit("rename", new_path); errno = EACCES; return -1;
    }
    if (next_renameat2 == NULL) next_renameat2 = dlsym(RTLD_NEXT, "renameat2");
    return next_renameat2(old_dirfd, old_path, new_dirfd, new_path, flags);
}
