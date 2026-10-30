/* Included by runtime_process_owned.c on Linux only. One broker owns one
 * grouped compiler attempt. The worker enters a fresh monitored cgroup
 * atomically in clone3, before its first instruction or execveat. */
#include "runtime_linux_cgroup_events_private.h"
#include <linux/magic.h>
#include <linux/memfd.h>
#include <linux/sched.h>
#include <errno.h>
#include <ctype.h>
#include <fcntl.h>
#include <limits.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>
#include <sys/statfs.h>
#include <sys/statvfs.h>
#include <sys/mman.h>
#include <sys/syscall.h>
#include <sys/wait.h>
#include <time.h>
#include <unistd.h>

#ifndef CGROUP2_SUPER_MAGIC
#define CGROUP2_SUPER_MAGIC 0x63677270
#endif
#ifndef AT_EMPTY_PATH
#define AT_EMPTY_PATH 0x1000
#endif
#ifndef F_ADD_SEALS
#define F_ADD_SEALS 1033
#define F_SEAL_SEAL 0x0001
#define F_SEAL_SHRINK 0x0002
#define F_SEAL_GROW 0x0004
#define F_SEAL_WRITE 0x0008
#endif
extern char **environ;

typedef struct {
    int active, collected, parent_fd, group_fd, pidfd;
    pid_t pid;
    char name[80];
    int64_t started_ms, timeout_ms, peak, current;
    int leader_reaped, tree_empty, timed_out, cancelled, exit_code, kill_pending;
} RtLinuxGroup;

static RtLinuxGroup rt_linux_group = {0};

/* An explicit acquisition owns an EMPTY parent; the broker stays outside it.
 * Only this fresh parent's subtree_control may be changed. */
static struct {
    int active, root_fd, parent_fd;
    int64_t token;
    dev_t device;
    ino_t inode;
    char name[80], identity[65], attempt[4096];
} rt_lg_delegation;
static int64_t rt_lg_next_parent_token;

static int rt_lg_copy_text(const char *data, uint64_t len, char *out, size_t cap) {
    if (!data || !out || len == 0 || len >= cap || memchr(data, 0, (size_t)len))
        return 0;
    memcpy(out, data, (size_t)len); out[len] = 0; return 1;
}

static int rt_lg_read_fd(int fd, char *out, size_t cap) {
    if (fd < 0 || !out || cap < 2) return 0;
    ssize_t n = read(fd, out, cap - 1);
    if (n < 0) return 0;
    if (n == 0) { errno = ENODATA; return 0; }
    if (memchr(out, 0, (size_t)n)) { errno = EPROTO; return 0; }
    if ((size_t)n >= cap - 1) { errno = EOVERFLOW; return 0; }
    out[n] = 0; return 1;
}

static int rt_lg_read_at(int dir, const char *name, char *out, size_t cap) {
    int fd = openat(dir, name, O_RDONLY | O_CLOEXEC | O_NOFOLLOW);
    if (fd < 0) return 0;
    int ok = rt_lg_read_fd(fd, out, cap);
    close(fd); return ok;
}

static int rt_lg_write_at(int dir, const char *name, const char *data) {
    int fd = openat(dir, name, O_WRONLY | O_CLOEXEC | O_NOFOLLOW);
    if (fd < 0) return 0;
    size_t size = strlen(data);
    ssize_t written = write(fd, data, size);
    int saved = errno;
    int closed = close(fd);
    if (written != (ssize_t)size || closed != 0) { errno = saved ? saved : EIO; return 0; }
    return 1;
}

static int rt_lg_number(const char *text, int64_t *value) {
    if (!text || !value || !(*text >= '0' && *text <= '9')) return 0;
    uint64_t result = 0;
    const char *p = text;
    for (; *p >= '0' && *p <= '9'; p++) {
        if (result > (uint64_t)INT64_MAX / 10) return 0;
        result = result * 10 + (uint64_t)(*p - '0');
        if (result > INT64_MAX) return 0;
    }
    if (*p != 0 && !(*p == '\n' && p[1] == 0)) return 0;
    *value = (int64_t)result; return 1;
}

static int rt_lg_parent(void) {
    FILE *file = fopen("/proc/self/cgroup", "re");
    if (!file) return -1;
    char line[4096], path[4096]; int found = 0;
    while (fgets(line, sizeof(line), file)) {
        if (strncmp(line, "0::/", 4) == 0) {
            size_t n = strcspn(line + 3, "\r\n");
            if (n == 0 || n > sizeof(path) - 15) break;
            memcpy(path, "/sys/fs/cgroup", 14);
            memcpy(path + 14, line + 3, n); path[14 + n] = 0;
            found = 1; break;
        }
    }
    fclose(file);
    if (!found || strstr(path, "/../") || strstr(path, "/./")) return -1;
    int fd = open(path, O_RDONLY | O_DIRECTORY | O_CLOEXEC | O_NOFOLLOW);
    struct statfs fs;
    if (fd < 0) return -1;
    if (fstatfs(fd, &fs) != 0 || (unsigned long)fs.f_type != CGROUP2_SUPER_MAGIC) {
        close(fd); errno = ENOTSUP; return -1;
    }
    return fd;
}

/* V2 accepts only a canonical, fd-walkable absolute directory. Every
 * component is opened without following symlinks; textual prefixes are never
 * used as an ancestry proof. */
static int rt_lg_canonical_path(const char *path) {
    if (!path || path[0] != '/') return 0;
    if (path[1] == 0) return 1;
    if (path[strlen(path) - 1] == '/') return 0;
    const char *at = path + 1;
    while (*at) {
        const char *end = strchr(at, '/');
        size_t n = end ? (size_t)(end - at) : strlen(at);
        if (!n || (n == 1 && at[0] == '.') ||
            (n == 2 && at[0] == '.' && at[1] == '.') ||
            memchr(at, '\\', n)) return 0;
        at += n;
        if (*at == '/') { at++; if (!*at) return 0; }
    }
    return 1;
}

static int rt_lg_open_absolute_dir(const char *path) {
    if (!rt_lg_canonical_path(path)) { errno = EINVAL; return -1; }
    int current = open("/", O_RDONLY | O_DIRECTORY | O_CLOEXEC | O_NOFOLLOW);
    if (current < 0) return -1;
    const char *at = path + 1;
    while (*at) {
        const char *end = strchr(at, '/');
        size_t n = end ? (size_t)(end - at) : strlen(at);
        char component[NAME_MAX + 1];
        if (!n || n > NAME_MAX) { close(current); errno = ENAMETOOLONG; return -1; }
        memcpy(component, at, n); component[n] = 0;
        int next = openat(current, component, O_RDONLY | O_DIRECTORY | O_CLOEXEC | O_NOFOLLOW);
        int saved = errno; close(current); current = next; errno = saved;
        if (current < 0) return -1;
        at += n; if (*at == '/') at++;
    }
    return current;
}

static int rt_lg_read_proc_file(const char *file_name, char **contents, size_t *length) {
    const size_t cap = 1024 * 1024;
    int fd = open(file_name, O_RDONLY | O_CLOEXEC);
    if (fd < 0) return 0;
    char *data = malloc(cap + 1);
    if (!data) { close(fd); errno = ENOMEM; return 0; }
    size_t used = 0;
    while (used < cap) {
        ssize_t n = read(fd, data + used, cap - used);
        if (n < 0 && errno == EINTR) continue;
        if (n < 0) { free(data); close(fd); return 0; }
        if (n == 0) break;
        used += (size_t)n;
    }
    close(fd);
    if (used == cap) { free(data); errno = EOVERFLOW; return 0; }
    data[used] = 0; *contents = data; *length = used; return 1;
}

static int rt_lg_parse_mountinfo(const char *data, size_t length,
        char *mount_root, size_t root_cap, char *mount_point, size_t point_cap) {
    size_t offset = 0; int mounts = 0, lines = 0;
    char root[4096] = "", point[4096] = "";
    while (offset < length) {
        const char *newline = memchr(data + offset, '\n', length - offset);
        if (!newline || ++lines > 4096) { errno = EPROTO; return 0; }
        size_t line_len = (size_t)(newline - (data + offset));
        if (!line_len || line_len >= 16384 || memchr(data + offset, '\\', line_len) ||
            memchr(data + offset, 0, line_len) || memchr(data + offset, '\r', line_len)) {
            errno = ENOTSUP; return 0;
        }
        char line[16384]; memcpy(line, data + offset, line_len); line[line_len] = 0;
        offset += line_len + 1;
        char *save = NULL, *token = strtok_r(line, " \t", &save);
        char *fields[6] = {0};
        for (int i = 0; token && i < 6; i++, token = strtok_r(NULL, " \t", &save)) fields[i] = token;
        if (!fields[0] || !fields[1] || !fields[2] || !fields[3] || !fields[4] || !fields[5]) {
            errno = EPROTO; return 0;
        }
        for (int field = 0; field < 2; field++) {
            if (!*fields[field]) { errno = EPROTO; return 0; }
            for (const char *digit = fields[field]; *digit; digit++)
                if (!isdigit((unsigned char)*digit)) { errno = EPROTO; return 0; }
        }
        const char *device_colon = strchr(fields[2], ':');
        if (!device_colon || device_colon == fields[2] || !device_colon[1] ||
            strchr(device_colon + 1, ':')) { errno = EPROTO; return 0; }
        for (const char *digit = fields[2]; *digit; digit++)
            if (digit != device_colon && !isdigit((unsigned char)*digit)) {
                errno = EPROTO; return 0;
            }
        int separator = 0, cgroup2 = 0;
        while (token) {
            if (strcmp(token, "-") == 0) {
                char *fstype = strtok_r(NULL, " \t", &save);
                char *source = strtok_r(NULL, " \t", &save);
                char *super_options = strtok_r(NULL, " \t", &save);
                if (!fstype || !source || !super_options) { errno = EPROTO; return 0; }
                separator = 1; cgroup2 = strcmp(fstype, "cgroup2") == 0; break;
            }
            token = strtok_r(NULL, " \t", &save);
        }
        if (!separator) { errno = EPROTO; return 0; }
        if (cgroup2) {
            if (++mounts > 1 || strlen(fields[3]) >= sizeof(root) ||
                strlen(fields[4]) >= sizeof(point) || !rt_lg_canonical_path(fields[3]) ||
                !rt_lg_canonical_path(fields[4])) { errno = ENOTSUP; return 0; }
            strcpy(root, fields[3]); strcpy(point, fields[4]);
        }
    }
    if (mounts != 1 || strlen(root) >= root_cap || strlen(point) >= point_cap) {
        errno = ENOTSUP; return 0;
    }
    strcpy(mount_root, root); strcpy(mount_point, point); return 1;
}

static int rt_lg_parse_membership(const char *data, size_t length,
        char *membership, size_t cap) {
    size_t offset = 0; int found = 0, lines = 0;
    while (offset < length) {
        const char *newline = memchr(data + offset, '\n', length - offset);
        if (!newline || ++lines > 4096) { errno = EPROTO; return 0; }
        size_t line_len = (size_t)(newline - (data + offset));
        const char *line = data + offset; offset += line_len + 1;
        const char *first = memchr(line, ':', line_len);
        const char *second = first ? memchr(first + 1, ':', line_len - (size_t)(first + 1 - line)) : NULL;
        if (!line_len || memchr(line, '\\', line_len) || memchr(line, 0, line_len) ||
            memchr(line, '\r', line_len) || !first || !second || first == line ||
            second + 1 >= line + line_len) {
            errno = EPROTO; return 0;
        }
        for (const char *digit = line; digit < first; digit++)
            if (!isdigit((unsigned char)*digit)) { errno = EPROTO; return 0; }
        size_t path_len = (size_t)(line + line_len - (second + 1));
        if (path_len >= 4096) { errno = EOVERFLOW; return 0; }
        char record_path[4096]; memcpy(record_path, second + 1, path_len); record_path[path_len] = 0;
        if (!rt_lg_canonical_path(record_path)) { errno = EPROTO; return 0; }
        if (line[0] == '0') {
            if ((size_t)(first - line) != 1 || second != first + 1 || found) {
                errno = ENOTSUP; return 0;
            }
            size_t n = path_len;
            if (!n || n >= cap) { errno = EOVERFLOW; return 0; }
            memcpy(membership, second + 1, n); membership[n] = 0; found = 1;
        }
    }
    if (!found) { errno = ENOENT; return 0; }
    return 1;
}

/* Resolve the one unambiguous cgroup2 mount visible to this process and map
 * its unified membership back into that mount. Escaped/ambiguous mountinfo is
 * rejected rather than guessed. */
static int rt_lg_current_mapping(char *mount_path, size_t mount_cap,
        char *membership_path, size_t membership_cap) {
    char *mountinfo = NULL, *cgroups = NULL; size_t mountinfo_len = 0, cgroups_len = 0;
    char mount_root[4096], mount_point[4096], membership[4096];
    int ok = rt_lg_read_proc_file("/proc/self/mountinfo", &mountinfo, &mountinfo_len) &&
        rt_lg_read_proc_file("/proc/self/cgroup", &cgroups, &cgroups_len) &&
        rt_lg_parse_mountinfo(mountinfo, mountinfo_len, mount_root, sizeof(mount_root),
            mount_point, sizeof(mount_point)) &&
        rt_lg_parse_membership(cgroups, cgroups_len, membership, sizeof(membership));
    free(mountinfo); free(cgroups);
    if (!ok ||
        !rt_lg_canonical_path(mount_root) || !rt_lg_canonical_path(mount_point) ||
        !rt_lg_canonical_path(membership)) return 0;
    size_t root_len = strlen(mount_root);
    if (strncmp(membership, mount_root, root_len) != 0 ||
        (root_len > 1 && membership[root_len] != 0 && membership[root_len] != '/')) {
        errno = ENOTSUP; return 0;
    }
    const char *suffix = membership + root_len;
    if (root_len == 1 && mount_root[0] == '/') suffix = membership + 1;
    if (*suffix == '/') suffix++;
    int n;
    if (strcmp(mount_point, "/") == 0)
        n = snprintf(membership_path, membership_cap, "/%s", suffix);
    else if (*suffix)
        n = snprintf(membership_path, membership_cap, "%s/%s", mount_point, suffix);
    else n = snprintf(membership_path, membership_cap, "%s", mount_point);
    if (n < 0 || (size_t)n >= membership_cap || strlen(mount_point) >= mount_cap) {
        errno = EOVERFLOW; return 0;
    }
    strcpy(mount_path, mount_point);
    return 1;
}

static int rt_lg_is_current_or_parent(int candidate, const char *candidate_path,
        int current, const char *current_path) {
    struct stat a, b, named;
    if (fstat(candidate, &a) || fstat(current, &b)) return 0;
    if (a.st_dev == b.st_dev && a.st_ino == b.st_ino &&
        strcmp(candidate_path, current_path) == 0) return 1;
    size_t n = strlen(candidate_path);
    if (strncmp(current_path, candidate_path, n) != 0 ||
        (n > 1 && current_path[n] != '/') || !current_path[n]) return 0;
    const char *child_name = current_path + n + (n == 1 ? 0 : 1);
    if (!*child_name || strchr(child_name, '/')) return 0;
    int child = openat(candidate, child_name,
        O_RDONLY | O_DIRECTORY | O_CLOEXEC | O_NOFOLLOW);
    if (child < 0) return 0;
    int ok = fstat(child, &named) == 0 && named.st_dev == b.st_dev && named.st_ino == b.st_ino;
    close(child);
    return ok;
}

static int rt_lg_hex_digest(const char *data, uint64_t len, char out[65]) {
    if (!rt_lg_copy_text(data, len, out, 65) || len != 64) return 0;
    for (size_t i = 0; i < 64; i++)
        if (!((out[i] >= '0' && out[i] <= '9') ||
              (out[i] >= 'a' && out[i] <= 'f'))) return 0;
    return 1;
}

static int rt_lg_digest_fd(int fd, const char expected[65]) {
    struct stat before, after;
    if (fd < 0 || fstat(fd, &before) || !S_ISREG(before.st_mode) ||
        before.st_size < 0 || before.st_size > (off_t)1073741824) return 0;
    size_t size = (size_t)before.st_size;
    void *data = size ? mmap(NULL, size, PROT_READ, MAP_PRIVATE, fd, 0) : NULL;
    if (size && data == MAP_FAILED) return 0;
    uint8_t digest[32]; owned_sha256(size ? (const uint8_t*)data : (const uint8_t*)"", size, digest);
    if (size) munmap(data, size);
    if (fstat(fd, &after) || before.st_dev != after.st_dev ||
        before.st_ino != after.st_ino || before.st_size != after.st_size ||
        before.st_mtim.tv_sec != after.st_mtim.tv_sec ||
        before.st_mtim.tv_nsec != after.st_mtim.tv_nsec ||
        before.st_ctim.tv_sec != after.st_ctim.tv_sec ||
        before.st_ctim.tv_nsec != after.st_ctim.tv_nsec) return 0;
    static const char digits[] = "0123456789abcdef";
    for (size_t i = 0; i < 32; i++)
        if (expected[i * 2] != digits[digest[i] >> 4] ||
            expected[i * 2 + 1] != digits[digest[i] & 15]) return 0;
    return 1;
}

/* Copy once to a sealed anonymous executable, then hash and execute those
 * exact bytes. A writer changing the original inode after admission cannot
 * change either the broker or compiler worker image. */
static int rt_lg_pin_image(const char *path, const char expected[65]) {
#if !defined(SYS_memfd_create)
    (void)path; (void)expected; errno = ENOTSUP; return -1;
#else
    int source = open(path, O_RDONLY | O_CLOEXEC | O_NOFOLLOW);
    if (source < 0) return -1;
    struct stat before, after;
    if (fstat(source, &before) != 0 || !S_ISREG(before.st_mode) ||
        before.st_size <= 0 || before.st_size > (off_t)536870912) {
        close(source); errno = EFBIG; return -1;
    }
    int sealed = (int)syscall(SYS_memfd_create, "simple-native-image",
        MFD_CLOEXEC | MFD_ALLOW_SEALING);
    if (sealed < 0) { close(source); return -1; }
    uint8_t buffer[65536]; off_t copied = 0;
    while (copied < before.st_size) {
        size_t want = (size_t)(before.st_size - copied);
        if (want > sizeof(buffer)) want = sizeof(buffer);
        ssize_t got = pread(source, buffer, want, copied);
        if (got < 0 && errno == EINTR) continue;
        if (got <= 0) goto fail;
        ssize_t offset = 0;
        while (offset < got) {
            ssize_t written = write(sealed, buffer + offset, (size_t)(got - offset));
            if (written < 0 && errno == EINTR) continue;
            if (written <= 0) goto fail;
            offset += written;
        }
        copied += got;
    }
    if (fstat(source, &after) != 0 || before.st_dev != after.st_dev ||
        before.st_ino != after.st_ino || before.st_size != after.st_size ||
        before.st_mtim.tv_sec != after.st_mtim.tv_sec ||
        before.st_mtim.tv_nsec != after.st_mtim.tv_nsec ||
        before.st_ctim.tv_sec != after.st_ctim.tv_sec ||
        before.st_ctim.tv_nsec != after.st_ctim.tv_nsec ||
        fchmod(sealed, 0500) != 0 ||
        fcntl(sealed, F_ADD_SEALS,
            F_SEAL_WRITE | F_SEAL_GROW | F_SEAL_SHRINK | F_SEAL_SEAL) != 0 ||
        lseek(sealed, 0, SEEK_SET) < 0 || !rt_lg_digest_fd(sealed, expected))
        goto fail;
    close(source); return sealed;
fail:
    close(source); close(sealed); errno = ESTALE; return -1;
#endif
}

static char **rt_lg_copy_environment(SplArray *values) {
    int64_t count = values ? rt_array_len(values) : -1;
    if (count < 0 || count > 4096) return NULL;
    char **result = calloc((size_t)count + 1, sizeof(char*));
    if (!result) return NULL;
    for (int64_t i = 0; i < count; i++) {
        int64_t item = rt_array_get(values, i);
        int64_t len = rt_string_len(item);
        const uint8_t *data = rt_string_data(item);
        if (!data || len < 3 || len > 65535 || memchr(data, 0, (size_t)len) ||
            !memchr(data, '=', (size_t)len)) goto fail;
        result[i] = malloc((size_t)len + 1);
        if (!result[i]) goto fail;
        memcpy(result[i], data, (size_t)len); result[i][len] = 0;
    }
    return result;
fail:
    for (int64_t i = 0; i < count; i++) free(result[i]);
    free(result); return NULL;
}

static void rt_lg_free_strings(char **items) {
    if (!items) return;
    for (size_t i = 0; items[i]; i++) free(items[i]);
    free(items);
}

static int rt_lg_populated(int fd, int *populated) {
    char events[256];
    if (!rt_lg_read_at(fd, "cgroup.events", events, sizeof(events))) return 0;
    if (!rt_lg_parse_populated(events, strlen(events), populated)) {
        errno = EPROTO; return 0;
    }
    return 1;
}

static int rt_lg_peak(int fd, int64_t *peak) {
    char data[128];
    return rt_lg_read_at(fd, "memory.peak", data, sizeof(data)) &&
        rt_lg_number(data, peak);
}

static int64_t rt_lg_now_ms(void) {
    struct timespec now;
    if (clock_gettime(CLOCK_MONOTONIC, &now)) return -1;
    return (int64_t)now.tv_sec * 1000 + now.tv_nsec / 1000000;
}

static int rt_lg_kill(RtLinuxGroup *owner) {
    /* Intent survives a failed write. A timeout/cancel latch is not evidence
     * that the kernel received the kill request. */
    owner->kill_pending = 1;
    if (!rt_lg_write_at(owner->group_fd, "cgroup.kill", "1")) return 0;
    owner->kill_pending = 0;
    return 1;
}

/* A controller being available is not a delegation to child groups. Do not
 * create a probe or change subtree_control under an undelegated host parent. */
static int rt_lg_memory_delegated(int parent) {
    char controllers[4096];
    if (!rt_lg_read_at(parent, "cgroup.subtree_control", controllers,
            sizeof(controllers))) return 0;
    const char *at = controllers;
    while (*at) {
        at += strspn(at, " \t\r\n");
        size_t length = strcspn(at, " \t\r\n");
        if (length == 6 && memcmp(at, "memory", 6) == 0) return 1;
        at += length;
    }
    errno = ENOTSUP; return 0;
}

static int rt_lg_delegation_fd(void) {
    struct stat status, named;
    if (!rt_lg_delegation.active) { errno = ENOENT; return -1; }
    if (fstat(rt_lg_delegation.parent_fd, &status) ||
        fstatat(rt_lg_delegation.root_fd, rt_lg_delegation.name, &named,
            AT_SYMLINK_NOFOLLOW) || !S_ISDIR(named.st_mode) ||
        status.st_dev != rt_lg_delegation.device ||
        status.st_ino != rt_lg_delegation.inode ||
        named.st_dev != status.st_dev || named.st_ino != status.st_ino) {
        errno = ESTALE; return -1;
    }
    return fcntl(rt_lg_delegation.parent_fd, F_DUPFD_CLOEXEC, 3);
}

/* Shared fresh-child transaction. root_fd is either the legacy literal
 * cgroup2 mount root or the verified explicit delegated directory. */
static SplArray *rt_lg_parent_acquire_root(int root, const char *attempt,
        const char identity[65]) {
    int64_t answer[4] = {EINVAL, 0, 0, 0};
    char name[80];
    int parent = -1, created = 0;
    struct statfs fs;
    struct stat status = {0};
    if (root < 0 || rt_lg_delegation.active || rt_linux_group.active ||
        rt_lg_next_parent_token == INT64_MAX) goto done;
    if (fstatfs(root, &fs) ||
        (unsigned long)fs.f_type != CGROUP2_SUPER_MAGIC) {
        answer[0] = ENOTSUP; goto done;
    }
    if (!rt_lg_memory_delegated(root)) { answer[0] = errno ? errno : ENOTSUP; goto done; }
    snprintf(name, sizeof(name), "simple-parent-%s", identity);
    if (mkdirat(root, name, 0700)) { answer[0] = errno; goto done; }
    created = 1;
    parent = openat(root, name, O_RDONLY | O_DIRECTORY | O_CLOEXEC | O_NOFOLLOW);
    int populated = 1;
    memset(&status, 0, sizeof(status));
    if (parent < 0 || fstat(parent, &status)) {
        answer[0] = errno ? errno : EIO; goto done;
    }
    struct stat named;
    if (fstatat(root, name, &named, AT_SYMLINK_NOFOLLOW) || !S_ISDIR(named.st_mode) ||
        named.st_dev != status.st_dev || named.st_ino != status.st_ino) {
        answer[0] = ESTALE; goto done;
    }
    if (!rt_lg_populated(parent, &populated) || populated ||
        !rt_lg_write_at(parent, "cgroup.subtree_control", "+memory") ||
        !rt_lg_memory_delegated(parent)) {
        answer[0] = errno ? errno : ENOTSUP; goto done;
    }
    rt_lg_delegation.active = 1;
    rt_lg_delegation.token = ++rt_lg_next_parent_token;
    rt_lg_delegation.root_fd = root; rt_lg_delegation.parent_fd = parent;
    rt_lg_delegation.device = status.st_dev; rt_lg_delegation.inode = status.st_ino;
    strcpy(rt_lg_delegation.name, name); strcpy(rt_lg_delegation.identity, identity);
    strcpy(rt_lg_delegation.attempt, attempt);
    answer[0] = 0; answer[1] = rt_lg_delegation.token;
    answer[2] = (int64_t)status.st_dev; answer[3] = (int64_t)status.st_ino;
    return owned_adapter_values(answer, 4);
done:
    /* A positive token with a nonzero status is retained ownership, NOT proof
     * of no allocation. Never discard an unremoved parent after rollback. */
    if (created) {
        struct stat named;
        int same = parent >= 0 && fstat(parent, &status) == 0 &&
            fstatat(root, name, &named, AT_SYMLINK_NOFOLLOW) == 0 &&
            S_ISDIR(named.st_mode) && named.st_dev == status.st_dev && named.st_ino == status.st_ino;
        if (!same) {
            /* mkdir succeeded but no pinned inode can be proven. Do not
             * unlink a possibly substituted sibling or mint a fake token. */
            answer[0] = EOWNERDEAD; answer[1] = -1;
            if (parent >= 0) close(parent);
            if (root >= 0) close(root);
            return owned_adapter_values(answer, 4);
        }
        if (unlinkat(root, name, AT_REMOVEDIR)) {
            answer[0] = errno ? errno : EIO;
        rt_lg_delegation.active = 1;
        rt_lg_delegation.token = ++rt_lg_next_parent_token;
        rt_lg_delegation.root_fd = root; rt_lg_delegation.parent_fd = parent;
        rt_lg_delegation.device = status.st_dev; rt_lg_delegation.inode = status.st_ino;
        strcpy(rt_lg_delegation.name, name); strcpy(rt_lg_delegation.identity, identity);
        strcpy(rt_lg_delegation.attempt, attempt);
        answer[1] = rt_lg_delegation.token;
        answer[2] = (int64_t)status.st_dev; answer[3] = (int64_t)status.st_ino;
        return owned_adapter_values(answer, 4);
        }
    }
    if (parent >= 0) close(parent);
    if (root >= 0) close(root);
    return owned_adapter_values(answer, 4);
}

/* Receipt: status, token, device, inode. V1 deliberately retains its original
 * literal mount-root policy; V2 supplies an already verified delegated fd. */
SplArray *rt_linux_group_parent_acquire_v1(const char *attempt_data, uint64_t attempt_len,
        const char *identity_data, uint64_t identity_len) {
    char attempt[4096], identity[65];
    if (rt_lg_delegation.active || rt_linux_group.active ||
        !rt_lg_copy_text(attempt_data, attempt_len, attempt, sizeof(attempt)) ||
        attempt[0] != '/' || !rt_lg_hex_digest(identity_data, identity_len, identity)) {
        const int64_t error[4] = {EINVAL, 0, 0, 0}; return owned_adapter_values(error, 4);
    }
    int root = open("/", O_RDONLY | O_DIRECTORY | O_CLOEXEC | O_NOFOLLOW);
    const char *components[] = {"sys", "fs", "cgroup"};
    for (size_t i = 0; root >= 0 && i < 3; i++) {
        int next = openat(root, components[i], O_RDONLY | O_DIRECTORY | O_CLOEXEC | O_NOFOLLOW);
        int saved = errno; close(root); root = next; errno = saved;
    }
    return rt_lg_parent_acquire_root(root, attempt, identity);
}

/* V2 proves an explicit current/immediate-parent mapping before any child
 * mkdir. The parent's existing controller set is observed only, never changed. */
SplArray *rt_linux_group_parent_acquire_at_v2(const char *path_data, uint64_t path_len,
        const char *attempt_data, uint64_t attempt_len,
        const char *identity_data, uint64_t identity_len) {
    int64_t failure[4] = {EINVAL, 0, 0, 0};
    char path[4096], attempt[4096], identity[65], mount_path[4096], current_path[4096];
    int root = -1, current = -1;
    struct statfs fs;
    if (rt_lg_delegation.active || rt_linux_group.active ||
        !rt_lg_copy_text(path_data, path_len, path, sizeof(path)) ||
        !rt_lg_copy_text(attempt_data, attempt_len, attempt, sizeof(attempt)) ||
        !rt_lg_hex_digest(identity_data, identity_len, identity) ||
        !rt_lg_canonical_path(path) || !rt_lg_canonical_path(attempt)) goto reject;
    if (!rt_lg_current_mapping(mount_path, sizeof(mount_path), current_path, sizeof(current_path))) {
        failure[0] = errno ? errno : ENOTSUP; goto reject;
    }
    root = rt_lg_open_absolute_dir(path);
    current = rt_lg_open_absolute_dir(current_path);
    int mount = rt_lg_open_absolute_dir(mount_path);
    if (root < 0 || current < 0 || mount < 0 || fstatfs(root, &fs) ||
        (unsigned long)fs.f_type != CGROUP2_SUPER_MAGIC || fstatfs(current, &fs) ||
        (unsigned long)fs.f_type != CGROUP2_SUPER_MAGIC ||
        !rt_lg_is_current_or_parent(root, path, current, current_path)) {
        failure[0] = errno ? errno : EACCES;
        if (mount >= 0) close(mount);
        goto reject;
    }
    struct stat root_stat, current_stat, mount_stat;
    if (fstat(root, &root_stat) || fstat(current, &current_stat) || fstat(mount, &mount_stat)) {
        failure[0] = errno ? errno : EIO; close(mount); goto reject;
    }
    close(mount);
    if (root_stat.st_dev != mount_stat.st_dev || current_stat.st_dev != mount_stat.st_dev) {
        failure[0] = EXDEV; goto reject;
    }
    if (root_stat.st_dev == mount_stat.st_dev && root_stat.st_ino == mount_stat.st_ino) {
        failure[0] = EACCES; goto reject;
    }
    if (!rt_lg_memory_delegated(root)) { failure[0] = errno ? errno : ENOTSUP; goto reject; }
    /* Re-read membership and prove the named delegated path still resolves to
     * the pinned inode immediately before starting the fresh-child transaction. */
    char mount_path_again[4096], current_path_again[4096];
    int named_root = -1, named_current = -1, named_mount = -1;
    if (!rt_lg_current_mapping(mount_path_again, sizeof(mount_path_again),
            current_path_again, sizeof(current_path_again)) ||
        strcmp(mount_path_again, mount_path) != 0 || strcmp(current_path_again, current_path) != 0 ||
        (named_root = rt_lg_open_absolute_dir(path)) < 0 ||
        (named_current = rt_lg_open_absolute_dir(current_path_again)) < 0 ||
        (named_mount = rt_lg_open_absolute_dir(mount_path_again)) < 0) {
        failure[0] = errno ? errno : ESTALE;
        if (named_root >= 0) close(named_root);
        if (named_current >= 0) close(named_current);
        if (named_mount >= 0) close(named_mount);
        goto reject;
    }
    struct stat pinned, named_status, named_current_status, named_mount_status;
    struct statfs named_mount_fs;
    int revalidated = fstat(root, &pinned) == 0 && fstat(named_root, &named_status) == 0 &&
        pinned.st_dev == named_status.st_dev && pinned.st_ino == named_status.st_ino &&
        fstat(named_current, &named_current_status) == 0 &&
        named_current_status.st_dev == mount_stat.st_dev &&
        fstat(named_mount, &named_mount_status) == 0 &&
        named_mount_status.st_dev == mount_stat.st_dev && named_mount_status.st_ino == mount_stat.st_ino &&
        fstatfs(named_mount, &named_mount_fs) == 0 &&
        (unsigned long)named_mount_fs.f_type == CGROUP2_SUPER_MAGIC &&
        rt_lg_is_current_or_parent(named_root, path, named_current, current_path_again);
    close(named_root); close(named_current); close(named_mount);
    if (!revalidated) { failure[0] = ESTALE; goto reject; }
    if (current >= 0) close(current);
    return rt_lg_parent_acquire_root(root, attempt, identity);
reject:
    if (current >= 0) close(current);
    if (root >= 0) close(root);
    return owned_adapter_values(failure, 4);
}

int64_t rt_linux_group_parent_release_v1(int64_t token) {
    if (!rt_lg_delegation.active || token != rt_lg_delegation.token) return EINVAL;
    if (rt_linux_group.active && !rt_linux_group.collected) return EBUSY;
    int pinned = rt_lg_delegation_fd();
    if (pinned < 0) return errno;
    close(pinned);
    if (unlinkat(rt_lg_delegation.root_fd, rt_lg_delegation.name, AT_REMOVEDIR)) return errno;
    close(rt_lg_delegation.parent_fd); close(rt_lg_delegation.root_fd);
    rt_lg_delegation.active = 0;
    return 0;
}

static int rt_lg_capacity_capability(int parent) {
#if !defined(SYS_pidfd_open) || !defined(SYS_clone3) || !defined(SYS_execveat)
    (void)parent; errno = ENOTSUP; return 0;
#else
    if (!rt_lg_memory_delegated(parent)) return 0;
    int pidfd = (int)syscall(SYS_pidfd_open, getpid(), 0);
    if (pidfd < 0) return 0;
    close(pidfd);
    struct timespec now;
    if (clock_gettime(CLOCK_MONOTONIC, &now) != 0) return 0;
    char name[80], value[128];
    snprintf(name, sizeof(name), "simple-native-cap-%ld-%ld-%ld",
        (long)getpid(), (long)now.tv_sec, (long)now.tv_nsec);
    if (mkdirat(parent, name, 0700) != 0) return 0;
    int group = openat(parent, name, O_RDONLY | O_DIRECTORY | O_CLOEXEC | O_NOFOLLOW);
    int kill_fd = group >= 0 ? openat(group, "cgroup.kill", O_WRONLY | O_CLOEXEC | O_NOFOLLOW) : -1;
    int valid = group >= 0 && kill_fd >= 0 &&
        rt_lg_read_at(group, "memory.max", value, sizeof(value)) &&
        rt_lg_read_at(group, "memory.peak", value, sizeof(value)) &&
        rt_lg_read_at(group, "cgroup.events", value, sizeof(value));
    int saved = errno;
    if (kill_fd >= 0) close(kill_fd);
    if (group >= 0) close(group);
    if (unlinkat(parent, name, AT_REMOVEDIR) != 0) valid = 0;
    if (!valid) errno = saved ? saved : ENOTSUP;
    return valid;
#endif
}

static int rt_lg_poll(RtLinuxGroup *owner) {
    if (!owner->active || owner->collected) return EINVAL;
    int64_t now = rt_lg_now_ms();
    if (now < 0) return EIO;
    if (owner->timeout_ms > 0 && !owner->timed_out && !owner->leader_reaped &&
        now - owner->started_ms >= owner->timeout_ms) {
        owner->timed_out = 1;
        owner->kill_pending = 1;
    }
    if (owner->kill_pending && !rt_lg_kill(owner)) return errno ? errno : EIO;
    if (!owner->leader_reaped) {
        int status = 0;
        pid_t observed = waitpid(owner->pid, &status, WNOHANG);
        if (observed < 0) return errno ? errno : ECHILD;
        if (observed == owner->pid) {
            owner->leader_reaped = 1;
            owner->exit_code = WIFEXITED(status) ? WEXITSTATUS(status) :
                (WIFSIGNALED(status) ? 128 + WTERMSIG(status) : 255);
        }
    }
    int populated = 1;
    char current_text[128];
    if (!rt_lg_populated(owner->group_fd, &populated)) return EIO;
    /* Retire remaining descendants even when resource telemetry fails.
     * Telemetry errors still retain ownership and block collection. */
    if (owner->leader_reaped && populated) {
        if (!rt_lg_kill(owner)) return errno ? errno : EIO;
    }
    if (!rt_lg_read_at(owner->group_fd, "memory.current", current_text,
            sizeof(current_text)) ||
        !rt_lg_number(current_text, &owner->current) ||
        !rt_lg_peak(owner->group_fd, &owner->peak)) return EIO;
    owner->tree_empty = owner->leader_reaped && !populated;
    return 0;
}

static SplArray *rt_lg_observation(int error) {
    RtLinuxGroup *o = &rt_linux_group;
    const int64_t values[] = {error, o->leader_reaped && o->tree_empty,
        o->leader_reaped, o->tree_empty, o->tree_empty ? 0 : 1,
        o->exit_code, o->timed_out, o->cancelled, o->peak,
        o->leader_reaped && o->tree_empty ? 0 : o->current};
    return owned_adapter_values(values, 10);
}

/* Double-fork leaves the broker independent of manager death. The exact
 * executable inode is opened, hashed, and execveat'd through the same fd. */
SplArray *rt_linux_group_launch_broker_v1(const char *program_data, uint64_t program_len, const char *digest_data, uint64_t digest_len, SplArray *args) {
    int64_t answer[2] = {0, EINVAL};
    char program[4096], expected[65];
    int64_t argc = 0; int copy_error = 0;
    char **argv = NULL;
    int image = -1, pipefd[2] = {-1, -1};
    if (!rt_lg_copy_text(program_data, program_len, program, sizeof(program)) ||
        !rt_lg_hex_digest(digest_data, digest_len, expected) ||
        program[0] != '/') goto done;
    argv = owned_adapter_copy_argv(program_data, program_len, args, &argc, &copy_error);
    if (!argv) { answer[1] = copy_error ? copy_error : EINVAL; goto done; }
    image = rt_lg_pin_image(program, expected);
    if (image < 0) {
        answer[1] = errno ? errno : ESTALE; goto done;
    }
#if defined(SYS_execveat) && defined(SYS_close_range)
    if (pipe(pipefd) != 0 || fcntl(pipefd[0], F_SETFD, FD_CLOEXEC) < 0 ||
        fcntl(pipefd[1], F_SETFD, FD_CLOEXEC) < 0) {
        answer[1] = errno ? errno : EIO; goto done;
    }
    pid_t intermediate = fork();
    if (intermediate == 0) {
        close(pipefd[0]);
        pid_t broker = fork();
        if (broker == 0) {
            close(pipefd[1]);
            if (setsid() < 0) _exit(126);
            int null_fd = open("/dev/null", O_RDWR | O_CLOEXEC);
            if (null_fd < 0 || dup2(null_fd, 0) < 0 || dup2(null_fd, 1) < 0 ||
                dup2(null_fd, 2) < 0 || image < 3) _exit(126);
            if (image != 3 && dup2(image, 3) < 0) _exit(126);
            if (fcntl(3, F_SETFD, FD_CLOEXEC) < 0 ||
                syscall(SYS_close_range, 4U, ~0U, 0U) != 0) _exit(126);
            syscall(SYS_execveat, 3, "", argv, environ, AT_EMPTY_PATH);
            _exit(127);
        }
        if (broker <= 0 || write(pipefd[1], &broker, sizeof(broker)) != sizeof(broker))
            _exit(125);
        _exit(0);
    }
    if (intermediate < 0) { answer[1] = errno; goto done; }
    close(pipefd[1]); pipefd[1] = -1;
    pid_t broker = 0;
    ssize_t bytes = read(pipefd[0], &broker, sizeof(broker));
    int status = 0;
    pid_t reaped = waitpid(intermediate, &status, 0);
    if (bytes != sizeof(broker) || broker <= 0 || reaped != intermediate ||
        !WIFEXITED(status) || WEXITSTATUS(status) != 0) {
        answer[1] = ECHILD; goto done;
    }
    answer[0] = broker; answer[1] = 0;
#else
    answer[1] = ENOTSUP;
#endif
done:
    if (pipefd[0] >= 0) close(pipefd[0]);
    if (pipefd[1] >= 0) close(pipefd[1]);
    if (image >= 0) close(image);
    owned_adapter_free_argv(argv, argc);
    return owned_adapter_values(answer, 2);
}

SplArray *rt_linux_group_start_v1(const char *program_data, uint64_t program_len, const char *digest_data, uint64_t digest_len, SplArray *args, SplArray *environment, const char *directory_data, uint64_t directory_len, const char *root_data, uint64_t root_len, const char *identity_data, uint64_t identity_len, int64_t memory_limit, int64_t timeout_ms, const char *stdout_data, uint64_t stdout_len, const char *stderr_data, uint64_t stderr_len) {
    int64_t answer[2] = {0, EINVAL};
    char program[4096], directory[4096], root[4096], stdout_path[4096], stderr_path[4096];
    char expected[65], identity[65], memory_text[64], verify[128];
    int64_t readback = 0, started_ms = -1;
    char **argv = NULL, **envp = NULL;
    int64_t argc = 0; int copy_error = 0;
    int parent_fd = -1, group_fd = -1, exec_fd = -1, cwd_fd = -1, out_fd = -1, err_fd = -1;
    int created = 0, pidfd = -1;
    pid_t pid = -1;
    if (rt_linux_group.active || memory_limit < 0 || memory_limit > 1125899906842624LL ||
        timeout_ms < 0 || timeout_ms > 604800000 ||
        !rt_lg_copy_text(program_data, program_len, program, sizeof(program)) ||
        !rt_lg_copy_text(directory_data, directory_len, directory, sizeof(directory)) ||
        !rt_lg_copy_text(root_data, root_len, root, sizeof(root)) ||
        !rt_lg_copy_text(stdout_data, stdout_len, stdout_path, sizeof(stdout_path)) ||
        !rt_lg_copy_text(stderr_data, stderr_len, stderr_path, sizeof(stderr_path)) ||
        !rt_lg_hex_digest(digest_data, digest_len, expected) ||
        !rt_lg_hex_digest(identity_data, identity_len, identity) ||
        program[0] != '/' || directory[0] != '/' || root[0] != '/' ||
        stdout_path[0] != '/' || stderr_path[0] != '/') goto done;
    argv = owned_adapter_copy_argv(program_data, program_len, args, &argc, &copy_error);
    envp = rt_lg_copy_environment(environment);
    if (!argv || !envp) { answer[1] = copy_error ? copy_error : ENOMEM; goto done; }
    exec_fd = rt_lg_pin_image(program, expected);
    cwd_fd = open(directory, O_RDONLY | O_DIRECTORY | O_CLOEXEC | O_NOFOLLOW);
    if (exec_fd < 0 || cwd_fd < 0) {
        answer[1] = errno ? errno : ESTALE; goto done;
    }
    if (rt_lg_delegation.active &&
        (strcmp(root, rt_lg_delegation.attempt) ||
         strcmp(identity, rt_lg_delegation.identity))) { answer[1] = ESTALE; goto done; }
    parent_fd = rt_lg_delegation.active ? rt_lg_delegation_fd() : rt_lg_parent();
    if (parent_fd < 0) { answer[1] = errno ? errno : ENOTSUP; goto done; }
    if (!rt_lg_memory_delegated(parent_fd)) {
        answer[1] = errno ? errno : ENOTSUP; goto done;
    }
    char name[80]; snprintf(name, sizeof(name), "simple-native-%s", identity);
    if (mkdirat(parent_fd, name, 0700) != 0) { answer[1] = errno; goto done; }
    created = 1;
    group_fd = openat(parent_fd, name, O_RDONLY | O_DIRECTORY | O_CLOEXEC | O_NOFOLLOW);
    if (group_fd < 0) { answer[1] = errno; goto done; }
    if (memory_limit == 0) snprintf(memory_text, sizeof(memory_text), "max");
    else snprintf(memory_text, sizeof(memory_text), "%lld", (long long)memory_limit);
    if (!rt_lg_write_at(group_fd, "memory.max", memory_text) ||
        !rt_lg_read_at(group_fd, "memory.max", verify, sizeof(verify)) ||
        (memory_limit == 0 ? (strcmp(verify, "max") != 0 && strcmp(verify, "max\n") != 0) :
            (!rt_lg_number(verify, &readback) || readback != memory_limit)) ||
        !rt_lg_write_at(group_fd, "memory.swap.max", memory_limit == 0 ? "max" : "0") ||
        !rt_lg_read_at(group_fd, "memory.swap.max", verify, sizeof(verify)) ||
        (memory_limit == 0 ? (strcmp(verify, "max") != 0 && strcmp(verify, "max\n") != 0) :
            (!rt_lg_number(verify, &readback) || readback != 0)) ||
        !rt_lg_write_at(group_fd, "memory.oom.group", "1") ||
        !rt_lg_read_at(group_fd, "memory.oom.group", verify, sizeof(verify)) ||
        !rt_lg_number(verify, &readback) || readback != 1 ||
        !rt_lg_read_at(group_fd, "memory.peak", verify, sizeof(verify))) {
        answer[1] = errno ? errno : ENOTSUP; goto done;
    }
    out_fd = open(stdout_path, O_WRONLY | O_CREAT | O_EXCL | O_CLOEXEC | O_NOFOLLOW, 0600);
    err_fd = open(stderr_path, O_WRONLY | O_CREAT | O_EXCL | O_CLOEXEC | O_NOFOLLOW, 0600);
    if (out_fd < 0 || err_fd < 0) { answer[1] = errno; goto done; }
    /* Finish fallible admission before clone: a clock failure must never
     * launch a child and then discard its cleanup authority. */
    started_ms = rt_lg_now_ms();
    if (started_ms < 0) { answer[1] = EIO; goto done; }
#if defined(SYS_clone3) && defined(SYS_execveat) && defined(SYS_close_range)
    struct clone_args clone = {0};
    clone.flags = CLONE_PIDFD | CLONE_INTO_CGROUP;
    clone.pidfd = (uint64_t)(uintptr_t)&pidfd;
    clone.cgroup = (uint64_t)group_fd;
    clone.exit_signal = SIGCHLD;
    pid = (pid_t)syscall(SYS_clone3, &clone, sizeof(clone));
    if (pid == 0) {
        int input_fd = open("/dev/null", O_RDONLY | O_CLOEXEC);
        if (input_fd < 0 || dup2(input_fd, STDIN_FILENO) < 0) _exit(126);
        if (fchdir(cwd_fd) || dup2(out_fd, STDOUT_FILENO) < 0 ||
            dup2(err_fd, STDERR_FILENO) < 0 || exec_fd < 3) _exit(126);
        if (exec_fd != 3 && dup2(exec_fd, 3) < 0) _exit(126);
        if (fcntl(3, F_SETFD, FD_CLOEXEC) < 0) _exit(126);
        if (syscall(SYS_close_range, 4U, ~0U, 0U) != 0) _exit(126);
        syscall(SYS_execveat, 3, "", argv, envp, AT_EMPTY_PATH);
        _exit(127);
    }
#else
    answer[1] = ENOTSUP; goto done;
#endif
    if (pid < 0) { answer[1] = errno ? errno : ENOTSUP; goto done; }
    /* CLONE_PIDFD stores the allocated descriptor before clone3 returns
     * success (clone(2)). No fallible work belongs between this successful
     * spawn and returning the lease. Cancellation/collection failures keep
     * these handles owned, instead of entering a blocking best-effort reap. */
    rt_linux_group = (RtLinuxGroup){.active=1, .parent_fd=parent_fd,
        .group_fd=group_fd, .pidfd=pidfd, .pid=pid,
        .started_ms=started_ms, .timeout_ms=timeout_ms};
    memcpy(rt_linux_group.name, name, strlen(name) + 1);
    answer[0] = 1; answer[1] = 0;
    parent_fd = group_fd = pidfd = -1; created = 0;
done:
    if (out_fd >= 0) close(out_fd);
    if (err_fd >= 0) close(err_fd);
    if (exec_fd >= 0) close(exec_fd);
    if (cwd_fd >= 0) close(cwd_fd);
    if (group_fd >= 0) close(group_fd);
    if (created && parent_fd >= 0) (void)unlinkat(parent_fd, name, AT_REMOVEDIR);
    if (parent_fd >= 0) close(parent_fd);
    owned_adapter_free_argv(argv, argc);
    rt_lg_free_strings(envp);
    return owned_adapter_values(answer, 2);
}

SplArray *rt_linux_group_poll_v1(int64_t token) {
    if (token != 1 || !rt_linux_group.active) return rt_lg_observation(EINVAL);
    return rt_lg_observation(rt_lg_poll(&rt_linux_group));
}

int64_t rt_linux_group_cancel_v1(int64_t token) {
    if (token != 1 || !rt_linux_group.active || rt_linux_group.collected) return EINVAL;
    rt_linux_group.cancelled = 1;
    return rt_lg_kill(&rt_linux_group) ? 0 : (errno ? errno : EIO);
}

SplArray *rt_linux_group_collect_v1(int64_t token) {
    if (token != 1 || !rt_linux_group.active || rt_linux_group.collected)
        return rt_lg_observation(EINVAL);
    int error = rt_lg_poll(&rt_linux_group);
    if (error) return rt_lg_observation(error);
    if (!rt_linux_group.leader_reaped || !rt_linux_group.tree_empty)
        return rt_lg_observation(EBUSY);
    if (unlinkat(rt_linux_group.parent_fd, rt_linux_group.name, AT_REMOVEDIR) != 0)
        return rt_lg_observation(errno ? errno : EIO);
    close(rt_linux_group.pidfd);
    close(rt_linux_group.group_fd);
    close(rt_linux_group.parent_fd);
    rt_linux_group.collected = 1;
    return rt_lg_observation(0);
}

SplArray *rt_linux_group_available_capacity_v1(const char *path_data, uint64_t path_len) {
    int64_t result[3] = {EINVAL, 0, 0};
    char path[4096], line[256];
    if (!rt_lg_copy_text(path_data, path_len, path, sizeof(path)) || path[0] != '/')
        return owned_adapter_values(result, 3);
    FILE *file = fopen("/proc/meminfo", "re");
    if (!file) { result[0] = errno; return owned_adapter_values(result, 3); }
    int64_t available = 0;
    while (fgets(line, sizeof(line), file)) {
        if (strncmp(line, "MemAvailable:", 13) == 0) {
            long long kb = 0;
            if (sscanf(line, "MemAvailable: %lld kB", &kb) == 1 &&
                kb > 0 && kb <= INT64_MAX / 1024) available = (int64_t)kb * 1024;
            break;
        }
    }
    fclose(file);
    int parent = rt_lg_delegation.active ? rt_lg_delegation_fd() : rt_lg_parent();
    if (parent < 0 || available <= 0) {
        if (parent >= 0) close(parent);
        result[0] = ENOTSUP; return owned_adapter_values(result, 3);
    }
    if (!rt_lg_capacity_capability(parent)) {
        result[0] = errno ? errno : ENOTSUP;
        close(parent); return owned_adapter_values(result, 3);
    }
    char maximum[128], current[128]; int64_t max_bytes = 0, used = 0;
    if (!rt_lg_read_at(parent, "memory.max", maximum, sizeof(maximum)) ||
        !rt_lg_read_at(parent, "memory.current", current, sizeof(current)) ||
        !rt_lg_number(current, &used)) {
        close(parent); result[0] = ENOTSUP; return owned_adapter_values(result, 3);
    }
    close(parent);
    if (strcmp(maximum, "max\n") != 0 && strcmp(maximum, "max") != 0) {
        if (!rt_lg_number(maximum, &max_bytes)) {
            result[0] = EPROTO; return owned_adapter_values(result, 3);
        }
        int64_t headroom = max_bytes > used ? max_bytes - used : 0;
        if (headroom < available) available = headroom;
    }
    struct statvfs volume;
    if (available <= 0 || statvfs(path, &volume) != 0 ||
        volume.f_frsize == 0 || volume.f_bavail > INT64_MAX / volume.f_frsize) {
        result[0] = errno ? errno : ENOSPC; return owned_adapter_values(result, 3);
    }
    result[0] = 0; result[1] = available;
    result[2] = (int64_t)(volume.f_bavail * volume.f_frsize);
    return owned_adapter_values(result, 3);
}
