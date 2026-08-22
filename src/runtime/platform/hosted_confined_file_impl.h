#ifndef SIMPLE_HOSTED_CONFINED_FILE_IMPL_H
#define SIMPLE_HOSTED_CONFINED_FILE_IMPL_H

/* Descriptor-relative hosted file authority for mission-critical environment
 * replay.  The caller pins a capability root once, then every component is
 * resolved relative to that descriptor without following links.  All path
 * storage is fixed-size and the read/write operations use caller storage. */

#include <stdint.h>
#include <stddef.h>
#include <string.h>
#include <limits.h>

#if !defined(_WIN32) && !defined(__simpleos__)
#include <errno.h>
#include <fcntl.h>
#include <sys/stat.h>
#include <unistd.h>

#ifndef SIMPLE_CONFINED_PATH_MAX
#define SIMPLE_CONFINED_PATH_MAX 4096
#endif

static int simple_confined_copy_path(char out[SIMPLE_CONFINED_PATH_MAX],
                                     const uint8_t *path, int64_t path_len) {
    if (!path || path_len <= 0 || path_len >= SIMPLE_CONFINED_PATH_MAX ||
        memchr(path, '\0', (size_t)path_len) != NULL) return 0;
    memcpy(out, path, (size_t)path_len);
    out[path_len] = '\0';
    return 1;
}

static int simple_confined_component_ok(const char *part) {
    return part && part[0] != '\0' && strcmp(part, ".") != 0 &&
           strcmp(part, "..") != 0;
}

int64_t rt_hosted_confined_root_open(const uint8_t *path, int64_t path_len) {
    char copy[SIMPLE_CONFINED_PATH_MAX];
    if (!simple_confined_copy_path(copy, path, path_len)) return -1;
    int fd = copy[0] == '/' ? open("/", O_RDONLY | O_DIRECTORY | O_CLOEXEC)
                            : open(".", O_RDONLY | O_DIRECTORY | O_CLOEXEC);
    if (fd < 0) return -1;
    char *walk = copy[0] == '/' ? copy + 1 : copy;
    char *save = NULL;
    for (char *part = strtok_r(walk, "/", &save); part;
         part = strtok_r(NULL, "/", &save)) {
        if (!simple_confined_component_ok(part)) { close(fd); return -1; }
        int next = openat(fd, part,
            O_RDONLY | O_DIRECTORY | O_NOFOLLOW | O_CLOEXEC);
        if (next < 0) { close(fd); return -1; }
        close(fd);
        fd = next;
    }
    struct stat st;
    if (fstat(fd, &st) != 0 || !S_ISDIR(st.st_mode)) { close(fd); return -1; }
    return (int64_t)fd;
}

int64_t rt_hosted_confined_file_open(int64_t root_fd64,
        const uint8_t *path_region, int64_t region_len,
        int64_t relative_offset, int64_t relative_len, int64_t access) {
    if (root_fd64 < 0 || root_fd64 > INT_MAX || (access != 0 && access != 1))
        return -1;
    if (region_len < 0 || relative_offset < 0 || relative_len < 0 ||
        relative_offset > region_len - relative_len) return -1;
    char copy[SIMPLE_CONFINED_PATH_MAX];
    if (!simple_confined_copy_path(copy, path_region + relative_offset, relative_len) ||
        copy[0] == '/' || copy[relative_len - 1] == '/') return -1;
    if (strstr(copy, "//") != NULL) return -1;
    int parent = fcntl((int)root_fd64, F_DUPFD_CLOEXEC, 0);
    if (parent < 0) return -1;
    char *save = NULL;
    char *part = strtok_r(copy, "/", &save);
    if (!simple_confined_component_ok(part)) { close(parent); return -1; }
    for (;;) {
        char *next_part = strtok_r(NULL, "/", &save);
        if (!next_part) break;
        if (!simple_confined_component_ok(next_part)) { close(parent); return -1; }
        int next = openat(parent, part,
            O_RDONLY | O_DIRECTORY | O_NOFOLLOW | O_CLOEXEC);
        if (next < 0) { close(parent); return -1; }
        close(parent);
        parent = next;
        part = next_part;
    }
    int flags = (access == 0 ? O_RDONLY : O_RDWR) | O_NOFOLLOW | O_CLOEXEC;
    int fd = openat(parent, part, flags);
    close(parent);
    if (fd < 0) return -1;
    struct stat st;
    if (fstat(fd, &st) != 0 || !S_ISREG(st.st_mode)) { close(fd); return -1; }
    return (int64_t)fd;
}

int64_t rt_hosted_confined_file_read_at(int64_t fd64, int64_t file_offset,
        uint8_t *out, int64_t out_len, int64_t out_offset, int64_t capacity) {
    if (fd64 < 0 || fd64 > INT_MAX || file_offset < 0 || out_len < 0 ||
        out_offset < 0 || capacity < 0 || out_offset > out_len - capacity ||
        (capacity > 0 && !out) || (uint64_t)capacity > (uint64_t)SSIZE_MAX)
        return -1;
    ssize_t got;
    do { got = pread((int)fd64, out + out_offset, (size_t)capacity, (off_t)file_offset); }
    while (got < 0 && errno == EINTR);
    return got < 0 ? -1 : (int64_t)got;
}

int64_t rt_hosted_confined_file_write_at(int64_t fd64, int64_t file_offset,
        const uint8_t *bytes, int64_t bytes_len,
        int64_t bytes_offset, int64_t length) {
    if (fd64 < 0 || fd64 > INT_MAX || file_offset < 0 || bytes_len < 0 ||
        bytes_offset < 0 || length < 0 || bytes_offset > bytes_len - length ||
        (length > 0 && !bytes) || (uint64_t)length > (uint64_t)SSIZE_MAX)
        return -1;
    int64_t used = 0;
    while (used < length) {
        ssize_t wrote = pwrite((int)fd64, bytes + bytes_offset + used,
            (size_t)(length - used), (off_t)(file_offset + used));
        if (wrote < 0 && errno == EINTR) continue;
        if (wrote <= 0) return -1;
        used += (int64_t)wrote;
    }
    return used;
}

int rt_hosted_confined_file_close(int64_t fd64) {
    if (fd64 < 0 || fd64 > INT_MAX) return 0;
    return close((int)fd64) == 0;
}

#else
int64_t rt_hosted_confined_root_open(const uint8_t *p, int64_t n) { (void)p; (void)n; return -1; }
int64_t rt_hosted_confined_file_open(int64_t r, const uint8_t *p, int64_t z, int64_t o, int64_t n, int64_t a) { (void)r; (void)p; (void)z; (void)o; (void)n; (void)a; return -1; }
int64_t rt_hosted_confined_file_read_at(int64_t f, int64_t o, uint8_t *p, int64_t z, int64_t b, int64_t n) { (void)f; (void)o; (void)p; (void)z; (void)b; (void)n; return -1; }
int64_t rt_hosted_confined_file_write_at(int64_t f, int64_t o, const uint8_t *p, int64_t z, int64_t b, int64_t n) { (void)f; (void)o; (void)p; (void)z; (void)b; (void)n; return -1; }
int rt_hosted_confined_file_close(int64_t f) { (void)f; return 0; }
#endif

#endif
