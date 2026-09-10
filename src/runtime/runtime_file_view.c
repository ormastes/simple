/* Secure, descriptor-pinned read-only file views for compiler snapshots.
 *
 * This is the sole C owner of rt_file_view_* and rt_pinned_archive_*.
 * Paths are opened component-by-component beneath an already opened root;
 * absolute paths, dot components, symlinks, and non-regular leaves fail
 * closed.  Public handles index this TU's private table, not host file
 * descriptors, so a forged handle cannot close an unrelated descriptor.
 */
#include "runtime.h"

#include <stdint.h>
#include <stdlib.h>
#include <string.h>

/* native_all needs a Rust-visible ABI owner as well as the standalone C
 * owner. In that build only, compile these bodies under private names; the
 * Rust module exports the public rt_* names as zero-policy aliases. */
#if defined(SIMPLE_RUNTIME_FILE_VIEW_RUST_OWNER)
#define rt_file_view_open_beneath_no_follow_v1 spl_c_file_view_open_beneath_no_follow_v1
#define rt_file_view_mapping_supported_v1 spl_c_file_view_mapping_supported_v1
#define rt_file_view_map_copy_v1 spl_c_file_view_map_copy_v1
#define rt_file_view_pread_exact_v1 spl_c_file_view_pread_exact_v1
#define rt_file_view_prefetch_v1 spl_c_file_view_prefetch_v1
#define rt_file_view_device_v1 spl_c_file_view_device_v1
#define rt_file_view_inode_v1 spl_c_file_view_inode_v1
#define rt_file_view_size_v1 spl_c_file_view_size_v1
#define rt_file_view_close_v1 spl_c_file_view_close_v1
#define rt_pinned_archive_open_beneath_v1 spl_c_pinned_archive_open_beneath_v1
#define rt_pinned_archive_device_v1 spl_c_pinned_archive_device_v1
#define rt_pinned_archive_inode_v1 spl_c_pinned_archive_inode_v1
#define rt_pinned_archive_size_v1 spl_c_pinned_archive_size_v1
#define rt_pinned_archive_close_v1 spl_c_pinned_archive_close_v1
#endif

#ifdef _WIN32

int64_t rt_file_view_open_beneath_no_follow_v1(int64_t root, int64_t path) { (void)root; (void)path; return -1; }
int8_t rt_file_view_mapping_supported_v1(int64_t handle) { (void)handle; return 0; }
int64_t rt_file_view_map_copy_v1(int64_t handle, uint64_t offset, uint64_t length) { (void)handle; (void)offset; (void)length; return 0; }
int64_t rt_file_view_pread_exact_v1(int64_t handle, uint64_t offset, uint64_t length) { (void)handle; (void)offset; (void)length; return 0; }
int8_t rt_file_view_prefetch_v1(int64_t handle, uint64_t offset, uint64_t length) { (void)handle; (void)offset; (void)length; return 0; }
int64_t rt_file_view_device_v1(int64_t handle) { (void)handle; return -1; }
int64_t rt_file_view_inode_v1(int64_t handle) { (void)handle; return -1; }
int64_t rt_file_view_size_v1(int64_t handle) { (void)handle; return -1; }
int8_t rt_file_view_close_v1(int64_t handle) { (void)handle; return 0; }
int64_t rt_pinned_archive_open_beneath_v1(int64_t root, int64_t path) { (void)root; (void)path; return -4; }
int64_t rt_pinned_archive_device_v1(int64_t handle) { (void)handle; return -1; }
int64_t rt_pinned_archive_inode_v1(int64_t handle) { (void)handle; return -1; }
int64_t rt_pinned_archive_size_v1(int64_t handle) { (void)handle; return -1; }
int8_t rt_pinned_archive_close_v1(int64_t handle) { (void)handle; return 0; }

#else

#include <errno.h>
#include <fcntl.h>
#include <pthread.h>
#include <sys/mman.h>
#include <sys/stat.h>
#include <unistd.h>

#ifndef O_CLOEXEC
#define O_CLOEXEC 0
#endif
#ifndef O_NOFOLLOW
#define O_NOFOLLOW 0
#endif

#define FILE_VIEW_CAPACITY 1024
#define FILE_VIEW_HANDLE_BASE INT64_C(0x4656000000000000)

static int file_view_fds[FILE_VIEW_CAPACITY];
static uint32_t file_view_generations[FILE_VIEW_CAPACITY];
static pthread_mutex_t file_view_lock = PTHREAD_MUTEX_INITIALIZER;

static int copy_text_value(int64_t value, char **out) {
    const uint8_t *data = rt_string_data(value);
    int64_t len = rt_string_len(value);
    if (len < 0 || len > 32768 || (!data && len) ||
        (len && memchr(data, 0, (size_t)len))) return 0;
    char *copy = (char *)malloc((size_t)len + 1);
    if (!copy) return 0;
    if (len) memcpy(copy, data, (size_t)len);
    copy[len] = 0;
    *out = copy;
    return 1;
}

static int relative_path_valid(const char *path) {
    if (!path || !path[0] || path[0] == '/') return 0;
    const char *start = path;
    for (const char *p = path;; ++p) {
        if (*p != '/' && *p != 0) continue;
        size_t n = (size_t)(p - start);
        if (n == 0 || (n == 1 && start[0] == '.') ||
            (n == 2 && start[0] == '.' && start[1] == '.')) return 0;
        if (*p == 0) return 1;
        start = p + 1;
    }
}

static int open_regular_beneath(const char *root, const char *relative) {
    if (!relative_path_valid(relative)) return -2;
    int current = open(root, O_RDONLY | O_DIRECTORY | O_NOFOLLOW | O_CLOEXEC);
    if (current < 0) return (errno == ELOOP ? -3 : -1);
    char *work = strdup(relative);
    if (!work) { close(current); return -1; }
    char *save = NULL;
    char *part = strtok_r(work, "/", &save);
    while (part) {
        char *next = strtok_r(NULL, "/", &save);
        int flags = O_RDONLY | O_NOFOLLOW | O_CLOEXEC | (next ? O_DIRECTORY : 0);
        int opened = openat(current, part, flags);
        int saved_errno = errno;
        close(current);
        if (opened < 0) {
            free(work);
            return (saved_errno == ELOOP ? -3 : -1);
        }
        current = opened;
        part = next;
    }
    free(work);
    struct stat st;
    if (fstat(current, &st) != 0 || !S_ISREG(st.st_mode)) {
        close(current);
        return -3;
    }
    return current;
}

static int64_t register_fd(int fd) {
    int64_t result = -1;
    pthread_mutex_lock(&file_view_lock);
    for (uint32_t i = 0; i < FILE_VIEW_CAPACITY; ++i) {
        if (file_view_fds[i] == 0) {
            file_view_fds[i] = fd + 1;
            uint32_t generation = ++file_view_generations[i];
            if (!generation) generation = ++file_view_generations[i];
            result = FILE_VIEW_HANDLE_BASE | ((int64_t)generation << 10) | i;
            break;
        }
    }
    pthread_mutex_unlock(&file_view_lock);
    if (result < 0) close(fd);
    return result;
}

static int lookup_fd_locked(int64_t handle) {
    if ((handle & INT64_C(0xFFFF000000000000)) != FILE_VIEW_HANDLE_BASE) return -1;
    uint32_t slot = (uint32_t)(handle & 1023);
    uint32_t generation = (uint32_t)((uint64_t)handle >> 10);
    if (slot >= FILE_VIEW_CAPACITY || file_view_fds[slot] == 0 ||
        file_view_generations[slot] != generation) return -1;
    return file_view_fds[slot] - 1;
}

static int64_t bytes_array(const uint8_t *bytes, uint64_t length) {
    if (length > INT64_MAX) return 0;
    SplArray *array = rt_array_new((int64_t)length);
    if (!array) return 0;
    for (uint64_t i = 0; i < length; ++i) {
        if (!rt_array_push(array, (int64_t)bytes[i] << 3)) {
            rt_array_free(array);
            return 0;
        }
    }
    return (int64_t)(uintptr_t)array;
}

int64_t rt_file_view_open_beneath_no_follow_v1(int64_t root_value, int64_t path_value) {
    char *root = NULL, *path = NULL;
    if (!copy_text_value(root_value, &root) || !copy_text_value(path_value, &path)) {
        free(root); free(path); return -1;
    }
    int fd = open_regular_beneath(root, path);
    free(root); free(path);
    return fd < 0 ? fd : register_fd(fd);
}

int8_t rt_file_view_mapping_supported_v1(int64_t handle) {
    pthread_mutex_lock(&file_view_lock);
    int ok = lookup_fd_locked(handle) >= 0;
    pthread_mutex_unlock(&file_view_lock);
    return (int8_t)ok;
}

static int64_t read_exact_array(int64_t handle, uint64_t offset, uint64_t length, int mapped) {
    if (offset > (uint64_t)INT64_MAX || length > (uint64_t)SIZE_MAX ||
        length > (uint64_t)INT64_MAX || offset > UINT64_MAX - length ||
        offset + length > (uint64_t)INT64_MAX) return 0;
    pthread_mutex_lock(&file_view_lock);
    int fd = lookup_fd_locked(handle);
    if (fd < 0) { pthread_mutex_unlock(&file_view_lock); return 0; }
    struct stat st;
    if (fstat(fd, &st) != 0 || st.st_size < 0 ||
        offset + length > (uint64_t)st.st_size) {
        pthread_mutex_unlock(&file_view_lock);
        return 0;
    }
    uint8_t *buffer = length ? (uint8_t *)malloc((size_t)length) : NULL;
    if (length && !buffer) { pthread_mutex_unlock(&file_view_lock); return 0; }
    int ok = 1;
    if (mapped && length) {
        long page = sysconf(_SC_PAGESIZE);
        if (page <= 0) page = 4096;
        uint64_t base = offset - (offset % (uint64_t)page);
        uint64_t delta = offset - base;
        if (length > SIZE_MAX - delta) ok = 0;
        void *map = ok ? mmap(NULL, (size_t)(length + delta), PROT_READ, MAP_PRIVATE, fd, (off_t)base) : MAP_FAILED;
        if (map == MAP_FAILED) ok = 0;
        else { memcpy(buffer, (uint8_t *)map + delta, (size_t)length); munmap(map, (size_t)(length + delta)); }
    } else {
        uint64_t done = 0;
        while (done < length) {
            ssize_t n = pread(fd, buffer + done, (size_t)(length - done), (off_t)(offset + done));
            if (n < 0 && errno == EINTR) continue;
            if (n <= 0) { ok = 0; break; }
            done += (uint64_t)n;
        }
    }
    int64_t result = ok ? bytes_array(buffer, length) : 0;
    free(buffer);
    pthread_mutex_unlock(&file_view_lock);
    return result;
}

int64_t rt_file_view_map_copy_v1(int64_t handle, uint64_t offset, uint64_t length) { return read_exact_array(handle, offset, length, 1); }
int64_t rt_file_view_pread_exact_v1(int64_t handle, uint64_t offset, uint64_t length) { return read_exact_array(handle, offset, length, 0); }

int8_t rt_file_view_prefetch_v1(int64_t handle, uint64_t offset, uint64_t length) {
    pthread_mutex_lock(&file_view_lock);
    int fd = lookup_fd_locked(handle);
#if defined(POSIX_FADV_WILLNEED)
    int ok = fd >= 0 && posix_fadvise(fd, (off_t)offset, (off_t)length, POSIX_FADV_WILLNEED) == 0;
#else
    int ok = fd >= 0; (void)offset; (void)length;
#endif
    pthread_mutex_unlock(&file_view_lock);
    return (int8_t)ok;
}

static int64_t identity_field(int64_t handle, int field) {
    pthread_mutex_lock(&file_view_lock);
    int fd = lookup_fd_locked(handle);
    struct stat st;
    int ok = fd >= 0 && fstat(fd, &st) == 0 && S_ISREG(st.st_mode);
    int64_t value = -1;
    if (ok) value = field == 0 ? (int64_t)st.st_dev : field == 1 ? (int64_t)st.st_ino : (int64_t)st.st_size;
    pthread_mutex_unlock(&file_view_lock);
    return value;
}

int64_t rt_file_view_device_v1(int64_t handle) { return identity_field(handle, 0); }
int64_t rt_file_view_inode_v1(int64_t handle) { return identity_field(handle, 1); }
int64_t rt_file_view_size_v1(int64_t handle) { return identity_field(handle, 2); }

int8_t rt_file_view_close_v1(int64_t handle) {
    pthread_mutex_lock(&file_view_lock);
    int fd = lookup_fd_locked(handle);
    if (fd < 0) { pthread_mutex_unlock(&file_view_lock); return 0; }
    uint32_t slot = (uint32_t)(handle & 1023);
    file_view_fds[slot] = 0;
    pthread_mutex_unlock(&file_view_lock);
    return (int8_t)(close(fd) == 0);
}

int64_t rt_pinned_archive_open_beneath_v1(int64_t root, int64_t path) { return rt_file_view_open_beneath_no_follow_v1(root, path); }
int64_t rt_pinned_archive_device_v1(int64_t handle) { return rt_file_view_device_v1(handle); }
int64_t rt_pinned_archive_inode_v1(int64_t handle) { return rt_file_view_inode_v1(handle); }
int64_t rt_pinned_archive_size_v1(int64_t handle) { return rt_file_view_size_v1(handle); }
int8_t rt_pinned_archive_close_v1(int64_t handle) { return rt_file_view_close_v1(handle); }

#endif
