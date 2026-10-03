#ifndef SIMPLE_RUNTIME_SOSIX_DIRECTORY_ROOTS_V1_H
#define SIMPLE_RUNTIME_SOSIX_DIRECTORY_ROOTS_V1_H

/* Descriptor/handle-owned directory pairs. Policy: existing absolute roots,
 * no symlink/reparse ancestors, and no equal or ancestor physical location.
 * Tokens are generation identities, never caller-dereferenced pointers.
 * Revalidation detects pathname replacement; it is not a write transaction.
 */
#include <stdint.h>
#include <stddef.h>
#include <stdlib.h>
#include <string.h>
#include <stdio.h>
#include <errno.h>
#include <limits.h>
#define RT_SDR_PATH_V1 4096
#define RT_SDR_SLOTS_V1 32
#define RT_SDR_WORDS_V1 8
#define RT_SDR_OVERLAP_V1 (-1001)
#define RT_SDR_CHANGED_V1 (-1002)

#if defined(_WIN32)
#include <windows.h>
#include <wchar.h>
typedef struct RtSdrRootV1 {
    char path[RT_SDR_PATH_V1];
    uint64_t identity[3];
    HANDLE ancestors[256];
    size_t count;
    wchar_t physical[RT_SDR_PATH_V1];
} RtSdrRootV1;
static SRWLOCK rt_sdr_lock_v1 = SRWLOCK_INIT;
#define RT_SDR_LOCK() AcquireSRWLockExclusive(&rt_sdr_lock_v1)
#define RT_SDR_UNLOCK() ReleaseSRWLockExclusive(&rt_sdr_lock_v1)
#elif defined(__linux__)
#include <fcntl.h>
#include <unistd.h>
#include <sys/stat.h>
#include <sys/sysmacros.h>
#include <pthread.h>
typedef struct RtSdrRootV1 {
    char path[RT_SDR_PATH_V1];
    uint64_t identity[3];
    int fd;
    uint64_t mount_id;
    char physical[RT_SDR_PATH_V1];
    char filesystem[64];
} RtSdrRootV1;
static pthread_mutex_t rt_sdr_lock_v1 = PTHREAD_MUTEX_INITIALIZER;
#define RT_SDR_LOCK() ((void)pthread_mutex_lock(&rt_sdr_lock_v1))
#define RT_SDR_UNLOCK() ((void)pthread_mutex_unlock(&rt_sdr_lock_v1))
#else
typedef struct RtSdrRootV1 { char path[RT_SDR_PATH_V1]; uint64_t identity[3]; } RtSdrRootV1;
#define RT_SDR_LOCK() ((void)0)
#define RT_SDR_UNLOCK() ((void)0)
#endif

typedef struct RtSdrPairV1 {
    int64_t token;
    RtSdrRootV1 shared;
    RtSdrRootV1 private_root;
} RtSdrPairV1;
static RtSdrPairV1 rt_sdr_pairs_v1[RT_SDR_SLOTS_V1];
static int64_t rt_sdr_next_v1 = 1;

static int rt_sdr_path_v1(const char *input, char *out) {
    if (!input || !input[0]) return -EINVAL;
    size_t length = strlen(input);
    if (length >= RT_SDR_PATH_V1) return -ENAMETOOLONG;
    memcpy(out, input, length + 1);
    for (size_t i = 0; i < length; ++i) {
        if ((unsigned char)out[i] < 32 || out[i] == 127) return -EINVAL;
#if defined(_WIN32)
        if (out[i] == '\\') out[i] = '/';
#endif
    }
#if defined(_WIN32)
    if (length < 3 || out[1] != ':' || out[2] != '/' ||
        !((out[0] >= 'A' && out[0] <= 'Z') || (out[0] >= 'a' && out[0] <= 'z')))
        return -EINVAL;
    size_t start = 3;
#else
    if (out[0] != '/') return -EINVAL;
    size_t start = 1;
#endif
    if (length <= start || out[length - 1] == '/') return -EINVAL;
    for (size_t at = start; at < length;) {
        size_t end = at;
        while (end < length && out[end] != '/') ++end;
        size_t n = end - at;
        if (!n || (n == 1 && out[at] == '.') ||
            (n == 2 && out[at] == '.' && out[at + 1] == '.')) return -EINVAL;
#if defined(_WIN32)
        if (out[end - 1] == '.' || out[end - 1] == ' ' || memchr(out + at, ':', n))
            return -EINVAL;
#endif
        at = end + 1;
    }
    return 0;
}

static int rt_sdr_identity_equal_v1(const RtSdrRootV1 *a, const RtSdrRootV1 *b) {
    return a->identity[0] == b->identity[0] && a->identity[1] == b->identity[1] &&
        a->identity[2] == b->identity[2];
}

#if defined(_WIN32)
static void rt_sdr_root_close_v1(RtSdrRootV1 *root) {
    while (root->count) CloseHandle(root->ancestors[--root->count]);
}
static int rt_sdr_root_open_v1(const char *path, RtSdrRootV1 *root) {
    memset(root, 0, sizeof(*root));
    int status = rt_sdr_path_v1(path, root->path);
    if (status) return status;
    wchar_t wide[RT_SDR_PATH_V1];
    if (!MultiByteToWideChar(CP_UTF8, MB_ERR_INVALID_CHARS, root->path, -1,
            wide, RT_SDR_PATH_V1)) return -EINVAL;
    size_t length = wcslen(wide);
    for (size_t end = 3; end <= length; ++end) {
        if (end != 3 && end != length && wide[end] != L'/') continue;
        if (root->count == 256) { status = -ENAMETOOLONG; goto fail; }
        wchar_t saved = wide[end]; wide[end] = 0;
        HANDLE handle = CreateFileW(wide, FILE_READ_ATTRIBUTES | FILE_LIST_DIRECTORY,
            FILE_SHARE_READ | FILE_SHARE_WRITE, NULL, OPEN_EXISTING,
            FILE_FLAG_BACKUP_SEMANTICS | FILE_FLAG_OPEN_REPARSE_POINT, NULL);
        wide[end] = saved;
        if (handle == INVALID_HANDLE_VALUE) {
            DWORD error = GetLastError();
            status = error == ERROR_FILE_NOT_FOUND || error == ERROR_PATH_NOT_FOUND ? -ENOENT : -EACCES;
            goto fail;
        }
        root->ancestors[root->count++] = handle;
        BY_HANDLE_FILE_INFORMATION info;
        if (!GetFileInformationByHandle(handle, &info)) { status = -EIO; goto fail; }
        if (!(info.dwFileAttributes & FILE_ATTRIBUTE_DIRECTORY) ||
            (info.dwFileAttributes & FILE_ATTRIBUTE_REPARSE_POINT)) {
            status = -ELOOP; goto fail;
        }
    }
    HANDLE handle = root->ancestors[root->count - 1];
    BY_HANDLE_FILE_INFORMATION identity;
    if (!GetFileInformationByHandle(handle, &identity)) { status = -EIO; goto fail; }
    root->identity[0] = identity.dwVolumeSerialNumber;
    root->identity[1] = ((uint64_t)identity.nFileIndexHigh << 32) | identity.nFileIndexLow;
    root->identity[2] = 0;
    if (!root->identity[1]) { status = -EIO; goto fail; }
    DWORD count = GetFinalPathNameByHandleW(handle, root->physical, RT_SDR_PATH_V1,
        FILE_NAME_NORMALIZED | VOLUME_NAME_GUID);
    if (!count || count >= RT_SDR_PATH_V1) { status = -ENOTSUP; goto fail; }
    while (count && (root->physical[count - 1] == L'\\' || root->physical[count - 1] == L'/'))
        root->physical[--count] = 0;
    return 0;
fail:
    rt_sdr_root_close_v1(root);
    return status;
}
static int rt_sdr_physical_contains_v1(const wchar_t *a, const wchar_t *b) {
    size_t n = wcslen(a), m = wcslen(b);
    return m >= n && CompareStringOrdinal(a, (int)n, b, (int)n, TRUE) == CSTR_EQUAL &&
        (m == n || b[n] == L'\\' || b[n] == L'/');
}
static int rt_sdr_overlap_v1(const RtSdrRootV1 *a, const RtSdrRootV1 *b) {
    return rt_sdr_identity_equal_v1(a, b) ||
        rt_sdr_physical_contains_v1(a->physical, b->physical) ||
        rt_sdr_physical_contains_v1(b->physical, a->physical);
}
static int rt_sdr_location_equal_v1(const RtSdrRootV1 *a, const RtSdrRootV1 *b) {
    return rt_sdr_identity_equal_v1(a, b) &&
        CompareStringOrdinal(a->physical, -1, b->physical, -1, TRUE) == CSTR_EQUAL;
}
#elif defined(__linux__)
static void rt_sdr_root_close_v1(RtSdrRootV1 *root) {
    if (root->fd >= 0) { close(root->fd); root->fd = -1; }
}
static int rt_sdr_contains_v1(const char *a, const char *b) {
    size_t n = strlen(a), m = strlen(b);
    return m >= n && !memcmp(a, b, n) &&
        (n == 1 || m == n || b[n] == '/');
}
static int rt_sdr_mount_unescape_v1(const char *input, char *out) {
    size_t n = 0;
    for (size_t i = 0; input[i]; ++i) {
        unsigned int ch = (unsigned char)input[i];
        if (ch == '\\') {
            if (!input[i+1] || !input[i+2] || !input[i+3] ||
                input[i+1] < '0' || input[i+1] > '7' ||
                input[i+2] < '0' || input[i+2] > '7' ||
                input[i+3] < '0' || input[i+3] > '7') return -EINVAL;
            ch = (input[i+1]-'0')*64 + (input[i+2]-'0')*8 + input[i+3]-'0'; i += 3;
        }
        if (ch < 32 || ch > 255 || n + 1 >= RT_SDR_PATH_V1) return -EINVAL;
        out[n++] = (char)ch;
    }
    out[n] = 0;
    return 0;
}
static int rt_sdr_mount_location_v1(RtSdrRootV1 *root) {
    char proc[80], line[16384], actual[RT_SDR_PATH_V1];
    snprintf(proc, sizeof(proc), "/proc/self/fdinfo/%d", root->fd);
    FILE *info = fopen(proc, "r");
    if (!info) return -ENOTSUP;
    unsigned long long mount_id = 0;
    while (fgets(line, sizeof(line), info)) {
        if (sscanf(line, "mnt_id:\t%llu", &mount_id) == 1) break;
    }
    fclose(info);
    if (!mount_id) return -ENOTSUP;
    snprintf(proc, sizeof(proc), "/proc/self/fd/%d", root->fd);
    ssize_t n = readlink(proc, actual, sizeof(actual) - 1);
    if (n <= 0 || n >= (ssize_t)sizeof(actual) - 1) return -EIO;
    actual[n] = 0;
    FILE *mounts = fopen("/proc/self/mountinfo", "r");
    if (!mounts) return -ENOTSUP;
    int status = -ENOTSUP;
    size_t read_bytes = 0;
    while (fgets(line, sizeof(line), mounts)) {
        read_bytes += strlen(line);
        if (read_bytes > 4 * 1024 * 1024 || !strchr(line, '\n')) { status = -EOVERFLOW; break; }
        unsigned long long id = 0, parent = 0;
        unsigned int major_id = 0, minor_id = 0;
        char escaped_root[RT_SDR_PATH_V1], escaped_mount[RT_SDR_PATH_V1];
        if (sscanf(line, "%llu %llu %u:%u %4095s %4095s", &id, &parent,
                &major_id, &minor_id, escaped_root, escaped_mount) != 6 || id != mount_id) continue;
        char mount_root[RT_SDR_PATH_V1], mount_path[RT_SDR_PATH_V1];
        if (rt_sdr_mount_unescape_v1(escaped_root, mount_root) ||
            rt_sdr_mount_unescape_v1(escaped_mount, mount_path) ||
            !rt_sdr_contains_v1(mount_path, actual)) { status = -EIO; break; }
        if ((uint64_t)makedev(major_id, minor_id) != root->identity[0]) { status = -EIO; break; }
        char *separator = strstr(line, " - ");
        if (!separator || sscanf(separator + 3, "%63s", root->filesystem) != 1) { status = -EIO; break; }
        const char *relative = actual + strlen(mount_path);
        if (!strcmp(mount_path, "/")) relative = actual;
        if (!strcmp(mount_root, "/")) mount_root[0] = 0;
        int length = snprintf(root->physical, sizeof(root->physical), "%s%s", mount_root, relative);
        if (length < 0 || length >= (int)sizeof(root->physical)) { status = -ENAMETOOLONG; break; }
        if (!root->physical[0]) strcpy(root->physical, "/");
        root->mount_id = (uint64_t)mount_id;
        status = 0; break;
    }
    fclose(mounts);
    return status;
}
static int rt_sdr_mount_id_v1(int fd, uint64_t *out) {
    char proc[80], line[256];
    snprintf(proc, sizeof(proc), "/proc/self/fdinfo/%d", fd);
    FILE *info = fopen(proc, "r");
    if (!info) return -ENOTSUP;
    unsigned long long mount_id = 0;
    for (unsigned int i = 0; i < 64 && fgets(line, sizeof(line), info); ++i)
        if (sscanf(line, "mnt_id:\t%llu", &mount_id) == 1) break;
    fclose(info);
    if (!mount_id) return -ENOTSUP;
    *out = (uint64_t)mount_id; return 0;
}
static int rt_sdr_root_open_mode_v1(const char *path, RtSdrRootV1 *root, int physical) {
    memset(root, 0, sizeof(*root)); root->fd = -1;
    int status = rt_sdr_path_v1(path, root->path);
    if (status) return status;
    int fd = open("/", O_RDONLY | O_DIRECTORY | O_CLOEXEC);
    if (fd < 0) return -errno;
    char copy[RT_SDR_PATH_V1]; strcpy(copy, root->path + 1);
    char *part = copy;
    while (part && *part) {
        char *slash = strchr(part, '/'); if (slash) *slash = 0;
        int next = openat(fd, part, O_RDONLY | O_DIRECTORY | O_NOFOLLOW | O_CLOEXEC);
        int saved = errno;
        close(fd);
        if (next < 0) return -(saved ? saved : EIO);
        fd = next; part = slash ? slash + 1 : NULL;
    }
    root->fd = fd;
    struct stat stat;
    if (fstat(fd, &stat) || !S_ISDIR(stat.st_mode) || !stat.st_ino) { status = -EIO; goto fail; }
    root->identity[0] = (uint64_t)stat.st_dev;
    root->identity[1] = (uint64_t)stat.st_ino;
    root->identity[2] = 0;
    status = physical ? rt_sdr_mount_location_v1(root) : rt_sdr_mount_id_v1(fd, &root->mount_id);
    if (status) goto fail;
    return 0;
fail:
    rt_sdr_root_close_v1(root); return status;
}
static int rt_sdr_root_open_v1(const char *path, RtSdrRootV1 *root) {
    return rt_sdr_root_open_mode_v1(path, root, 1);
}
static int rt_sdr_root_fast_v1(const char *path, RtSdrRootV1 *root) {
    /* Bind roots can move without inode or mount-id changes. */
    return rt_sdr_root_open_mode_v1(path, root, 1);
}
static int rt_sdr_overlap_v1(const RtSdrRootV1 *a, const RtSdrRootV1 *b) {
    /* Visible nesting is forbidden even across a child filesystem mount. */
    if (rt_sdr_contains_v1(a->path, b->path) || rt_sdr_contains_v1(b->path, a->path)) return 1;
    return a->identity[0] == b->identity[0] &&
        (rt_sdr_identity_equal_v1(a, b) || rt_sdr_contains_v1(a->physical, b->physical) ||
            rt_sdr_contains_v1(b->physical, a->physical));
}
static int rt_sdr_location_equal_v1(const RtSdrRootV1 *a, const RtSdrRootV1 *b) {
    return rt_sdr_identity_equal_v1(a, b) && a->mount_id == b->mount_id &&
        !strcmp(a->physical, b->physical) && !strcmp(a->filesystem, b->filesystem);
}
#else
static void rt_sdr_root_close_v1(RtSdrRootV1 *root) { (void)root; }
static int rt_sdr_root_open_v1(const char *path, RtSdrRootV1 *root) { (void)path; (void)root; return -ENOTSUP; }
static int rt_sdr_overlap_v1(const RtSdrRootV1 *a, const RtSdrRootV1 *b) { (void)a; (void)b; return 1; }
static int rt_sdr_location_equal_v1(const RtSdrRootV1 *a, const RtSdrRootV1 *b) { (void)a; (void)b; return 0; }
#endif

#if !defined(__linux__)
static int rt_sdr_root_fast_v1(const char *path, RtSdrRootV1 *root) {
    return rt_sdr_root_open_v1(path, root);
}
#endif

/* Create only a prospective disjoint private subtree, relative to the nearest
 * existing no-follow parent. The final admission still opens the created root.
 * Linux mkdir/open walk stays fd-relative. Windows holds all parent handles
 * without DELETE sharing while it creates and opens each next component.
 */
static int rt_sdr_create_private_v1(const RtSdrRootV1 *shared, const char *requested) {
#if defined(__linux__) || defined(_WIN32)
    char target[RT_SDR_PATH_V1], parent_path[RT_SDR_PATH_V1];
    int status = rt_sdr_path_v1(requested, target);
    if (status) return status;
    strcpy(parent_path, target);
    RtSdrRootV1 parent;
    for (;;) {
        char *last = strrchr(parent_path, '/');
        if (!last || last == parent_path) return -ENOENT;
#if defined(_WIN32)
        if (last <= parent_path + 2) return -ENOENT;
#endif
        *last = 0;
        status = rt_sdr_root_open_v1(parent_path, &parent);
        if (!status) break;
        if (status != -ENOENT) return status;
    }
    RtSdrRootV1 prospective = parent;
    strcpy(prospective.path, target);
#if defined(_WIN32)
    wchar_t tail[RT_SDR_PATH_V1];
    if (!MultiByteToWideChar(CP_UTF8, MB_ERR_INVALID_CHARS,
            target + strlen(parent_path), -1, tail, RT_SDR_PATH_V1)) {
        rt_sdr_root_close_v1(&parent); return -EINVAL;
    }
    for (size_t i = 0; tail[i]; ++i) if (tail[i] == L'/') tail[i] = L'\\';
    if (wcslen(parent.physical) + wcslen(tail) >= RT_SDR_PATH_V1) {
        rt_sdr_root_close_v1(&parent); return -ENAMETOOLONG;
    }
    wcscpy(prospective.physical, parent.physical); wcscat(prospective.physical, tail);
#else
    int n = snprintf(prospective.physical, sizeof(prospective.physical), "%s%s",
        parent.physical, target + strlen(parent_path));
    if (n < 0 || n >= RT_SDR_PATH_V1) { rt_sdr_root_close_v1(&parent); return -ENAMETOOLONG; }
#endif
    /* The prospective node has no inode yet: compare paths, not parent inode. */
    prospective.identity[1] = 0; prospective.identity[2] = 0;
    if (rt_sdr_overlap_v1(shared, &prospective)) {
        rt_sdr_root_close_v1(&parent); return RT_SDR_OVERLAP_V1;
    }
    char walk[RT_SDR_PATH_V1]; strcpy(walk, parent_path);
    char remaining[RT_SDR_PATH_V1]; strcpy(remaining, target + strlen(parent_path) + 1);
    char *part = remaining;
    while (part && *part) {
        char *slash = strchr(part, '/'); if (slash) *slash = 0;
        size_t length = strlen(walk), part_length = strlen(part);
        if (length + part_length + 2 > sizeof(walk)) { status = -ENAMETOOLONG; break; }
        walk[length++] = '/'; memcpy(walk + length, part, part_length + 1);
#if defined(__linux__)
        if (mkdirat(parent.fd, part, 0700) && errno != EEXIST) { status = -errno; break; }
        int child = openat(parent.fd, part, O_RDONLY | O_DIRECTORY | O_NOFOLLOW | O_CLOEXEC);
        if (child < 0) { status = -errno; break; }
        close(parent.fd); parent.fd = child;
        /* A concurrent mount/symlink substitution cannot redirect the next mkdir. */
        struct stat child_stat;
        RtSdrRootV1 observed; memset(&observed, 0, sizeof(observed)); observed.fd = child;
        if (fstat(child, &child_stat)) { status = -EIO; break; }
        observed.identity[0] = (uint64_t)child_stat.st_dev;
        observed.identity[1] = (uint64_t)child_stat.st_ino;
        status = rt_sdr_mount_location_v1(&observed);
        char expected[RT_SDR_PATH_V1];
        int count = snprintf(expected, sizeof(expected), "%s%s", prospective.physical,
            "");
        size_t keep = strlen(prospective.physical) - (strlen(target) - strlen(walk));
        if (count < 0 || count >= RT_SDR_PATH_V1 || keep >= sizeof(expected)) { status = -EIO; break; }
        expected[keep] = 0;
        if (status || observed.identity[0] != prospective.identity[0] || strcmp(observed.physical, expected)) {
            status = RT_SDR_CHANGED_V1; break;
        }
#else
        wchar_t wide[RT_SDR_PATH_V1];
        if (!MultiByteToWideChar(CP_UTF8, MB_ERR_INVALID_CHARS, walk, -1, wide, RT_SDR_PATH_V1)) {
            status = -EINVAL; break;
        }
        if (!CreateDirectoryW(wide, NULL) && GetLastError() != ERROR_ALREADY_EXISTS) {
            status = -EACCES; break;
        }
        RtSdrRootV1 child;
        status = rt_sdr_root_open_v1(walk, &child);
        if (status) break;
        if (!rt_sdr_physical_contains_v1(child.physical, prospective.physical)) {
            rt_sdr_root_close_v1(&child); status = RT_SDR_CHANGED_V1; break;
        }
        rt_sdr_root_close_v1(&parent); parent = child;
#endif
        part = slash ? slash + 1 : NULL;
    }
    rt_sdr_root_close_v1(&parent); return status;
#else
    (void)shared; (void)requested; return -ENOTSUP;
#endif
}

static RtSdrPairV1 *rt_sdr_find_v1(int64_t token) {
    if (token <= 0) return NULL;
    for (size_t i = 0; i < RT_SDR_SLOTS_V1; ++i)
        if (rt_sdr_pairs_v1[i].token == token) return &rt_sdr_pairs_v1[i];
    return NULL;
}
static int64_t rt_sdr_open_v1(const char *shared, const char *private_root) {
    RtSdrRootV1 a, b;
    int status = rt_sdr_root_open_v1(shared, &a);
    if (status) return status;
    status = rt_sdr_root_open_v1(private_root, &b);
    if (status == -ENOENT) {
        status = rt_sdr_create_private_v1(&a, private_root);
        if (!status) status = rt_sdr_root_open_v1(private_root, &b);
    }
    if (status) { rt_sdr_root_close_v1(&a); return status; }
    if (rt_sdr_overlap_v1(&a, &b)) {
        rt_sdr_root_close_v1(&a); rt_sdr_root_close_v1(&b); return RT_SDR_OVERLAP_V1;
    }
    int64_t result = -EMFILE;
    RT_SDR_LOCK();
    if (rt_sdr_next_v1 > 0 && rt_sdr_next_v1 < INT64_MAX) {
        for (size_t i = 0; i < RT_SDR_SLOTS_V1; ++i) {
            if (!rt_sdr_pairs_v1[i].token) {
                result = rt_sdr_next_v1++;
                rt_sdr_pairs_v1[i].shared = a; rt_sdr_pairs_v1[i].private_root = b;
                rt_sdr_pairs_v1[i].token = result; break;
            }
        }
    }
    RT_SDR_UNLOCK();
    if (result < 0) { rt_sdr_root_close_v1(&a); rt_sdr_root_close_v1(&b); }
    return result;
}
static int64_t rt_sdr_revalidate_pair_v1(RtSdrPairV1 *pair) {
    int64_t status = -EBADF;
    if (pair) {
        RtSdrRootV1 a, b;
        status = rt_sdr_root_fast_v1(pair->shared.path, &a);
        if (!status) {
            status = rt_sdr_root_fast_v1(pair->private_root.path, &b);
            if (!status) {
                if (!rt_sdr_location_equal_v1(&pair->shared, &a) ||
                    !rt_sdr_location_equal_v1(&pair->private_root, &b)) status = RT_SDR_CHANGED_V1;
                rt_sdr_root_close_v1(&b);
            }
            rt_sdr_root_close_v1(&a);
        }
    }
    return status;
}
static int64_t rt_sdr_revalidate_v1(int64_t token) {
    RT_SDR_LOCK();
    int64_t status = rt_sdr_revalidate_pair_v1(rt_sdr_find_v1(token));
    RT_SDR_UNLOCK(); return status;
}
static int64_t rt_sdr_snapshot_v1(int64_t token, uint64_t *out, int64_t bytes) {
    if (!out || bytes != RT_SDR_WORDS_V1 * (int64_t)sizeof(uint64_t)) return -EINVAL;
    memset(out, 0, (size_t)bytes);
    int64_t status = -EBADF;
    RT_SDR_LOCK();
    RtSdrPairV1 *pair = rt_sdr_find_v1(token);
    if (pair) {
        memcpy(out, pair->shared.identity, 3 * sizeof(uint64_t));
        memcpy(out + 3, pair->private_root.identity, 3 * sizeof(uint64_t));
        out[6] = (uint64_t)token; out[7] = 1; status = 0;
    }
    RT_SDR_UNLOCK(); return status;
}
static int64_t rt_sdr_close_v1(int64_t token) {
    int64_t status = -EBADF;
    RT_SDR_LOCK();
    RtSdrPairV1 *pair = rt_sdr_find_v1(token);
    if (pair) {
        rt_sdr_root_close_v1(&pair->shared); rt_sdr_root_close_v1(&pair->private_root);
        pair->token = 0; status = 0;
    }
    RT_SDR_UNLOCK(); return status;
}

/* Compiler callers use this bounded mutex-owned cache, never mutable Simple
 * global token state. Failed admission/revalidation stays rejected for the
 * same requested roots. Linux checks also resolve mount-root ancestry because
 * moving a bind mount's backing directory preserves its inode and mount ID.
 */
typedef struct RtSdrCacheV1 {
    char shared[RT_SDR_PATH_V1];
    char private_root[RT_SDR_PATH_V1];
    int used;
    int64_t token;
    int64_t status;
} RtSdrCacheV1;
static RtSdrCacheV1 rt_sdr_cache_v1[RT_SDR_SLOTS_V1];
static int64_t rt_sdr_check_v1(const char *shared, const char *private_root) {
    char a_path[RT_SDR_PATH_V1], b_path[RT_SDR_PATH_V1];
    int64_t status = rt_sdr_path_v1(shared, a_path);
    if (!status) status = rt_sdr_path_v1(private_root, b_path);
    if (status) return status;
    RT_SDR_LOCK();
    RtSdrCacheV1 *cache = NULL;
    for (size_t i = 0; i < RT_SDR_SLOTS_V1; ++i) {
        if (rt_sdr_cache_v1[i].used && !strcmp(rt_sdr_cache_v1[i].shared, a_path) &&
            !strcmp(rt_sdr_cache_v1[i].private_root, b_path)) { cache = &rt_sdr_cache_v1[i]; break; }
    }
    if (cache) {
        status = cache->status;
        if (!status) {
            RtSdrPairV1 *pair = rt_sdr_find_v1(cache->token);
            status = rt_sdr_revalidate_pair_v1(pair);
            if (status) {
                if (pair) {
                    rt_sdr_root_close_v1(&pair->shared); rt_sdr_root_close_v1(&pair->private_root);
                    pair->token = 0;
                }
                cache->token = 0; cache->status = status;
            }
        }
        RT_SDR_UNLOCK(); return status;
    }
    RtSdrPairV1 *slot = NULL;
    for (size_t i = 0; i < RT_SDR_SLOTS_V1; ++i) {
        if (!cache && !rt_sdr_cache_v1[i].used) cache = &rt_sdr_cache_v1[i];
        if (!slot && !rt_sdr_pairs_v1[i].token) slot = &rt_sdr_pairs_v1[i];
    }
    if (!cache || !slot || rt_sdr_next_v1 <= 0 || rt_sdr_next_v1 == INT64_MAX) {
        RT_SDR_UNLOCK(); return -EMFILE;
    }
    strcpy(cache->shared, a_path); strcpy(cache->private_root, b_path); cache->used = 1;
    RtSdrRootV1 a, b;
    status = rt_sdr_root_open_v1(a_path, &a);
    if (!status) {
        status = rt_sdr_root_open_v1(b_path, &b);
        if (status == -ENOENT) {
            status = rt_sdr_create_private_v1(&a, b_path);
            if (!status) status = rt_sdr_root_open_v1(b_path, &b);
        }
        if (!status) {
            if (rt_sdr_overlap_v1(&a, &b)) {
                status = RT_SDR_OVERLAP_V1; rt_sdr_root_close_v1(&b);
            } else {
                slot->shared = a; slot->private_root = b; slot->token = rt_sdr_next_v1++;
                cache->token = slot->token;
            }
        }
        if (status) rt_sdr_root_close_v1(&a);
    }
    cache->status = status;
    RT_SDR_UNLOCK(); return status;
}
#endif
