/* Native mechanism for os.installer.hosted_safe_artifact_io_v1. The Simple
 * owner retains policy, grant redemption, and publication receipts. */
#if !defined(SIMPLE_RUNTIME_HOSTED_SAFE_ARTIFACT_OWNER_V1)
#error "instantiate hosted-safe-artifact only from runtime_native.c"
#endif

#include "runtime.h"
#include "runtime_hosted_safe_artifact_v1.h"

#include <limits.h>
#include <stdlib.h>
#include <string.h>

#define RT_HSA_MAX_BYTES INT64_C(16777216)
#define RT_HSA_PATH_BYTES 4096U

#if defined(__linux__) && !defined(SIMPLE_RUNTIME_FREESTANDING_V2) && \
    !defined(SIMPLE_HOSTED_SAFE_ARTIFACT_UNSUPPORTED_V1)
#include <errno.h>
#include <fcntl.h>
#include <linux/openat2.h>
#include <pthread.h>
#include <sys/stat.h>
#include <sys/syscall.h>
#include <unistd.h>

#define RT_HSA_ROOT_SLOTS 32
typedef struct RtHsaRootV1 {
    int64_t token;
    int fd;
    dev_t device;
    ino_t inode;
} RtHsaRootV1;

static RtHsaRootV1 rt_hsa_roots[RT_HSA_ROOT_SLOTS];
static int64_t rt_hsa_next_token = 1;
static pthread_mutex_t rt_hsa_mutex = PTHREAD_MUTEX_INITIALIZER;

/* Fault injection belongs only to the focused native check. Returning a
 * nonzero errno injects one failed operation. Close still consumes the fd. */
#if defined(SIMPLE_HOSTED_SAFE_ARTIFACT_TEST_V1)
extern int rt_hsa_test_fault_v1(const char* operation, int fd);
static int rt_hsa_fault(const char* operation, int fd) {
    int error = rt_hsa_test_fault_v1(operation, fd);
    if (error) errno = error;
    return error;
}
#else
#define rt_hsa_fault(operation, fd) 0
#endif

static int rt_hsa_close(int fd) {
    int result = close(fd);
    /* Never retry close(EINTR): on Linux the fd is already consumed and may
     * have been reused by another thread. A repeated close could close it. */
    if (rt_hsa_fault("close", fd)) return -1;
    return result;
}

static int rt_hsa_stat(int fd, struct stat* value) {
    memset(value, 0, sizeof(*value));
    if (rt_hsa_fault("fstat", fd)) return -1;
    return fstat(fd, value);
}

static int rt_hsa_path(const uint8_t* bytes, uint64_t length, int absolute,
                       char out[RT_HSA_PATH_BYTES]) {
    if (!bytes || length == 0 || length >= RT_HSA_PATH_BYTES ||
        memchr(bytes, 0, (size_t)length)) return 0;
    if (absolute ? bytes[0] != '/' : (bytes[0] == '/' || bytes[0] == '\\')) return 0;
    if (absolute && length == 1) { strcpy(out, "/"); return 1; }
    size_t start = absolute ? 1U : 0U;
    for (size_t end = start; end <= (size_t)length; ++end) {
        if (end != length && bytes[end] != '/') continue;
        size_t count = end - start;
        if (count == 0 || count > 255 || (count == 1 && bytes[start] == '.') ||
            (count == 2 && bytes[start] == '.' && bytes[start + 1] == '.')) return 0;
        start = end + 1;
    }
    memcpy(out, bytes, (size_t)length);
    out[length] = 0;
    return 1;
}

static int rt_hsa_openat(int parent, const char* path, int flags, mode_t mode) {
    int result;
    unsigned int attempts = 0;
    do {
        result = rt_hsa_fault("openat", parent) ? -1 : openat(parent, path, flags, mode);
    } while (result < 0 && errno == EINTR && ++attempts < 32);
    return result;
}

static int rt_hsa_beneath(int root, const char* path, int flags) {
#if defined(SYS_openat2)
    const struct open_how how = {
        .flags = (uint64_t)(flags | O_CLOEXEC | O_NOFOLLOW),
        .mode = 0,
        .resolve = RESOLVE_BENEATH | RESOLVE_NO_XDEV |
                   RESOLVE_NO_SYMLINKS | RESOLVE_NO_MAGICLINKS
    };
    int result;
    unsigned int attempts = 0;
    do {
        result = rt_hsa_fault("openat2", root) ? -1 :
            (int)syscall(SYS_openat2, root, path, &how, sizeof(how));
    } while (result < 0 && errno == EINTR && ++attempts < 32);
    return result;
#else
    (void)root; (void)path; (void)flags;
    errno = ENOSYS;
    return -1;
#endif
}

static RtHsaRootV1* rt_hsa_root(int64_t token) {
    if (token <= 0) return NULL;
    for (int i = 0; i < RT_HSA_ROOT_SLOTS; ++i) {
        RtHsaRootV1* root = &rt_hsa_roots[i];
        if (root->token != token) continue;
        struct stat identity;
        if (rt_hsa_stat(root->fd, &identity) != 0 || !S_ISDIR(identity.st_mode) ||
            root->device != identity.st_dev || root->inode != identity.st_ino) return NULL;
        return root;
    }
    return NULL;
}

static int rt_hsa_open_root(char* path) {
    int current = rt_hsa_openat(AT_FDCWD, "/", O_RDONLY | O_DIRECTORY | O_CLOEXEC | O_NOFOLLOW, 0);
    if (current < 0) return -1;
    for (char* component = path + 1; *component;) {
        char* slash = strchr(component, '/');
        if (slash) *slash = 0;
        int next = rt_hsa_openat(current, component, O_RDONLY | O_DIRECTORY | O_CLOEXEC | O_NOFOLLOW, 0);
        int closed = rt_hsa_close(current);
        if (next < 0 || closed != 0) {
            if (next >= 0) (void)rt_hsa_close(next);
            return -1;
        }
        current = next;
        if (!slash) break;
        component = slash + 1;
    }
    return current;
}

int64_t rt_hosted_safe_artifact_root_open_v1(const uint8_t* bytes, uint64_t length) {
    char path[RT_HSA_PATH_BYTES];
    if (!rt_hsa_path(bytes, length, 1, path)) return -1;
    if (pthread_mutex_lock(&rt_hsa_mutex) != 0) return -1;
    int64_t token = -1;
    for (int i = 0; rt_hsa_next_token > 0 && i < RT_HSA_ROOT_SLOTS; ++i) {
        if (rt_hsa_roots[i].token != 0) continue;
        int fd = rt_hsa_open_root(path);
        struct stat identity;
        if (fd < 0) break;
        if (rt_hsa_stat(fd, &identity) != 0 || !S_ISDIR(identity.st_mode)) {
            (void)rt_hsa_close(fd);
            break;
        }
        token = rt_hsa_next_token;
        rt_hsa_next_token = token == INT64_MAX ? 0 : token + 1;
        rt_hsa_roots[i] = (RtHsaRootV1){token, fd, identity.st_dev, identity.st_ino};
        break;
    }
    (void)pthread_mutex_unlock(&rt_hsa_mutex);
    return token;
}

bool rt_hosted_safe_artifact_root_close_v1(int64_t token) {
    if (token <= 0 || pthread_mutex_lock(&rt_hsa_mutex) != 0) return false;
    int closed = 0;
    for (int i = 0; i < RT_HSA_ROOT_SLOTS; ++i) {
        if (rt_hsa_roots[i].token != token) continue;
        int fd = rt_hsa_roots[i].fd;
        memset(&rt_hsa_roots[i], 0, sizeof(rt_hsa_roots[i]));
        closed = rt_hsa_close(fd) == 0;
        break;
    }
    (void)pthread_mutex_unlock(&rt_hsa_mutex);
    return closed != 0;
}

static int rt_hsa_same_stat(const struct stat* a, const struct stat* b) {
    return a->st_dev == b->st_dev && a->st_ino == b->st_ino &&
        a->st_mode == b->st_mode && a->st_size == b->st_size &&
        a->st_mtim.tv_sec == b->st_mtim.tv_sec && a->st_mtim.tv_nsec == b->st_mtim.tv_nsec &&
        a->st_ctim.tv_sec == b->st_ctim.tv_sec && a->st_ctim.tv_nsec == b->st_ctim.tv_nsec;
}

int64_t rt_hosted_safe_artifact_read_v1(int64_t token, const uint8_t* path_bytes,
                                      uint64_t length, int64_t max_bytes) {
    char path[RT_HSA_PATH_BYTES];
    if (max_bytes < 0 || max_bytes > RT_HSA_MAX_BYTES ||
        !rt_hsa_path(path_bytes, length, 0, path)) return 0;
    if (pthread_mutex_lock(&rt_hsa_mutex) != 0) return 0;
    RtHsaRootV1* root = rt_hsa_root(token);
    /* O_NONBLOCK prevents a FIFO replacement from hanging before fstat can
     * reject it. Regular files ignore this flag. */
    int fd = root ? rt_hsa_beneath(root->fd, path, O_RDONLY | O_NONBLOCK) : -1;
    struct stat before, after;
    uint8_t* bytes = NULL;
    size_t wanted = 0;
    int ok = fd >= 0 && rt_hsa_stat(fd, &before) == 0;
    if (ok) ok = S_ISREG(before.st_mode) && before.st_dev == root->device &&
                 before.st_size >= 0 && before.st_size <= max_bytes;
    if (ok) {
        wanted = (size_t)before.st_size;
        bytes = (uint8_t*)calloc(wanted ? wanted : 1, 1);
        ok = bytes != NULL;
    }
    size_t used = 0;
    unsigned int attempts = 0;
    while (ok && used < wanted) {
        ssize_t count = rt_hsa_fault("read", fd) ? -1 : read(fd, bytes + used, wanted - used);
        if (count > 0) { used += (size_t)count; attempts = 0; continue; }
        if (count < 0 && errno == EINTR && ++attempts < 32) continue;
        ok = 0;
    }
    if (ok) ok = rt_hsa_stat(fd, &after) == 0 && rt_hsa_same_stat(&before, &after);
    if (fd >= 0 && rt_hsa_close(fd) != 0) ok = 0;
    int64_t result = 0;
    if (ok) {
        SplArray* array = rt_byte_array_new_len(wanted);
        if (array) {
            result = (int64_t)(uintptr_t)array;
            if (rt_array_bytes_store_checked(result, bytes, (int64_t)wanted) != (int64_t)wanted) {
                rt_array_free(array);
                result = 0;
            }
        }
    }
    if (bytes) { memset(bytes, 0, wanted); free(bytes); }
    (void)pthread_mutex_unlock(&rt_hsa_mutex);
    return result;
}

static int rt_hsa_sync(int fd, int data_only) {
    unsigned int attempts = 0;
    int result;
    do {
        result = rt_hsa_fault(data_only ? "fdatasync" : "fsync", fd) ? -1 :
            (data_only ? fdatasync(fd) : fsync(fd));
    } while (result < 0 && errno == EINTR && ++attempts < 32);
    return result;
}

static int64_t rt_hsa_publish(RtHsaRootV1* root, char* path,
                              const uint8_t* bytes, size_t length) {
    char* leaf = strrchr(path, '/');
    const char* parent_path = ".";
    if (leaf) { *leaf++ = 0; parent_path = path; } else leaf = path;
    int parent = rt_hsa_beneath(root->fd, parent_path, O_RDONLY | O_DIRECTORY);
    if (parent < 0) return errno == ENOSYS ? -3 : -1;
    int fd = -1;
    int published = 0;
    int64_t status = -1;
    struct stat identity;
    if (rt_hsa_stat(parent, &identity) != 0 || !S_ISDIR(identity.st_mode) ||
        identity.st_dev != root->device) goto cleanup;
    fd = rt_hsa_openat(parent, ".", O_TMPFILE | O_WRONLY | O_CLOEXEC, 0600);
    if (fd < 0) { status = -3; goto cleanup; }
    size_t used = 0;
    unsigned int attempts = 0;
    while (used < length) {
        ssize_t count = rt_hsa_fault("write", fd) ? -1 : write(fd, bytes + used, length - used);
        if (count > 0) { used += (size_t)count; attempts = 0; continue; }
        if (count < 0 && errno == EINTR && ++attempts < 32) continue;
        goto cleanup;
    }
    if (rt_hsa_sync(fd, 1) != 0 || rt_hsa_sync(fd, 0) != 0 ||
        rt_hsa_stat(fd, &identity) != 0 || !S_ISREG(identity.st_mode) ||
        identity.st_dev != root->device || identity.st_size != (off_t)length) goto cleanup;
    /* Link the unnamed inode directly, never through a guessed temporary
     * pathname or /proc/self/fd. linkat cannot replace any existing leaf. */
    if ((rt_hsa_fault("linkat", fd) ? -1 : linkat(fd, "", parent, leaf, AT_EMPTY_PATH)) == 0) {
        published = 1;
        status = rt_hsa_sync(parent, 0) == 0 ? 0 : -4;
    } else if (errno == EEXIST) status = -2;
cleanup:
    if (fd >= 0 && rt_hsa_close(fd) != 0) status = published ? -4 : -5;
    if (rt_hsa_close(parent) != 0) status = published ? -4 : -5;
    return status;
}

int64_t rt_hosted_safe_artifact_publish_v1(int64_t token, const uint8_t* path_bytes,
                                         uint64_t path_length, int64_t payload,
                                         int64_t max_bytes) {
    char path[RT_HSA_PATH_BYTES];
    if (max_bytes < 0 || max_bytes > RT_HSA_MAX_BYTES ||
        !rt_hsa_path(path_bytes, path_length, 0, path)) return -1;
    int64_t length = rt_array_bytes_validate(payload);
    if (length < 0 || length > max_bytes) return -1;
    uint8_t* bytes = (uint8_t*)malloc(length ? (size_t)length : 1);
    if (!bytes) return -1;
    int64_t status = -1;
    if (rt_array_bytes_copy_checked(payload, bytes, length) == length &&
        pthread_mutex_lock(&rt_hsa_mutex) == 0) {
        RtHsaRootV1* root = rt_hsa_root(token);
        if (root) status = rt_hsa_publish(root, path, bytes, (size_t)length);
        (void)pthread_mutex_unlock(&rt_hsa_mutex);
    }
    memset(bytes, 0, (size_t)length);
    free(bytes);
    return status;
}
#else
int64_t rt_hosted_safe_artifact_root_open_v1(const uint8_t* root, uint64_t length) {
    (void)root; (void)length;
    return -1;
}
bool rt_hosted_safe_artifact_root_close_v1(int64_t handle) {
    (void)handle;
    return false;
}
int64_t rt_hosted_safe_artifact_read_v1(int64_t handle, const uint8_t* path,
                                      uint64_t length, int64_t max_bytes) {
    (void)handle; (void)path; (void)length; (void)max_bytes;
    return 0;
}
int64_t rt_hosted_safe_artifact_publish_v1(int64_t handle, const uint8_t* path,
                                         uint64_t length, int64_t payload,
                                         int64_t max_bytes) {
    (void)handle; (void)path; (void)length; (void)payload; (void)max_bytes;
    return -3;
}
#endif
