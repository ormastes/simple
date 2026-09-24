/* Included by the retained-root owner. This is the physical single-bundle
 * transaction; policy/receipt construction remains in Simple. */
#if !defined(SIMPLE_RUNTIME_HOSTED_SAFE_ARTIFACT_OWNER_V1)
/* Standalone syntax gate: runtime_native.c instantiates this file with the
 * shared retained-root owner macro, not a bundle-only one, so self-
 * instantiate that same macro here. The live bundle body uses rt_hsa_*
 * helpers and root state that exist only inside the owner TU, so a
 * standalone check compiles the explicit-unsupported stub branch below
 * instead of duplicating that state. SIMPLE_HOSTED_SAFE_ARTIFACT_
 * UNSUPPORTED_V1 is never defined by the real owner, so the
 * include-from-runtime_native.c path is unchanged. */
#define SIMPLE_RUNTIME_HOSTED_SAFE_ARTIFACT_OWNER_V1 1
#define RT_HSA_BUNDLE_STANDALONE_SYNTAX_SELF_INSTANTIATE 1
#define SIMPLE_HOSTED_SAFE_ARTIFACT_UNSUPPORTED_V1 1
#include "runtime.h"
#include "runtime_hosted_safe_artifact_v1.h"
#endif

#if defined(__linux__) && !defined(SIMPLE_RUNTIME_FREESTANDING_V2) && \
    !defined(SIMPLE_HOSTED_SAFE_ARTIFACT_UNSUPPORTED_V1)
#include <stdio.h>
#include <sys/random.h>

#define RT_HSA_BUNDLE_SLOTS 8
#define RT_HSA_BUNDLE_MAX_BYTES INT64_C(1073741824)
typedef struct RtHsaBundleV1 {
    int64_t token, root_token, max_bytes, bytes_read;
    int parent, temp, source, payload, receipt;
    int created, failed, eof_seen, receipt_staged;
    char temp_leaf[64], bundle_leaf[256], payload_leaf[256], receipt_leaf[256];
    struct stat source_identity, temp_identity;
} RtHsaBundleV1;
static RtHsaBundleV1 rt_hsa_bundles[RT_HSA_BUNDLE_SLOTS];
static int64_t rt_hsa_bundle_next_token = 1;

static RtHsaBundleV1* rt_hsa_bundle(int64_t token) {
    if (token <= 0) return NULL;
    for (int i = 0; i < RT_HSA_BUNDLE_SLOTS; ++i)
        if (rt_hsa_bundles[i].token == token) return &rt_hsa_bundles[i];
    return NULL;
}

static int rt_hsa_bundle_leaf(const uint8_t* bytes, uint64_t length, char out[256]) {
    char path[RT_HSA_PATH_BYTES];
    if (length > 255 || !rt_hsa_path(bytes, length, 0, path) ||
        strchr(path, '/') || strchr(path, '\\')) return 0;
    memcpy(out, path, (size_t)length + 1);
    return 1;
}

static int rt_hsa_bundle_close(int* fd) {
    if (*fd < 0) return 1;
    int owned = *fd;
    *fd = -1; /* close(EINTR) consumes the descriptor on this Linux lane. */
    return rt_hsa_close(owned) == 0;
}

static int rt_hsa_bundle_unlink(int parent, const char* leaf, int flags) {
    if (rt_hsa_fault("bundle-unlink", parent)) return 0;
    return unlinkat(parent, leaf, flags) == 0 || errno == ENOENT;
}

static int rt_hsa_bundle_name_matches(RtHsaBundleV1* t) {
    struct stat current;
    return fstatat(t->parent, t->temp_leaf, &current, AT_SYMLINK_NOFOLLOW) == 0 &&
        S_ISDIR(current.st_mode) && current.st_dev == t->temp_identity.st_dev &&
        current.st_ino == t->temp_identity.st_ino;
}

/* Every action is attempted even after an earlier failure. Never claim a
 * rollback if an unlink, synchronization, or descriptor-close fence failed. */
static int rt_hsa_bundle_cleanup(RtHsaBundleV1* t, int published) {
    int ok = rt_hsa_bundle_close(&t->source);
    ok = rt_hsa_bundle_close(&t->payload) && ok;
    ok = rt_hsa_bundle_close(&t->receipt) && ok;
    if (!published && t->temp >= 0) {
        ok = rt_hsa_bundle_unlink(t->temp, t->payload_leaf, 0) && ok;
        ok = rt_hsa_bundle_unlink(t->temp, t->receipt_leaf, 0) && ok;
        ok = (rt_hsa_sync(t->temp, 0) == 0) && ok;
    }
    if (!published && t->created) {
        /* An actor replacing the staging pathname must not redirect cleanup
         * onto an unrelated directory. A mismatch is explicit quarantine. */
        if (rt_hsa_bundle_name_matches(t))
            ok = rt_hsa_bundle_unlink(t->parent, t->temp_leaf, AT_REMOVEDIR) && ok;
        else ok = 0;
        ok = (rt_hsa_sync(t->parent, 0) == 0) && ok;
    }
    ok = rt_hsa_bundle_close(&t->temp) && ok;
    ok = rt_hsa_bundle_close(&t->parent) && ok;
    for (int i = 0; i < RT_HSA_ROOT_SLOTS; ++i)
        if (rt_hsa_roots[i].token == t->root_token && rt_hsa_roots[i].bundles)
            --rt_hsa_roots[i].bundles;
    memset(t, 0, sizeof(*t));
    return ok;
}

static int rt_hsa_bundle_write(int fd, const uint8_t* bytes, size_t length) {
    size_t used = 0;
    unsigned int attempts = 0;
    while (used < length) {
        ssize_t count = rt_hsa_fault("bundle-write", fd) ? -1 :
            write(fd, bytes + used, length - used);
        if (count > 0) { used += (size_t)count; attempts = 0; continue; }
        if (count < 0 && errno == EINTR && ++attempts < 32) continue;
        return 0;
    }
    return 1;
}

static int rt_hsa_bundle_same_source(RtHsaBundleV1* t) {
    struct stat current;
    return rt_hsa_stat(t->source, &current) == 0 &&
        rt_hsa_same_stat(&t->source_identity, &current);
}

int64_t rt_hosted_safe_artifact_bundle_begin_v1(int64_t root_token,
    const uint8_t* source, uint64_t source_len, const uint8_t* bundle, uint64_t bundle_len,
    const uint8_t* payload, uint64_t payload_len, const uint8_t* scr1, uint64_t scr1_len,
    int64_t max_bytes) {
    char source_path[RT_HSA_PATH_BYTES], bundle_path[RT_HSA_PATH_BYTES];
    char payload_leaf[256], receipt_leaf[256];
    if (max_bytes <= 0 || max_bytes > RT_HSA_BUNDLE_MAX_BYTES ||
        !rt_hsa_path(source, source_len, 0, source_path) ||
        !rt_hsa_path(bundle, bundle_len, 0, bundle_path) ||
        !rt_hsa_bundle_leaf(payload, payload_len, payload_leaf) ||
        !rt_hsa_bundle_leaf(scr1, scr1_len, receipt_leaf) ||
        strcmp(payload_leaf, receipt_leaf) == 0) return -1;
    if (pthread_mutex_lock(&rt_hsa_mutex) != 0) return -1;
    RtHsaRootV1* root = rt_hsa_root(root_token);
    RtHsaBundleV1* t = NULL;
    int64_t result = -1;
    for (int i = 0; root && rt_hsa_bundle_next_token > 0 && i < RT_HSA_BUNDLE_SLOTS; ++i)
        if (!rt_hsa_bundles[i].token) { t = &rt_hsa_bundles[i]; break; }
    if (!t) goto done;
    memset(t, 0, sizeof(*t));
    t->source = t->payload = t->receipt = t->parent = t->temp = -1;
    t->root_token = root_token;
    ++root->bundles;
    t->max_bytes = max_bytes;
    strcpy(t->payload_leaf, payload_leaf);
    strcpy(t->receipt_leaf, receipt_leaf);
    char* leaf = strrchr(bundle_path, '/');
    const char* parent_path = ".";
    if (leaf) { *leaf++ = 0; parent_path = bundle_path; } else leaf = bundle_path;
    if (!rt_hsa_bundle_leaf((const uint8_t*)leaf, strlen(leaf), t->bundle_leaf)) goto fail;
    t->parent = rt_hsa_beneath(root->fd, parent_path, O_RDONLY | O_DIRECTORY);
    if (t->parent < 0) goto fail;
    struct stat existing;
    /* Named directory publication requires an owner-controlled parent:
     * child mode 0700 alone does not prevent parent writers swapping its
     * name. Group/other writers (including an effective POSIX ACL mask)
     * are rejected. Same-uid native actors remain inside the trust boundary. */
    if (rt_hsa_stat(t->parent, &existing) != 0 || !S_ISDIR(existing.st_mode) ||
        existing.st_uid != geteuid() || (existing.st_mode & 0022) != 0 ||
        existing.st_dev != root->device) goto fail;
    if (fstatat(t->parent, t->bundle_leaf, &existing, AT_SYMLINK_NOFOLLOW) == 0 || errno != ENOENT) goto fail;
    t->source = rt_hsa_beneath(root->fd, source_path, O_RDONLY | O_NONBLOCK);
    if (t->source < 0 || rt_hsa_stat(t->source, &t->source_identity) != 0 ||
        !S_ISREG(t->source_identity.st_mode) || t->source_identity.st_dev != root->device ||
        t->source_identity.st_size < 0 || t->source_identity.st_size > max_bytes) goto fail;
    for (unsigned int attempt = 0; attempt < 16; ++attempt) {
        uint64_t random[2];
        if (getrandom(random, sizeof(random), 0) != sizeof(random)) goto fail;
        (void)snprintf(t->temp_leaf, sizeof(t->temp_leaf), ".simple-bundle-%016llx%016llx",
            (unsigned long long)random[0], (unsigned long long)random[1]);
        if (mkdirat(t->parent, t->temp_leaf, 0700) == 0) { t->created = 1; break; }
        if (errno != EEXIST) goto fail;
    }
    if (!t->created) goto fail;
    /* Capture the created name before opening. Cleanup remains fail-closed
     * if no descriptor/identity can be established. */
    if (fstatat(t->parent, t->temp_leaf, &t->temp_identity, AT_SYMLINK_NOFOLLOW) != 0) goto fail;
    t->temp = rt_hsa_openat(t->parent, t->temp_leaf, O_RDONLY | O_DIRECTORY | O_CLOEXEC | O_NOFOLLOW, 0);
    struct stat opened;
    if (t->temp < 0 || rt_hsa_stat(t->temp, &opened) != 0 ||
        opened.st_dev != t->temp_identity.st_dev || opened.st_ino != t->temp_identity.st_ino ||
        !S_ISDIR(opened.st_mode) || opened.st_dev != root->device ||
        opened.st_uid != geteuid() || (opened.st_mode & 0077) != 0) goto fail;
    t->payload = rt_hsa_openat(t->temp, t->payload_leaf,
        O_WRONLY | O_CREAT | O_EXCL | O_CLOEXEC | O_NOFOLLOW, 0600);
    if (t->payload < 0) goto fail;
    t->token = rt_hsa_bundle_next_token;
    rt_hsa_bundle_next_token = t->token == INT64_MAX ? 0 : t->token + 1;
    result = t->token;
    goto done;
fail:
    if (!rt_hsa_bundle_cleanup(t, 0)) result = -3;
done:
    (void)pthread_mutex_unlock(&rt_hsa_mutex);
    return result;
}

int64_t rt_hosted_safe_artifact_bundle_read_stage_v1(int64_t token, int64_t max_bytes) {
    if (pthread_mutex_lock(&rt_hsa_mutex) != 0) return rt_value_nil();
    RtHsaBundleV1* t = rt_hsa_bundle(token);
    int64_t result = rt_value_nil();
    uint8_t* bytes = NULL;
    SplArray* array = NULL;
    if (!t) goto done;
    if (t->failed || t->eof_seen || max_bytes <= 0 || max_bytes > RT_HSA_MAX_BYTES ||
        !rt_hsa_root(t->root_token) || !rt_hsa_bundle_same_source(t)) goto fail;
    int64_t remaining = t->source_identity.st_size - t->bytes_read;
    size_t wanted = (size_t)(remaining < max_bytes ? remaining : max_bytes);
    /* At the exact source bound, a real one-byte read distinguishes EOF
     * from an oversized file. Never manufacture an empty successful read. */
    bytes = rt_hsa_fault("bundle-read-allocation", t->source) ? NULL : malloc(wanted ? wanted : 1);
    if (!bytes) goto fail;
    size_t used = 0;
    unsigned int attempts = 0;
    do {
        ssize_t count = rt_hsa_fault("bundle-read", t->source) ? -1 :
            read(t->source, bytes + used, wanted ? wanted - used : 1);
        if (count > 0) {
            if (!wanted) goto fail;
            used += (size_t)count;
            attempts = 0;
        } else if (count < 0 && errno == EINTR && ++attempts < 32) continue;
        else if (count == 0 && !wanted) break;
        else goto fail;
    } while (used < wanted);
    if (!rt_hsa_bundle_same_source(t)) goto fail;
    array = rt_hsa_fault("bundle-array-allocation", -1) ? NULL : rt_byte_array_new_len(wanted);
    if (!array || rt_array_bytes_store_checked((int64_t)(uintptr_t)array, bytes, (int64_t)wanted) != (int64_t)wanted ||
        !rt_hsa_bundle_write(t->payload, bytes, wanted)) goto fail;
    t->bytes_read += (int64_t)wanted;
    t->eof_seen = wanted == 0;
    result = (int64_t)(uintptr_t)array;
    array = NULL;
    goto done;
fail:
    t->failed = 1;
done:
    if (array) rt_array_free(array);
    free(bytes);
    (void)pthread_mutex_unlock(&rt_hsa_mutex);
    return result;
}

int64_t rt_hosted_safe_artifact_bundle_identity_v1(int64_t token, int64_t field) {
    if (pthread_mutex_lock(&rt_hsa_mutex) != 0) return -1;
    RtHsaBundleV1* t = rt_hsa_bundle(token);
    int64_t value = -1;
    if (t && !t->failed && rt_hsa_root(t->root_token) && rt_hsa_bundle_same_source(t)) {
        switch (field) {
            case 0: value = (int64_t)t->source_identity.st_dev; break;
            case 1: value = (int64_t)t->source_identity.st_ino; break;
            case 2: value = (int64_t)t->source_identity.st_size; break;
            case 3: value = (int64_t)t->source_identity.st_mtim.tv_sec; break;
            case 4: value = (int64_t)t->source_identity.st_mtim.tv_nsec; break;
            case 5: value = t->bytes_read; break;
        }
    }
    (void)pthread_mutex_unlock(&rt_hsa_mutex);
    return value;
}

int64_t rt_hosted_safe_artifact_bundle_stage_scr1_v1(int64_t token, int64_t payload, int64_t max_bytes) {
    if (pthread_mutex_lock(&rt_hsa_mutex) != 0) return 0;
    RtHsaBundleV1* t = rt_hsa_bundle(token);
    int64_t result = 0;
    uint8_t* bytes = NULL;
    if (!t) goto done;
    int64_t length = rt_array_bytes_validate(payload);
    if (t->failed || !t->eof_seen || t->receipt_staged || max_bytes < 0 ||
        max_bytes > RT_HSA_MAX_BYTES || length < 0 || length > max_bytes ||
        length > t->max_bytes - t->bytes_read || !rt_hsa_root(t->root_token)) goto fail;
    bytes = rt_hsa_fault("bundle-receipt-allocation", -1) ? NULL : malloc(length ? (size_t)length : 1);
    if (!bytes || rt_array_bytes_copy_checked(payload, bytes, length) != length) goto fail;
    t->receipt = rt_hsa_openat(t->temp, t->receipt_leaf,
        O_WRONLY | O_CREAT | O_EXCL | O_CLOEXEC | O_NOFOLLOW, 0600);
    if (t->receipt < 0 || !rt_hsa_bundle_write(t->receipt, bytes, (size_t)length)) goto fail;
    t->receipt_staged = 1;
    result = 1;
    goto done;
fail:
    t->failed = 1;
done:
    free(bytes);
    (void)pthread_mutex_unlock(&rt_hsa_mutex);
    return result;
}

int64_t rt_hosted_safe_artifact_bundle_finish_v1(int64_t token, bool commit) {
    if (pthread_mutex_lock(&rt_hsa_mutex) != 0) return 0;
    RtHsaBundleV1* t = rt_hsa_bundle(token);
    int64_t result = 0;
    if (!t) goto done;
    if (!commit) { result = rt_hsa_bundle_cleanup(t, 0) ? 1 : -3; goto done; }
    if (t->failed || !t->eof_seen || !t->receipt_staged ||
        t->bytes_read != t->source_identity.st_size || !rt_hsa_root(t->root_token) ||
        !rt_hsa_bundle_same_source(t) || rt_hsa_sync(t->payload, 0) != 0 ||
        rt_hsa_sync(t->receipt, 0) != 0 || rt_hsa_sync(t->temp, 0) != 0) goto reject;
    /* Pre-publication file close errors prevent publication. The retained
     * staging directory remains available for cleanup. */
    if (!rt_hsa_bundle_close(&t->source) || !rt_hsa_bundle_close(&t->payload) ||
        !rt_hsa_bundle_close(&t->receipt) || !rt_hsa_bundle_name_matches(t)) goto reject;
#if defined(SYS_renameat2)
    if (rt_hsa_fault("bundle-rename", t->parent) ||
        syscall(SYS_renameat2, t->parent, t->temp_leaf,
            t->parent, t->bundle_leaf, RENAME_NOREPLACE) != 0) goto reject;
    result = rt_hsa_sync(t->parent, 0) == 0 ? 1 : -2;
    if (!rt_hsa_bundle_cleanup(t, 1)) result = -2;
    goto done;
#endif
reject:
    result = rt_hsa_bundle_cleanup(t, 0) ? -1 : -3;
done:
    (void)pthread_mutex_unlock(&rt_hsa_mutex);
    return result;
}
#else
int64_t rt_hosted_safe_artifact_bundle_begin_v1(int64_t root,
    const uint8_t* source, uint64_t source_len, const uint8_t* bundle, uint64_t bundle_len,
    const uint8_t* payload, uint64_t payload_len, const uint8_t* scr1, uint64_t scr1_len, int64_t max_bytes) {
    (void)root; (void)source; (void)source_len; (void)bundle; (void)bundle_len;
    (void)payload; (void)payload_len; (void)scr1; (void)scr1_len; (void)max_bytes;
    return RT_HSA_BUNDLE_UNSUPPORTED_V1;
}
int64_t rt_hosted_safe_artifact_bundle_read_stage_v1(int64_t token, int64_t max_bytes) {
    (void)token; (void)max_bytes; return rt_value_nil();
}
int64_t rt_hosted_safe_artifact_bundle_identity_v1(int64_t token, int64_t field) {
    (void)token; (void)field; return -1;
}
int64_t rt_hosted_safe_artifact_bundle_stage_scr1_v1(int64_t token, int64_t payload, int64_t max_bytes) {
    (void)token; (void)payload; (void)max_bytes; return RT_HSA_BUNDLE_UNSUPPORTED_V1;
}
int64_t rt_hosted_safe_artifact_bundle_finish_v1(int64_t token, bool commit) {
    (void)token; (void)commit; return RT_HSA_BUNDLE_UNSUPPORTED_V1;
}
#endif

#include "runtime_hosted_safe_artifact_bundle_unsupported_v1.c"
