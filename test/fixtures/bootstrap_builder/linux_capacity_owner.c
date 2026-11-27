/* Native adapter integration probe: real cgroup2, clone3 and sealed exec.
 * Build: cc -D_GNU_SOURCE -I src/runtime THIS_FILE -lcrypto -o PROBE
 * Run: PROBE /absolute/private/evidence-directory
 * Requires a cgroup2 mount whose root already delegates memory. */
#include "runtime.h"
#include <assert.h>
#include <errno.h>
#include <fcntl.h>
#include <stdint.h>
#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <sys/syscall.h>
#include <openssl/sha.h>

static void owned_sha256(const uint8_t *data, size_t len, uint8_t out[32]) {
    SHA256(data, len, out);
}
static char **owned_adapter_copy_argv(const char *command, uint64_t length,
        SplArray *args, int64_t *argc, int *error) {
    (void)args;
    char **value = calloc(2, sizeof(char*));
    assert(value);
    value[0] = strndup(command, (size_t)length);
    assert(value[0]); *argc = 0; *error = 0; return value;
}
static void owned_adapter_free_argv(char **value, int64_t argc) {
    (void)argc;
    if (value) { free(value[0]); free(value); }
}
static SplArray *owned_adapter_values(const int64_t *values, int64_t count) {
    SplArray *result = calloc(1, sizeof(*result));
    assert(result);
    result->items = calloc((size_t)count, sizeof(*result->items));
    assert(result->items); result->cap = result->len = count;
    for (int64_t i = 0; i < count; i++) result->items[i].as_int = values[i];
    return result;
}
int64_t rt_array_len(SplArray *array) { return array ? array->len : -1; }
int64_t rt_array_get(SplArray *array, int64_t index) {
    return array && index >= 0 && index < array->len ? array->items[index].as_int : 0;
}
int64_t rt_string_len(int64_t value) { (void)value; return -1; }
const uint8_t *rt_string_data(int64_t value) { (void)value; return NULL; }

static int fail_delegation, fail_rollback, fail_parent_open, fail_readonly_mkdir;
static int probe_openat(int fd, const char *name, int flags, ...) {
    if (fail_parent_open && strncmp(name, "simple-parent-", 14) == 0 &&
        (flags & O_DIRECTORY)) {
        fail_parent_open = 0; errno = EACCES; return -1;
    }
    mode_t mode = 0;
    if (flags & O_CREAT) {
        va_list args; va_start(args, flags); mode = (mode_t)va_arg(args, int); va_end(args);
        return (int)syscall(SYS_openat, fd, name, flags, mode);
    }
    return (int)syscall(SYS_openat, fd, name, flags);
}
static ssize_t probe_write(int fd, const void *data, size_t size) {
    if (fail_delegation && size == 7 && memcmp(data, "+memory", 7) == 0) {
        fail_delegation = 0; errno = EPERM; return -1;
    }
    return syscall(SYS_write, fd, data, size);
}
static int probe_unlinkat(int fd, const char *name, int flags) {
    if (fail_rollback && flags == AT_REMOVEDIR && strncmp(name, "simple-parent-", 14) == 0) {
        fail_rollback = 0; errno = EBUSY; return -1;
    }
    return (int)syscall(SYS_unlinkat, fd, name, flags);
}
static int probe_mkdirat(int fd, const char *name, mode_t mode) {
    if (fail_readonly_mkdir && strncmp(name, "simple-parent-", 14) == 0) {
        fail_readonly_mkdir = 0; errno = EROFS; return -1;
    }
    return (int)syscall(SYS_mkdirat, fd, name, mode);
}
#define write probe_write
#define unlinkat probe_unlinkat
#define openat probe_openat
#define mkdirat probe_mkdirat
#include "runtime_linux_group_owner_impl.h"
#undef mkdirat
#undef openat
#undef write
#undef unlinkat

static int64_t field(SplArray *array, int i) {
    assert(array && i < array->len); return array->items[i].as_int;
}

static void digest_path(const char *path, char digest[65]) {
    int fd = open(path, O_RDONLY); assert(fd >= 0);
    struct stat status; assert(!fstat(fd, &status));
    void *data = mmap(NULL, (size_t)status.st_size, PROT_READ, MAP_PRIVATE, fd, 0);
    assert(data != MAP_FAILED); uint8_t bytes[32];
    SHA256(data, (size_t)status.st_size, bytes);
    munmap(data, (size_t)status.st_size); close(fd);
    for (int i = 0; i < 32; i++) sprintf(digest + i * 2, "%02x", bytes[i]);
}

static int lifecycle_probe(const char *path) {
    const char *first = "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa";
    const char *second = "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb";
    SplArray *a = rt_linux_group_parent_acquire_v1(path, strlen(path), first, 64);
    assert(field(a, 0) == 0); int64_t first_token = field(a, 1);
    assert(rt_linux_group_parent_release_v1(first_token) == 0);
    SplArray *b = rt_linux_group_parent_acquire_v1(path, strlen(path), second, 64);
    assert(field(b, 0) == 0 && field(b, 1) > first_token);
    assert(rt_linux_group_parent_release_v1(first_token) == EINVAL);
    int retained = rt_lg_delegation_fd(); assert(retained >= 0); close(retained);
    assert(rt_linux_group_parent_release_v1(field(b, 1)) == 0);
    fail_delegation = 1; fail_rollback = 1;
    SplArray *pending = rt_linux_group_parent_acquire_v1(path, strlen(path), first, 64);
    assert(field(pending, 0) == EBUSY && field(pending, 1) > field(b, 1));
    assert(field(pending, 2) >= 0 && field(pending, 3) > 0 && rt_lg_delegation.active);
    retained = rt_lg_delegation_fd(); assert(retained >= 0); close(retained);
    assert(rt_linux_group_parent_release_v1(field(pending, 1)) == 0);
    assert(!rt_lg_delegation.active);
    fail_parent_open = 1; fail_rollback = 1;
    pending = rt_linux_group_parent_acquire_v1(path, strlen(path), second, 64);
    assert(field(pending, 0) == EOWNERDEAD && field(pending, 1) == -1);
    assert(!rt_lg_delegation.active);
    /* The shim could not pin the inode after mkdir, so it must not unlink by
     * name or publish fabricated device/inode ownership. Clean the injected
     * fixture only after proving its expected test name is still present. */
    int cleanup_root = open("/sys/fs/cgroup", O_RDONLY | O_DIRECTORY | O_CLOEXEC);
    assert(cleanup_root >= 0);
    struct stat orphan;
    assert(fstatat(cleanup_root, "simple-parent-bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb",
        &orphan, AT_SYMLINK_NOFOLLOW) == 0 && S_ISDIR(orphan.st_mode));
    assert(syscall(SYS_unlinkat, cleanup_root,
        "simple-parent-bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb",
        AT_REMOVEDIR) == 0);
    close(cleanup_root);
    puts("PASS: nonreused lease rejects stale release; failed acquisition rollback retains exact owner until cleanup");
    return 0;
}

static void assert_v2_rejected(const char *path, const char *attempt, const char *identity) {
    SplArray *receipt = rt_linux_group_parent_acquire_at_v2(path, strlen(path),
        attempt, strlen(attempt), identity, strlen(identity));
    assert(field(receipt, 0) != 0 && field(receipt, 1) == 0);
}

static int has_word(const char *text, const char *word) {
    const char *at = text;
    size_t wanted = strlen(word);
    while (*at) {
        at += strspn(at, " \t\r\n");
        size_t length = strcspn(at, " \t\r\n");
        if (length == wanted && memcmp(at, word, wanted) == 0) return 1;
        at += length;
    }
    return 0;
}

/* This test-only setup writes controllers only in this uniquely named,
 * process-empty transient service parent. DelegateSubgroup keeps the test
 * process in its supervisor child while the service parent is configured. */
static int setup_owned_service_parent(int parent, const char *path,
        const char *expected_service) {
    const char *name = strrchr(path, '/'); name = name ? name + 1 : path;
    size_t name_len = strlen(name);
    if (!expected_service || strcmp(name, expected_service) != 0 ||
        strncmp(name, "simple-linux-parent-v2-", 23) != 0 || name_len < 8 ||
        strcmp(name + name_len - 8, ".service") != 0) return 0;
    char procs[4096], available[4096], enabled[4096];
    if (rt_lg_read_at(parent, "cgroup.procs", procs, sizeof(procs))) {
        if (strspn(procs, " \t\r\n") != strlen(procs)) return 0;
    } else if (errno != ENODATA) return 0;
    if (!rt_lg_read_at(parent, "cgroup.controllers", available, sizeof(available)) ||
        !has_word(available, "memory") || !has_word(available, "pids")) return 0;
    if (rt_lg_read_at(parent, "cgroup.subtree_control", enabled, sizeof(enabled))) {
        if (strspn(enabled, " \t\r\n") != strlen(enabled)) return 0;
    } else if (errno == ENODATA) enabled[0] = 0;
    else return 0;
    printf("V2_DELEGATION_BEFORE=subtree_control_empty; available=%s; parent_procs_empty=true\n",
        available); fflush(stdout);
    if (!rt_lg_write_at(parent, "cgroup.subtree_control", "+memory +pids") ||
        !rt_lg_read_at(parent, "cgroup.subtree_control", enabled, sizeof(enabled)) ||
        !has_word(enabled, "memory") || !has_word(enabled, "pids")) return 0;
    int count = 0;
    const char *at = enabled;
    while (*at) {
        at += strspn(at, " \t\r\n");
        size_t length = strcspn(at, " \t\r\n");
        if (!length) break;
        if (!((length == 6 && memcmp(at, "memory", 6) == 0) ||
              (length == 4 && memcmp(at, "pids", 4) == 0))) return 0;
        count++; at += length;
    }
    if (count != 2) return 0;
    printf("V2_DELEGATION_AFTER=memory,pids; readback=%s; service=%s\n",
        enabled, expected_service); fflush(stdout);
    return 1;
}

/* A failure before a child launch still owns the admitted V2 parent until this
 * exact release and both filesystem/controller readbacks are proven. */
static int release_v2_parent_without_process(int service_parent, int64_t token,
        const char *controls_before) {
    if (!rt_lg_delegation.active || token != rt_lg_delegation.token) return 79;
    char parent_name[sizeof(rt_lg_delegation.name)];
    memcpy(parent_name, rt_lg_delegation.name, sizeof(parent_name));
    parent_name[sizeof(parent_name) - 1] = 0;
    if (rt_linux_group_parent_release_v1(token) != 0) return 79;
    struct stat missing;
    if (fstatat(service_parent, parent_name, &missing, AT_SYMLINK_NOFOLLOW) != -1 || errno != ENOENT)
        return 79;
    char controls_after[4096];
    if (!rt_lg_read_at(service_parent, "cgroup.subtree_control", controls_after,
            sizeof(controls_after)) || strcmp(controls_before, controls_after) != 0) return 79;
    return 0;
}

static int valid_fresh_evidence_dir(const char *path) {
    if (!rt_lg_canonical_path(path) || strcmp(path, "/") == 0) return 0;
    int fd = rt_lg_open_absolute_dir(path);
    if (fd < 0) return 0;
    struct stat status, out_status, err_status;
    int valid = fstat(fd, &status) == 0 && S_ISDIR(status.st_mode) &&
        status.st_uid == geteuid() && (status.st_mode & 0700) == 0700 &&
        (status.st_mode & 0077) == 0 &&
        fstatat(fd, "true.stdout", &out_status, AT_SYMLINK_NOFOLLOW) == -1 && errno == ENOENT &&
        fstatat(fd, "true.stderr", &err_status, AT_SYMLINK_NOFOLLOW) == -1 && errno == ENOENT;
    close(fd); return valid;
}

static int v2_service_probe(const char *expected_service) {
    char mount_path[4096], current_path[4096], delegated_path[4096];
    char parsed_root[4096], parsed_mount[4096], parsed_member[4096];
    const char *valid_mount = "1 0 0:1 / /sys/fs/cgroup rw - cgroup2 cgroup rw\n";
    const char *duplicate_mount =
        "1 0 0:1 / /sys/fs/cgroup rw - cgroup2 cgroup rw\n"
        "2 0 0:1 / /mnt/cgroup rw - cgroup2 cgroup rw\n";
    const char *escaped_mount = "1 0 0:1 / /sys/fs/cgroup\\040x rw - cgroup2 cgroup rw\n";
    const char *valid_then_escaped =
        "1 0 0:1 / /sys/fs/cgroup rw - cgroup2 cgroup rw\n"
        "2 0 0:1 / /sys/fs/cgroup\\040x rw - cgroup2 cgroup rw\n";
    const char *valid_then_truncated =
        "1 0 0:1 / /sys/fs/cgroup rw - cgroup2 cgroup rw\n"
        "2 0 0:1 / /sys/fs/cgroup rw";
    assert(rt_lg_parse_mountinfo(valid_mount, strlen(valid_mount), parsed_root,
        sizeof(parsed_root), parsed_mount, sizeof(parsed_mount)));
    assert(!rt_lg_parse_mountinfo(duplicate_mount, strlen(duplicate_mount), parsed_root,
        sizeof(parsed_root), parsed_mount, sizeof(parsed_mount)));
    assert(!rt_lg_parse_mountinfo(escaped_mount, strlen(escaped_mount), parsed_root,
        sizeof(parsed_root), parsed_mount, sizeof(parsed_mount)));
    assert(!rt_lg_parse_mountinfo(valid_then_escaped, strlen(valid_then_escaped), parsed_root,
        sizeof(parsed_root), parsed_mount, sizeof(parsed_mount)));
    assert(!rt_lg_parse_mountinfo(valid_then_truncated, strlen(valid_then_truncated), parsed_root,
        sizeof(parsed_root), parsed_mount, sizeof(parsed_mount)));
    const char *duplicate_membership = "0::/a\n0::/b\n";
    assert(!rt_lg_parse_membership(duplicate_membership, strlen(duplicate_membership),
        parsed_member, sizeof(parsed_member)));
    assert(rt_lg_current_mapping(mount_path, sizeof(mount_path),
        current_path, sizeof(current_path)));
    size_t current_len = strlen(current_path);
    assert(current_len > 11 && strcmp(current_path + current_len - 11, "/supervisor") == 0);
    memcpy(delegated_path, current_path, current_len - 11);
    delegated_path[current_len - 11] = 0;
    assert(delegated_path[0] == '/' && delegated_path[1] != 0);
    printf("V2_DELEGATED_PATH=%s\n", delegated_path); fflush(stdout);

    const char *attempt = "/tmp/linux-parent-v2-selfcheck";
    const char *identities[] = {
        "1111111111111111111111111111111111111111111111111111111111111111",
        "2222222222222222222222222222222222222222222222222222222222222222",
        "3333333333333333333333333333333333333333333333333333333333333333",
        "4444444444444444444444444444444444444444444444444444444444444444"
    };
    assert_v2_rejected("relative/path", attempt, identities[0]);
    assert_v2_rejected("/sys/fs/cgroup/../cgroup", attempt, identities[0]);
    assert_v2_rejected(mount_path, attempt, identities[0]); /* actual cgroup2 mount root */
    assert_v2_rejected("/tmp", attempt, identities[0]); /* wrong filesystem/ancestor */
    char sibling[4096], symlink_path[4096], temp_dir[] = "/tmp/simple-v2-link-XXXXXX";
    assert(snprintf(sibling, sizeof(sibling), "%s-sibling", delegated_path) < (int)sizeof(sibling));
    assert_v2_rejected(sibling, attempt, identities[0]);
    char missing[4096];
    assert(snprintf(missing, sizeof(missing), "%s/missing", delegated_path) < (int)sizeof(missing));
    assert_v2_rejected(missing, attempt, identities[0]); /* missing path */
    char *created = mkdtemp(temp_dir); assert(created);
    assert(snprintf(symlink_path, sizeof(symlink_path), "%s/linked", created) < (int)sizeof(symlink_path));
    assert(symlink(delegated_path, symlink_path) == 0);
    assert_v2_rejected(symlink_path, attempt, identities[0]);
    assert(unlink(symlink_path) == 0);
    assert(rmdir(created) == 0);

    int parent = rt_lg_open_absolute_dir(delegated_path); assert(parent >= 0);
    char controls_before[4096], controls_after[4096], child_name[80];
    if (!setup_owned_service_parent(parent, delegated_path, expected_service)) {
        printf("UNSUPPORTED: owned service parent could not enable/read back memory+pids (errno=%d)\n", errno);
        close(parent); return 77;
    }
    if (!rt_lg_read_at(parent, "cgroup.subtree_control", controls_before, sizeof(controls_before))) {
        printf("UNSUPPORTED: service parent controller state is unreadable (errno=%d)\n", errno);
        close(parent); return 77;
    }
    snprintf(child_name, sizeof(child_name), "simple-parent-%s", identities[0]);
    struct stat no_offscope_child;
    assert(fstatat(parent, child_name, &no_offscope_child, AT_SYMLINK_NOFOLLOW) == -1 && errno == ENOENT);
    assert(mkdirat(parent, child_name, 0700) == 0);
    SplArray *busy = rt_linux_group_parent_acquire_at_v2(delegated_path,
        strlen(delegated_path), attempt, strlen(attempt), identities[0], 64);
    assert(field(busy, 0) == EEXIST && field(busy, 1) == 0);
    assert(unlinkat(parent, child_name, AT_REMOVEDIR) == 0);
    snprintf(child_name, sizeof(child_name), "simple-parent-%s", identities[0]);
    struct stat rejected_absent;
    assert(fstatat(parent, child_name, &rejected_absent, AT_SYMLINK_NOFOLLOW) == -1 && errno == ENOENT);

    fail_readonly_mkdir = 1;
    SplArray *readonly = rt_linux_group_parent_acquire_at_v2(delegated_path,
        strlen(delegated_path), attempt, strlen(attempt), identities[2], 64);
    assert(field(readonly, 0) == EROFS && field(readonly, 1) == 0);
    snprintf(child_name, sizeof(child_name), "simple-parent-%s", identities[2]);
    struct stat readonly_absent;
    assert(fstatat(parent, child_name, &readonly_absent, AT_SYMLINK_NOFOLLOW) == -1 && errno == ENOENT);

    /* Exercise the shared V1/V2 transaction's failed-open rollback path using
     * only this service's delegated directory, never the host mount root. */
    fail_parent_open = 1; fail_rollback = 1;
    SplArray *unknown = rt_lg_parent_acquire_root(dup(parent), attempt, identities[2]);
    assert(field(unknown, 0) == EOWNERDEAD && field(unknown, 1) == -1);
    assert(field(unknown, 2) == 0 && field(unknown, 3) == 0 && !rt_lg_delegation.active);
    snprintf(child_name, sizeof(child_name), "simple-parent-%s", identities[2]);
    struct stat orphan;
    assert(fstatat(parent, child_name, &orphan, AT_SYMLINK_NOFOLLOW) == 0 && S_ISDIR(orphan.st_mode));
    assert(syscall(SYS_unlinkat, parent, child_name, AT_REMOVEDIR) == 0);
    fail_parent_open = 0; fail_rollback = 0;

    SplArray *acquired = rt_linux_group_parent_acquire_at_v2(delegated_path,
        strlen(delegated_path), attempt, strlen(attempt), identities[3], 64);
    assert(field(acquired, 0) == 0 && field(acquired, 1) > 0 && field(acquired, 3) > 0);
    assert(rt_lg_read_at(parent, "cgroup.subtree_control", controls_after, sizeof(controls_after)));
    assert(strcmp(controls_before, controls_after) == 0);
    assert(rt_linux_group_parent_release_v1(field(acquired, 1)) == 0);
    snprintf(child_name, sizeof(child_name), "simple-parent-%s", identities[3]);
    struct stat absent;
    assert(fstatat(parent, child_name, &absent, AT_SYMLINK_NOFOLLOW) == -1 && errno == ENOENT);
    close(parent);
    puts("PASS: explicit delegated-parent controls and shared-transaction unknown rollback classification");
    return 0;
}

static int v2_process_probe(const char *expected_service, const char *evidence_dir) {
    if (!valid_fresh_evidence_dir(evidence_dir)) {
        printf("PROCESS_SETUP_FAIL: evidence directory is not canonical, private, or fresh\n");
        return 1;
    }
    char mount_path[4096], current_path[4096], delegated_path[4096];
    if (!rt_lg_current_mapping(mount_path, sizeof(mount_path),
            current_path, sizeof(current_path))) {
        printf("PROCESS_SETUP_FAIL: current cgroup mapping unavailable errno=%d\n", errno);
        return 1;
    }
    size_t current_len = strlen(current_path);
    if (current_len <= 11 || strcmp(current_path + current_len - 11, "/supervisor") != 0) {
        printf("PROCESS_SETUP_FAIL: service process is not in supervisor: %s\n", current_path);
        return 1;
    }
    memcpy(delegated_path, current_path, current_len - 11);
    delegated_path[current_len - 11] = 0;
    printf("V2_DELEGATED_PATH=%s\n", delegated_path); fflush(stdout);
    int service_parent = rt_lg_open_absolute_dir(delegated_path);
    if (service_parent < 0) {
        printf("PROCESS_SETUP_FAIL: cannot open service parent errno=%d\n", errno);
        return 1;
    }
    if (!setup_owned_service_parent(service_parent, delegated_path, expected_service)) {
        printf("PROCESS_SETUP_FAIL: owned service parent setup/readback failed errno=%d\n", errno);
        close(service_parent); return 1;
    }
    char controls_before[4096];
    if (!rt_lg_read_at(service_parent, "cgroup.subtree_control", controls_before,
            sizeof(controls_before))) {
        printf("PROCESS_SETUP_FAIL: enabled controllers unreadable errno=%d\n", errno);
        close(service_parent); return 1;
    }

    char identity[65]; uint8_t identity_bytes[32];
    SHA256((const uint8_t*)expected_service, strlen(expected_service), identity_bytes);
    static const char hex[] = "0123456789abcdef";
    for (int i = 0; i < 32; i++) {
        identity[i * 2] = hex[identity_bytes[i] >> 4];
        identity[i * 2 + 1] = hex[identity_bytes[i] & 15];
    }
    identity[64] = 0;
    const char *attempt = evidence_dir;
    SplArray *admission = rt_linux_group_parent_acquire_at_v2(delegated_path,
        strlen(delegated_path), attempt, strlen(attempt), identity, 64);
    if (!admission || admission->len != 4) {
        printf("PARENT_ADMISSION_UNKNOWN: receipt layout invalid\n");
        close(service_parent); return 1;
    }
    int64_t parent_status = field(admission, 0), parent_token = field(admission, 1);
    if (parent_status != 0 || parent_token <= 0 || field(admission, 2) < 0 || field(admission, 3) <= 0) {
        if (parent_token > 0) {
            int cleanup = release_v2_parent_without_process(service_parent,
                parent_token, controls_before);
            if (cleanup == 0)
                printf("PARENT_ADMISSION_FAIL_CLEANED: status=%lld token=%lld\n",
                    (long long)parent_status, (long long)parent_token);
            else
                printf("PARENT_ADMISSION_CLEANUP_PENDING: status=%lld token=%lld cleanup=%d\n",
                    (long long)parent_status, (long long)parent_token, cleanup);
        } else if (parent_token < 0 || (parent_status == 0 && parent_token == 0)) {
            printf("PARENT_ADMISSION_UNKNOWN: status=%lld token=%lld\n",
                (long long)parent_status, (long long)parent_token);
        } else {
            printf("PARENT_ADMISSION_REJECTED: status=%lld token=%lld\n",
                (long long)parent_status, (long long)parent_token);
        }
        close(service_parent); return 1;
    }
    printf("PARENT_ADMISSION_PASS: token=%lld device=%lld inode=%lld\n",
        (long long)parent_token, (long long)field(admission, 2), (long long)field(admission, 3));
    fflush(stdout);

    char executable[4096], digest[65], stdout_path[4096], stderr_path[4096];
    if (!realpath("/usr/bin/true", executable)) {
        printf("PROCESS_FAIL: /usr/bin/true resolution failed errno=%d\n", errno);
        int cleanup = release_v2_parent_without_process(service_parent, parent_token, controls_before);
        if (cleanup != 0) { close(service_parent); return 79; }
        close(service_parent); return 1;
    }
    digest_path(executable, digest);
    int sealed_probe = rt_lg_pin_image(executable, digest);
    if (sealed_probe < 0) {
        printf("PROCESS_FAIL: sealed-image preflight failed errno=%d\n", errno);
        int cleanup = release_v2_parent_without_process(service_parent, parent_token, controls_before);
        if (cleanup != 0) { close(service_parent); return 79; }
        close(service_parent); return 1;
    }
    close(sealed_probe);
    if (snprintf(stdout_path, sizeof(stdout_path), "%s/true.stdout", evidence_dir) >= (int)sizeof(stdout_path) ||
        snprintf(stderr_path, sizeof(stderr_path), "%s/true.stderr", evidence_dir) >= (int)sizeof(stderr_path)) {
        printf("PROCESS_FAIL: evidence output path too long\n");
        int cleanup = release_v2_parent_without_process(service_parent, parent_token, controls_before);
        if (cleanup != 0) { close(service_parent); return 79; }
        close(service_parent); return 1;
    }
    printf("PROCESS_IMAGE=/usr/bin/true sha256=%s extra_args=empty env=empty cwd=%s\n",
        digest, evidence_dir);
    SplArray empty_args = {0}, empty_environment = {0};
    SplArray *started = rt_linux_group_start_v1(executable, strlen(executable), digest, 64,
        &empty_args, &empty_environment, evidence_dir, strlen(evidence_dir), attempt,
        strlen(attempt), identity, 64, 33554432, 5000, stdout_path, strlen(stdout_path),
        stderr_path, strlen(stderr_path));
    char group_name[80]; snprintf(group_name, sizeof(group_name), "simple-native-%s", identity);
    if (!started || started->len != 2) {
        printf("PROCESS_CLEANUP_PENDING: start receipt layout unknown\n");
        close(service_parent); return 79;
    }
    int64_t start_token = field(started, 0), start_status = field(started, 1);
    if (start_token != 1 || start_status != 0) {
        if (start_token != 0 || start_status == 0) {
            printf("PROCESS_CLEANUP_PENDING: start receipt token=%lld status=%lld is ambiguous\n",
                (long long)start_token, (long long)start_status);
            close(service_parent); return 79;
        }
        struct stat child_status;
        int child_absent = fstatat(rt_lg_delegation.parent_fd, group_name, &child_status,
            AT_SYMLINK_NOFOLLOW) == -1 && errno == ENOENT;
        int release = child_absent ? release_v2_parent_without_process(service_parent,
            parent_token, controls_before) : 79;
        if (!child_absent || release != 0) {
            printf("PROCESS_CLEANUP_PENDING: start_status=%lld child_absent=%d release=%lld\n",
                (long long)start_status, child_absent, (long long)release);
            close(service_parent); return 79;
        }
        if (start_status == ENOSYS) printf("PROCESS_UNSUPPORTED: status=ENOSYS; parent_admission=PASS\n");
        else if (start_status == EPERM) printf("PROCESS_POLICY_BLOCKED: status=EPERM; parent_admission=PASS\n");
        else printf("PROCESS_FAIL: start_status=%lld; parent_admission=PASS\n", (long long)start_status);
        close(service_parent);
        return start_status == ENOSYS ? 77 : (start_status == EPERM ? 78 : 1);
    }

    int terminal = 0, poll_error = 0, completion_deadline = 0, clock_failure = 0;
    SplArray *observed = NULL;
    int64_t poll_started = rt_lg_now_ms();
    if (poll_started < 0) { poll_error = EIO; clock_failure = 1; }
    for (int i = 0; i < 1000 && !terminal && !poll_error; i++) {
        int64_t now = rt_lg_now_ms();
        if (now < 0) { poll_error = EIO; clock_failure = 1; break; }
        if (now - poll_started >= 10000) { completion_deadline = 1; break; }
        observed = rt_linux_group_poll_v1(1);
        if (!observed || observed->len != 10) { poll_error = EPROTO; break; }
        if (field(observed, 0) != 0) { poll_error = (int)field(observed, 0); break; }
        if (field(observed, 1) == 1) { terminal = 1; break; }
        usleep(10000);
    }
    if (!terminal && !poll_error && !clock_failure) {
        int64_t now = rt_lg_now_ms();
        if (now < 0) clock_failure = 1;
        else if (now - poll_started >= 10000) completion_deadline = 1;
        else completion_deadline = 1; /* bounded poll-turn budget elapsed */
    }
    if (!terminal) {
        int64_t cancel = rt_linux_group_cancel_v1(1);
        int64_t drain_started = rt_lg_now_ms();
        if (drain_started < 0) clock_failure = 1;
        printf("PROCESS_DRAIN: initial_poll_error=%d deadline=%d clock_failure=%d cancel=%lld\n",
            poll_error, completion_deadline, clock_failure, (long long)cancel); fflush(stdout);
        for (int i = 0; i < 1000; i++) {
            if (drain_started >= 0 && !clock_failure) {
                int64_t now = rt_lg_now_ms();
                if (now < 0) clock_failure = 1;
                else if (now - drain_started >= 10000) break;
            }
            observed = rt_linux_group_poll_v1(1);
            if (observed && observed->len == 10 && field(observed, 0) == 0 &&
                field(observed, 1) == 1) { terminal = 1; break; }
            usleep(10000);
        }
    }
    if (!terminal) {
        printf("PROCESS_CLEANUP_PENDING: terminal state unproven after bounded cancel/drain\n");
        close(service_parent); return 79;
    }
    int process_ok = poll_error == 0 && !completion_deadline && !clock_failure &&
        field(observed, 2) == 1 && field(observed, 3) == 1 && field(observed, 4) == 0 &&
        field(observed, 5) == 0 && field(observed, 6) == 0 && field(observed, 7) == 0;
    SplArray *collected = rt_linux_group_collect_v1(1);
    if (!collected || collected->len != 10 || field(collected, 0) != 0 ||
        field(collected, 1) != 1 || field(collected, 2) != 1 || field(collected, 3) != 1 ||
        field(collected, 4) != 0) {
        printf("PROCESS_CLEANUP_PENDING: collect/reap receipt unproven\n");
        close(service_parent); return 79;
    }
    struct stat child_missing;
    if (fstatat(rt_lg_delegation.parent_fd, group_name, &child_missing,
            AT_SYMLINK_NOFOLLOW) != -1 || errno != ENOENT) {
        printf("PROCESS_CLEANUP_PENDING: child cgroup remains after collect\n");
        close(service_parent); return 79;
    }
    int cleanup = release_v2_parent_without_process(service_parent, parent_token, controls_before);
    close(service_parent);
    if (cleanup != 0) {
        printf("PROCESS_CLEANUP_PENDING: parent release/removal/controller receipt unproven\n");
        return 79;
    }
    if (!process_ok) {
        printf("PROCESS_FAIL: poll_error=%d deadline=%d clock_failure=%d exit=%lld timeout=%lld cancelled=%lld\n",
            poll_error, completion_deadline, clock_failure,
            (long long)field(observed, 5), (long long)field(observed, 6), (long long)field(observed, 7));
        return 1;
    }
    printf("PROCESS_PASS: clone3 sealed_exec=true exit=0 leader_reaped=true tree_empty=true peak=%lld parent_released=true\n",
        (long long)field(observed, 8));
    return 0;
}

int main(int argc, char **argv) {
    if (argc == 3 && strcmp(argv[2], "lifecycle") == 0) return lifecycle_probe(argv[1]);
    if (argc == 3 && strcmp(argv[1], "v2-service") == 0)
        return v2_service_probe(argv[2]);
    if (argc == 4 && strcmp(argv[1], "v2-process") == 0)
        return v2_process_probe(argv[2], argv[3]);
    int monitor = argc == 3 && strcmp(argv[2], "monitor") == 0;
    assert((argc == 2 || monitor) && argv[1][0] == '/');
    const char *identity = "cafef00dcafef00dcafef00dcafef00dcafef00dcafef00dcafef00dcafef00d";
    const char *other = "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb";
    const char *path = argv[1];
    SplArray empty = {0};
    char root_before[4096], root_after[4096], current_before[4096], current_after[4096];
    int root = open("/sys/fs/cgroup", O_RDONLY | O_DIRECTORY);
    int current = rt_lg_parent(); assert(root >= 0 && current >= 0);
    assert(rt_lg_read_at(root, "cgroup.subtree_control", root_before, sizeof(root_before)));
    int current_before_ok = rt_lg_read_at(current, "cgroup.subtree_control", current_before, sizeof(current_before));
    if (!current_before_ok) { assert(errno == ENODATA); current_before[0] = 0; }
    assert(field(rt_linux_group_parent_acquire_v1(path, strlen(path), "bad", 3), 0) == EINVAL);
    SplArray *parent = rt_linux_group_parent_acquire_v1(path, strlen(path), identity, strlen(identity));
    printf("acquire status=%lld dev=%lld inode=%lld\n", (long long)field(parent, 0),
        (long long)field(parent, 2), (long long)field(parent, 3)); fflush(stdout);
    assert(field(parent, 0) == 0 && field(parent, 1) == 1);
    assert(field(rt_linux_group_parent_acquire_v1(path, strlen(path), other, 64), 0) != 0);
    SplArray *capacity = rt_linux_group_available_capacity_v1(path, strlen(path));
    assert(field(capacity, 0) == 0 && field(capacity, 1) > 0 && field(capacity, 2) > 0);
    /* An external parent constraint must bound reported capacity. */
    assert(rt_lg_write_at(rt_lg_delegation.parent_fd, "memory.max", "67108864"));
    capacity = rt_linux_group_available_capacity_v1(path, strlen(path));
    assert(field(capacity, 0) == 0 && field(capacity, 1) <= 67108864);
    char executable[4096], digest[65], out[4096], err[4096];
    assert(realpath("/usr/bin/true", executable)); digest_path(executable, digest);
    snprintf(out, sizeof(out), "%s/stdout.log", path);
    snprintf(err, sizeof(err), "%s/stderr.log", path);
    SplArray *wrong = rt_linux_group_start_v1(executable, strlen(executable), digest, 64,
        &empty, &empty, path, strlen(path), path, strlen(path), other, 64,
        33554432, 5000, out, strlen(out), err, strlen(err));
    assert(field(wrong, 0) == 0 && field(wrong, 1) == ESTALE);
    SplArray *started = rt_linux_group_start_v1(executable, strlen(executable), digest, 64,
        &empty, &empty, path, strlen(path), path, strlen(path), identity, 64,
        monitor ? 0 : 33554432, monitor ? 0 : 5000, out, strlen(out), err, strlen(err));
    printf("start status=%lld token=%lld\n", (long long)field(started, 1), (long long)field(started, 0)); fflush(stdout);
    assert(field(started, 0) == 1 && field(started, 1) == 0);
    assert(rt_linux_group_parent_release_v1(1) == EBUSY);
    char limit[128];
    assert(rt_lg_read_at(rt_linux_group.group_fd, "memory.max", limit, sizeof(limit)));
    assert(strcmp(limit, monitor ? "max\n" : "33554432\n") == 0);
    assert(rt_lg_read_at(rt_linux_group.group_fd, "memory.swap.max", limit, sizeof(limit)));
    assert(strcmp(limit, monitor ? "max\n" : "0\n") == 0);
    SplArray *observed = NULL;
    for (int i = 0; i < 1000; i++) {
        observed = rt_linux_group_poll_v1(1);
        assert(field(observed, 0) == 0);
        if (field(observed, 1)) break;
        usleep(10000);
    }
    assert(field(observed, 1) && field(observed, 2) && field(observed, 3));
    assert(field(observed, 5) == 0 && field(observed, 8) > 0);
    assert(!field(observed, 6)); /* timeout=0 must not become immediate timeout */
    assert(field(rt_linux_group_collect_v1(1), 0) == 0);
    assert(rt_linux_group_parent_release_v1(1) == 0);
    assert(rt_linux_group_parent_release_v1(1) == EINVAL);
    struct stat missing;
    assert(fstatat(root, rt_lg_delegation.name, &missing, AT_SYMLINK_NOFOLLOW) == -1 && errno == ENOENT);
    assert(rt_lg_read_at(root, "cgroup.subtree_control", root_after, sizeof(root_after)));
    int current_after_ok = rt_lg_read_at(current, "cgroup.subtree_control", current_after, sizeof(current_after));
    if (!current_after_ok) { assert(errno == ENODATA); current_after[0] = 0; }
    assert(strcmp(root_before, root_after) == 0 && strcmp(current_before, current_after) == 0);
    close(root); close(current);
    puts(monitor ? "PASS: positive parent capacity/no child memory or swap cap/no work deadline/peak/reap/cleanup" :
        "PASS: parent identity/capacity cap/atomic clone/child cap/reap/cleanup/no global mutation");
    return 0;
}
