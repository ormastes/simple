/* Native adapter integration probe: real cgroup2, clone3 and sealed exec.
 * Build: cc -D_GNU_SOURCE -I src/runtime THIS_FILE -lcrypto -o PROBE
 * Run: PROBE /absolute/private/evidence-directory
 * Requires a cgroup2 mount whose root already delegates memory. */
#include "runtime.h"
#include <assert.h>
#include <errno.h>
#include <fcntl.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
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

#include "runtime_linux_group_owner_impl.h"

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

int main(int argc, char **argv) {
    assert(argc == 2 && argv[1][0] == '/');
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
        33554432, 5000, out, strlen(out), err, strlen(err));
    printf("start status=%lld token=%lld\n", (long long)field(started, 1), (long long)field(started, 0)); fflush(stdout);
    assert(field(started, 0) == 1 && field(started, 1) == 0);
    assert(rt_linux_group_parent_release_v1(1) == EBUSY);
    char limit[128];
    assert(rt_lg_read_at(rt_linux_group.group_fd, "memory.max", limit, sizeof(limit)));
    assert(strcmp(limit, "33554432\n") == 0);
    SplArray *observed = NULL;
    for (int i = 0; i < 1000; i++) {
        observed = rt_linux_group_poll_v1(1);
        assert(field(observed, 0) == 0);
        if (field(observed, 1)) break;
        usleep(10000);
    }
    assert(field(observed, 1) && field(observed, 2) && field(observed, 3));
    assert(field(observed, 5) == 0 && field(observed, 8) > 0);
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
    puts("PASS: parent identity/capacity cap/atomic clone/child cap/reap/cleanup/no global mutation");
    return 0;
}
