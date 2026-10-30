/* Focused Linux fail-closed capability check. This host fixture deliberately
 * does not qualify tree reap or a memory cap; it only proves that a read-only
 * cgroup-v2 subtree cannot launch a grouped worker. */
#include "../runtime.h"
#if defined(__linux__)
#include <assert.h>
#include <errno.h>
#include <fcntl.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#ifdef RT_LINUX_GROUP_TEST_OPENSSL
#include <openssl/sha.h>
#endif

static void owned_sha256(const uint8_t *data, size_t len, uint8_t out[32]) {
#ifdef RT_LINUX_GROUP_TEST_OPENSSL
    SHA256(data, len, out);
#else
    (void)data; (void)len; memset(out, 0, 32);
#endif
}
static char **owned_adapter_copy_argv(const char *command, uint64_t length,
        SplArray *args, int64_t *argc, int *error) {
    (void)args;
    char **value = calloc(2, sizeof(char*));
    if (!value) return NULL;
    value[0] = calloc((size_t)length + 1, 1);
    if (!value[0]) { free(value); return NULL; }
    memcpy(value[0], command, (size_t)length);
    *argc = 0; *error = 0; return value;
}
static void owned_adapter_free_argv(char **value, int64_t argc) {
    (void)argc;
    if (value) { free(value[0]); free(value); }
}
static SplArray *owned_adapter_values(const int64_t *values, int64_t count) {
    SplArray *result = calloc(1, sizeof(*result));
    assert(result);
    result->items = calloc((size_t)count, sizeof(*result->items));
    assert(result->items);
    result->cap = result->len = count;
    for (int64_t i = 0; i < count; i++) result->items[i].as_int = values[i];
    return result;
}
int64_t rt_array_len(SplArray *array) { return array ? array->len : -1; }
int64_t rt_array_get(SplArray *array, int64_t index) {
    return array && index >= 0 && index < array->len ? array->items[index].as_int : 0;
}
int64_t rt_string_len(int64_t value) { (void)value; return -1; }
const uint8_t *rt_string_data(int64_t value) { (void)value; return NULL; }

#include "../runtime_linux_group_owner_impl.h"

/* A malformed observation must never become a tree-empty proof. These
 * regular-file fixtures test decoding only, not kernel containment. */
static void check_population_observation(void) {
    char directory[] = "/tmp/simple-group-events-XXXXXX";
    assert(mkdtemp(directory));
    int group = open(directory, O_RDONLY | O_DIRECTORY | O_CLOEXEC);
    assert(group >= 0);
    const char *events[] = {
        "populated 0\nfrozen 0\n", "frozen 0\npopulated 1\n",
        "populated 0junk\n", "populated 00\n", "populated 0",
        "populated 0\npopulated 1\n", "populated 1\npopulated 0\n",
        "notpopulated 0\n", "frozen 0\n", "populated 2\n",
        "populated 0 \n", "populated 0\t\n", "populated -1\n",
        "populated 0\ngarbage", "populated 0\nunknown 3\n",
        "populated 0\npopulated\r1\n", "populated 0\nfrozen 0\nfrozen 1\n"
    };
    for (size_t i = 0; i < sizeof(events) / sizeof(events[0]); i++) {
        int fd = openat(group, "cgroup.events", O_WRONLY | O_CREAT | O_TRUNC, 0600);
        assert(fd >= 0);
        assert(write(fd, events[i], strlen(events[i])) == (ssize_t)strlen(events[i]));
        assert(close(fd) == 0);
        int populated = 1;
        errno = 0;
        int valid = rt_lg_populated(group, &populated);
        if (i < 2) { assert(valid); assert(populated == (int)i); }
        else { assert(!valid); assert(populated == 1); assert(errno == EPROTO); }
    }
    const char hidden[] = "populated 0\n\0populated 1\n";
    int fd = openat(group, "cgroup.events", O_WRONLY | O_TRUNC);
    assert(fd >= 0);
    assert(write(fd, hidden, sizeof(hidden) - 1) == (ssize_t)sizeof(hidden) - 1);
    assert(close(fd) == 0);
    int populated = 1;
    errno = 0;
    assert(!rt_lg_populated(group, &populated));
    assert(populated == 1 && errno == EPROTO);
    assert(unlinkat(group, "cgroup.events", 0) == 0);
    assert(close(group) == 0);
    assert(rmdir(directory) == 0);
    puts("runtime_linux_group_population_observation: PASS");
}

int main(int argc, char **argv) {
    check_population_observation();
    if (argc == 2 && strcmp(argv[1], "--population-only") == 0) return 0;
#ifdef RT_LINUX_GROUP_TEST_OPENSSL
    int image = open("/bin/true", O_RDONLY);
    assert(image >= 0);
    struct stat image_stat;
    assert(fstat(image, &image_stat) == 0);
    uint8_t *image_bytes = mmap(NULL, (size_t)image_stat.st_size, PROT_READ, MAP_PRIVATE, image, 0);
    assert(image_bytes != MAP_FAILED);
    uint8_t image_digest[32]; SHA256(image_bytes, (size_t)image_stat.st_size, image_digest);
    munmap(image_bytes, (size_t)image_stat.st_size); close(image);
    char true_digest[65];
    static const char hex[] = "0123456789abcdef";
    for (int i = 0; i < 32; i++) {
        true_digest[2*i] = hex[image_digest[i] >> 4];
        true_digest[2*i+1] = hex[image_digest[i] & 15];
    }
    true_digest[64] = 0;
    SplArray empty_args = {0};
    char wrong_digest[65]; memset(wrong_digest, 'f', 64); wrong_digest[64] = 0;
    SplArray *rejected = rt_linux_group_launch_broker_v1(
        "/bin/true", 9, wrong_digest, 64, &empty_args);
    assert(rejected && rejected->len == 2 && rejected->items[0].as_int == 0);
    free(rejected->items); free(rejected);
    SplArray *launched = rt_linux_group_launch_broker_v1(
        "/bin/true", 9, true_digest, 64, &empty_args);
    assert(launched && launched->len == 2 && launched->items[0].as_int > 0 &&
        launched->items[1].as_int == 0);
    free(launched->items); free(launched);
#endif
    int parent = rt_lg_parent();
    if (parent < 0) { puts("runtime_linux_group_owner_unavailable_selfcheck: unavailable-no-cgroup2"); return 0; }
    int writable = mkdirat(parent, "simple-native-capability-probe", 0700) == 0;
    if (writable) {
        assert(unlinkat(parent, "simple-native-capability-probe", AT_REMOVEDIR) == 0);
        close(parent);
        puts("runtime_linux_group_owner_unavailable_selfcheck: delegated-live-proof-required");
        return 0;
    }
    assert(errno == EACCES || errno == EPERM || errno == EROFS);
    close(parent);
    SplArray *capacity = rt_linux_group_available_capacity_v1("/tmp", 4);
    assert(capacity && capacity->len == 3 && capacity->items[0].as_int != 0);
    assert(capacity->items[1].as_int == 0 && capacity->items[2].as_int == 0);
    free(capacity->items); free(capacity);
    char zero_digest[65]; memset(zero_digest, '0', 64); zero_digest[64] = 0;
#ifdef RT_LINUX_GROUP_TEST_OPENSSL
    memcpy(zero_digest, true_digest, 65);
#endif
    SplArray empty = {0};
    SplArray *started = rt_linux_group_start_v1("/bin/true", 9,
        zero_digest, 64, &empty, &empty, "/tmp", 4, "/tmp/native-group-test", 22,
        zero_digest, 64, 1048576, 1000,
        "/tmp/native-group-test.stdout", 29,
        "/tmp/native-group-test.stderr", 29);
    assert(started && started->len == 2);
    assert(started->items[0].as_int == 0);
    assert(started->items[1].as_int == EACCES ||
        started->items[1].as_int == EPERM ||
        started->items[1].as_int == EROFS);
    free(started->items); free(started);
    puts("runtime_linux_group_owner_unavailable_selfcheck: PASS (delegation denied, no child launched)");
    return 0;
}
#else
#include <stdio.h>
int main(void) { puts("runtime_linux_group_owner_unavailable_selfcheck: non-Linux"); return 0; }
#endif
