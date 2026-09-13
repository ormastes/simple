/* Build with runtime_native.c and SIMPLE_HOSTED_SAFE_ARTIFACT_TEST_V1. */
#include "../runtime.h"
#include "../runtime_hosted_safe_artifact_v1.h"

#include <assert.h>
#include <errno.h>
#include <fcntl.h>
#include <pthread.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>
#include <unistd.h>

typedef struct Fault {
    const char* operation;
    int error;
    unsigned int skip, remaining, observed;
} Fault;
static Fault faults[2];
static int mutate_fd = -1;
static int mutate_stat_count;

int rt_hsa_test_fault_v1(const char* operation, int fd) {
    (void)fd;
    if (mutate_fd >= 0 && strcmp(operation, "fstat") == 0 && ++mutate_stat_count == 3) {
        assert(ftruncate(mutate_fd, 1) == 0);
    }
    for (unsigned int i = 0; i < 2; ++i) {
        Fault* f = &faults[i];
        if (!f->operation || strcmp(f->operation, operation) != 0) continue;
        ++f->observed;
        if (f->skip) { --f->skip; continue; }
        if (f->remaining) { --f->remaining; return f->error; }
    }
    return 0;
}

static void clear_faults(void) { memset(faults, 0, sizeof(faults)); }
static void fault(const char* operation, int error, unsigned int skip, unsigned int count) {
    clear_faults();
    faults[0] = (Fault){operation, error, skip, count, 0};
}
static int64_t acquire(const char* path) {
    return rt_hosted_safe_artifact_root_open_v1((const uint8_t*)path, strlen(path));
}
static int64_t read_artifact(int64_t root, const char* path, int64_t max_bytes) {
    return rt_hosted_safe_artifact_read_v1(root, (const uint8_t*)path, strlen(path), max_bytes);
}
static int64_t publish(int64_t root, const char* path, int64_t array, int64_t bound) {
    return rt_hosted_safe_artifact_publish_v1(root, (const uint8_t*)path, strlen(path), array, bound);
}
static int64_t bytes_value(const uint8_t* bytes, size_t size) {
    SplArray* array = rt_byte_array_new_len(size);
    assert(array != NULL);
    int64_t value = (int64_t)(uintptr_t)array;
    assert(rt_array_bytes_store_checked(value, bytes, (int64_t)size) == (int64_t)size);
    return value;
}
static void expect_bytes(int64_t value, const uint8_t* expected, size_t size) {
    uint8_t copied[32] = {0};
    assert(size <= sizeof(copied) && value != 0);
    assert(!rt_is_none(value) && rt_is_some(value));
    assert(rt_array_bytes_validate(value) == (int64_t)size);
    assert(rt_array_bytes_copy_checked(value, copied, sizeof(copied)) == (int64_t)size);
    assert(memcmp(copied, expected, size) == 0);
    rt_array_free((SplArray*)(uintptr_t)value);
}
static void expect_none(int64_t value) {
    assert(value == rt_value_nil() && value == 3);
    assert(rt_is_none(value) && !rt_is_some(value));
}
static void create_file(int root, const char* path, const uint8_t* bytes, size_t size) {
    int fd = openat(root, path, O_WRONLY | O_CREAT | O_EXCL | O_CLOEXEC, 0600);
    assert(fd >= 0);
    assert(write(fd, bytes, size) == (ssize_t)size);
    assert(close(fd) == 0);
}
static void absent(int root, const char* path) {
    struct stat value;
    assert(fstatat(root, path, &value, AT_SYMLINK_NOFOLLOW) < 0 && errno == ENOENT);
}

typedef struct PublishTask { int64_t root, bytes, result; } PublishTask;
static void* concurrent_publish(void* raw) {
    PublishTask* task = (PublishTask*)raw;
    task->result = publish(task->root, "race", task->bytes, 32);
    return NULL;
}

int main(void) {
    const uint8_t payload[] = {0x00, 0x7f, 0x80, 0xff, 0x2a};
    /* Probe the exact extern ABI and the actual runtime optional predicates.
     * Raw zero is a present value; it cannot represent a failed byte read. */
    int64_t (*read_abi)(int64_t, const uint8_t*, uint64_t, int64_t) =
        rt_hosted_safe_artifact_read_v1;
    assert(rt_value_nil() == 3 && !rt_is_none(0));
    expect_none(read_abi(-1, (const uint8_t*)"missing", 7, 32));
    char directory[] = "/tmp/simple-safe-artifact-v1-XXXXXX";
    char moved[256], symlink_root[256], path[256];
    assert(mkdtemp(directory));
    int test_root = open(directory, O_RDONLY | O_DIRECTORY | O_CLOEXEC);
    assert(test_root >= 0);
    assert(mkdirat(test_root, "nested", 0700) == 0);
    create_file(test_root, "source", payload, sizeof(payload));
    create_file(test_root, "empty", payload, 0);
    assert(symlinkat("source", test_root, "link") == 0);
    assert(symlinkat("nested", test_root, "dirlink") == 0);
    assert(mkfifoat(test_root, "fifo", 0600) == 0);
    assert(snprintf(symlink_root, sizeof(symlink_root), "%s-link", directory) > 0);
    assert(symlink(directory, symlink_root) == 0);
    assert(acquire(symlink_root) == -1);
    assert(snprintf(path, sizeof(path), "%s-link/nested", directory) > 0);
    assert(acquire(path) == -1);
    assert(unlink(symlink_root) == 0);

    assert(acquire("relative") == -1);
    assert(acquire("/tmp/../tmp") == -1);
    assert(acquire("/tmp//bad") == -1);
    assert(acquire("/tmp/") == -1);
    assert(rt_hosted_safe_artifact_root_open_v1((const uint8_t*)"/tmp\0x", 6) == -1);
    assert(rt_hosted_safe_artifact_root_open_v1(NULL, 4) == -1);
    int64_t root = acquire(directory);
    assert(root > 0);
    assert(!rt_hosted_safe_artifact_root_close_v1(-1));
    assert(!rt_hosted_safe_artifact_root_close_v1(INT64_MAX));
    expect_bytes(read_artifact(root, "source", sizeof(payload)), payload, sizeof(payload));
    expect_bytes(read_artifact(root, "empty", 0), payload, 0);
    expect_none(read_artifact(root, "source", sizeof(payload) - 1));
    expect_none(read_artifact(root, "source", -1));
    expect_none(read_artifact(root, "source", 16777217));
    expect_none(read_artifact(root, "missing", 32));
    expect_none(read_artifact(root, "fifo", 32));
    expect_none(read_artifact(root, "nested", 32));
    const char* invalid[] = {"link", "dirlink/nope", "../source", "/source", "./source", "nested//x", "nested/", "\\source", ""};
    for (size_t i = 0; i < sizeof(invalid) / sizeof(invalid[0]); ++i)
        expect_none(read_artifact(root, invalid[i], 32));
    expect_none(rt_hosted_safe_artifact_read_v1(root, (const uint8_t*)"source\0x", 8, 32));

    fault("openat2", EINTR, 0, 1);
    expect_bytes(read_artifact(root, "source", 32), payload, sizeof(payload));
    assert(faults[0].observed == 2);
    fault("read", EINTR, 0, 32);
    expect_none(read_artifact(root, "source", 32));
    assert(faults[0].observed == 32);
    fault("read", EIO, 0, 1);
    expect_none(read_artifact(root, "source", 32));
    fault("fstat", EIO, 1, 1);
    expect_none(read_artifact(root, "source", 32));
    fault("close", EINTR, 0, 1);
    expect_none(read_artifact(root, "source", 32));
    assert(faults[0].observed == 1);
    const char* allocation_ops[] = {"read-allocation", "array-allocation", "array-store"};
    for (size_t i = 0; i < sizeof(allocation_ops) / sizeof(allocation_ops[0]); ++i) {
        fault(allocation_ops[i], ENOMEM, 0, 1);
        expect_none(read_artifact(root, "source", 32));
        assert(faults[0].observed == 1);
    }
    clear_faults();
    mutate_fd = openat(test_root, "source", O_WRONLY | O_CLOEXEC);
    assert(mutate_fd >= 0);
    expect_none(read_artifact(root, "source", 32));
    assert(close(mutate_fd) == 0);
    mutate_fd = -1;
    assert(unlinkat(test_root, "source", 0) == 0);
    create_file(test_root, "source", payload, sizeof(payload));

    int64_t bytes = bytes_value(payload, sizeof(payload));
    assert(publish(root, "nested/output", bytes, 32) == 0);
    expect_bytes(read_artifact(root, "nested/output", 32), payload, sizeof(payload));
    struct stat output_identity;
    assert(fstatat(test_root, "nested/output", &output_identity, 0) == 0);
    assert((output_identity.st_mode & 0777) == 0600);
    assert(publish(root, "nested/output", bytes, 32) == -2);
    assert(publish(root, "link", bytes, 32) == -2);
    assert(publish(root, "dirlink/output", bytes, 32) == -1);
    assert(publish(root, "../outside", bytes, 32) == -1);
    assert(publish(root, "too-small", bytes, 4) == -1);
    assert(publish(root, "invalid-array", 0, 32) == -1);
    absent(test_root, "too-small");
    absent(test_root, "invalid-array");

    int64_t empty = bytes_value(payload, 0);
    assert(publish(root, "zero", empty, 0) == 0);
    expect_bytes(read_artifact(root, "zero", 0), payload, 0);
    rt_array_free((SplArray*)(uintptr_t)empty);
    fault("openat2", ENOSYS, 0, 1);
    assert(publish(root, "unsupported-lookup", bytes, 32) == -3);
    fault("openat", EOPNOTSUPP, 0, 1);
    assert(publish(root, "unsupported-stage", bytes, 32) == -3);
    const char* failed_ops[] = {"write", "fdatasync", "fsync", "linkat"};
    for (size_t i = 0; i < sizeof(failed_ops) / sizeof(failed_ops[0]); ++i) {
        fault(failed_ops[i], EIO, 0, 1);
        assert(publish(root, "failed", bytes, 32) == -1);
        absent(test_root, "failed");
    }
    fault("write", EIO, 0, 1);
    faults[1] = (Fault){"close", EIO, 0, 1, 0};
    assert(publish(root, "cleanup-failed", bytes, 32) == -5);
    absent(test_root, "cleanup-failed");
    fault("fsync", EIO, 1, 1);
    assert(publish(root, "visible-not-durable", bytes, 32) == -4);
    clear_faults();
    expect_bytes(read_artifact(root, "visible-not-durable", 32), payload, sizeof(payload));
    fault("close", EIO, 0, 1);
    assert(publish(root, "visible-close-failed", bytes, 32) == -4);
    clear_faults();
    expect_bytes(read_artifact(root, "visible-close-failed", 32), payload, sizeof(payload));

    PublishTask first = {root, bytes, -99}, second = {root, bytes, -99};
    pthread_t threads[2];
    assert(pthread_create(&threads[0], NULL, concurrent_publish, &first) == 0);
    assert(pthread_create(&threads[1], NULL, concurrent_publish, &second) == 0);
    assert(pthread_join(threads[0], NULL) == 0 && pthread_join(threads[1], NULL) == 0);
    assert((first.result == 0 && second.result == -2) || (first.result == -2 && second.result == 0));
    expect_bytes(read_artifact(root, "race", 32), payload, sizeof(payload));

    int64_t handles[31];
    for (unsigned int i = 0; i < 31; ++i) { handles[i] = acquire(directory); assert(handles[i] > 0); }
    assert(acquire(directory) == -1);
    for (unsigned int i = 0; i < 31; ++i) assert(rt_hosted_safe_artifact_root_close_v1(handles[i]));

    assert(snprintf(moved, sizeof(moved), "%s-moved", directory) > 0);
    assert(rename(directory, moved) == 0 && mkdir(directory, 0700) == 0);
    expect_bytes(read_artifact(root, "source", 32), payload, sizeof(payload));
    int64_t replacement = acquire(directory);
    assert(replacement > 0 && replacement != root);
    expect_none(read_artifact(replacement, "source", 32));
    fault("close", EINTR, 0, 1);
    assert(!rt_hosted_safe_artifact_root_close_v1(root));
    assert(faults[0].observed == 1);
    clear_faults();
    assert(!rt_hosted_safe_artifact_root_close_v1(root));
    expect_none(read_artifact(root, "source", 32));
    assert(publish(root, "stale", bytes, 32) == -1);
    assert(rt_hosted_safe_artifact_root_close_v1(replacement));
    assert(rmdir(directory) == 0);
    rt_array_free((SplArray*)(uintptr_t)bytes);

    const char* cleanup[] = {"source", "empty", "link", "dirlink", "fifo", "nested/output", "zero", "visible-not-durable", "visible-close-failed", "race"};
    for (size_t i = 0; i < sizeof(cleanup) / sizeof(cleanup[0]); ++i) assert(unlinkat(test_root, cleanup[i], 0) == 0);
    assert(unlinkat(test_root, "nested", AT_REMOVEDIR) == 0);
    assert(close(test_root) == 0 && rmdir(moved) == 0);
    puts("PASS: hosted-safe-artifact native retained-root/read/publish ABI and failure cleanup");
    return 0;
}
