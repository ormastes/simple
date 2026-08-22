#define _GNU_SOURCE
#include <assert.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/resource.h>
#include <sys/stat.h>
#include <time.h>
#include <unistd.h>
#include <fcntl.h>

#include "../platform/hosted_confined_file_impl.h"

static volatile int track_allocations;
static volatile uint64_t allocation_count;
void *__real_malloc(size_t);
void *__real_calloc(size_t, size_t);
void *__real_realloc(void *, size_t);
void *__wrap_malloc(size_t n) { if (track_allocations) allocation_count++; return __real_malloc(n); }
void *__wrap_calloc(size_t a, size_t b) { if (track_allocations) allocation_count++; return __real_calloc(a, b); }
void *__wrap_realloc(void *p, size_t n) { if (track_allocations) allocation_count++; return __real_realloc(p, n); }

static int64_t ns_now(void) {
    struct timespec ts;
    assert(clock_gettime(CLOCK_MONOTONIC, &ts) == 0);
    return (int64_t)ts.tv_sec * 1000000000LL + ts.tv_nsec;
}

static void put_file(const char *path, const char *body) {
    int fd = open(path, O_CREAT | O_EXCL | O_WRONLY | O_CLOEXEC, 0600);
    assert(fd >= 0);
    assert(write(fd, body, strlen(body)) == (ssize_t)strlen(body));
    assert(close(fd) == 0);
}

static void join_path(char *out, size_t cap, const char *base, const char *suffix) {
    size_t a = strlen(base), b = strlen(suffix);
    assert(a + b + 1 <= cap);
    memcpy(out, base, a);
    memcpy(out + a, suffix, b + 1);
}

int main(void) {
    char base[] = "/tmp/simple-confined-file-XXXXXX";
    assert(mkdtemp(base) != NULL);
    char root[512], moved[512], sub[512], file[512], leaf_link[512], dir_link[512];
    char attacker_sub[512], attacker_file[512];
    join_path(root, sizeof(root), base, "/root");
    join_path(moved, sizeof(moved), base, "/root-pinned");
    join_path(sub, sizeof(sub), root, "/sub");
    join_path(file, sizeof(file), sub, "/data");
    join_path(leaf_link, sizeof(leaf_link), root, "/leaf-link");
    join_path(dir_link, sizeof(dir_link), root, "/dir-link");
    assert(mkdir(root, 0700) == 0 && mkdir(sub, 0700) == 0);
    put_file(file, "original");
    assert(symlink("/etc/passwd", leaf_link) == 0);
    assert(symlink("/etc", dir_link) == 0);

    int64_t root_fd = rt_hosted_confined_root_open((const uint8_t *)root, (int64_t)strlen(root));
    assert(root_fd >= 0);
    assert(rename(root, moved) == 0);
    assert(mkdir(root, 0700) == 0);
    join_path(attacker_sub, sizeof(attacker_sub), root, "/sub");
    join_path(attacker_file, sizeof(attacker_file), attacker_sub, "/data");
    assert(mkdir(attacker_sub, 0700) == 0);
    put_file(attacker_file, "attacker");

    const uint8_t relative[] = "sub/data";
    int64_t fd = rt_hosted_confined_file_open(root_fd, relative, 8, 0, 8, 1);
    assert(fd >= 0);
    uint8_t out[32] = {0};
    assert(rt_hosted_confined_file_read_at(fd, 0, out, 32, 0, 8) == 8);
    assert(memcmp(out, "original", 8) == 0);
    const uint8_t update[] = "updated!";
    assert(rt_hosted_confined_file_write_at(fd, 0, update, 8, 0, 8) == 8);
    memset(out, 0, sizeof(out));
    assert(rt_hosted_confined_file_read_at(fd, 0, out, 32, 0, 8) == 8);
    assert(memcmp(out, update, 8) == 0);

    const uint8_t leaf[] = "leaf-link";
    const uint8_t through_dir[] = "dir-link/passwd";
    const uint8_t parent[] = "../etc/passwd";
    const uint8_t absolute[] = "/etc/passwd";
    assert(rt_hosted_confined_file_open(root_fd, leaf, 9, 0, 9, 0) < 0);
    assert(rt_hosted_confined_file_open(root_fd, through_dir, 15, 0, 15, 0) < 0);
    assert(rt_hosted_confined_file_open(root_fd, parent, 13, 0, 13, 0) < 0);
    assert(rt_hosted_confined_file_open(root_fd, absolute, 11, 0, 11, 0) < 0);

    const int iterations = 20000;
    allocation_count = 0;
    track_allocations = 1;
    int64_t start = ns_now();
    for (int i = 0; i < iterations; ++i)
        assert(rt_hosted_confined_file_read_at(fd, 0, out, 32, 0, 8) == 8);
    int64_t elapsed = ns_now() - start;
    track_allocations = 0;
    assert(allocation_count == 0);
    assert(rt_hosted_confined_file_close(fd));
    assert(rt_hosted_confined_file_close(root_fd));

    struct rusage usage;
    assert(getrusage(RUSAGE_SELF, &usage) == 0);
    assert(usage.ru_maxrss < 16384);
    printf("hosted-confined-file: PASS iterations=%d avg_read_ns=%lld alloc=%llu max_rss_kib=%ld\n",
        iterations, (long long)(elapsed / iterations),
        (unsigned long long)allocation_count, usage.ru_maxrss);

    assert(unlink(attacker_file) == 0 && rmdir(attacker_sub) == 0 && rmdir(root) == 0);
    join_path(file, sizeof(file), moved, "/sub/data");
    join_path(leaf_link, sizeof(leaf_link), moved, "/leaf-link");
    join_path(dir_link, sizeof(dir_link), moved, "/dir-link");
    join_path(sub, sizeof(sub), moved, "/sub");
    assert(unlink(file) == 0 && unlink(leaf_link) == 0 && unlink(dir_link) == 0);
    assert(rmdir(sub) == 0 && rmdir(moved) == 0 && rmdir(base) == 0);
    return 0;
}
