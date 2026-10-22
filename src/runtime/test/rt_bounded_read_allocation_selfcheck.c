/* Real runtime contract tests. Link with --wrap=malloc,realloc,free,open,close,
 * fstat,read,__read_chk. The wrappers perform real file I/O and inject only named negative
 * edges or deterministic file mutations after the reader's successful stat.
 * Run: selfcheck logic DIR bounded|baseline
 *      selfcheck bench DIR SIZE LIMIT ITERATIONS
 * See the paired bug report for exact compile/link commands and qualification. */
#define _GNU_SOURCE
#include <assert.h>
#include <errno.h>
#include <fcntl.h>
#include <inttypes.h>
#include <limits.h>
#include <stdarg.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>
#include <time.h>
#include <unistd.h>

typedef struct SplArray SplArray;
extern int64_t rt_file_read_regular_no_follow_bounded(const uint8_t*, uint64_t, int64_t);
extern int64_t rt_file_read_regular_no_follow_bounded_bytes(const uint8_t*, uint64_t, int64_t);
extern int64_t rt_file_read_regular_no_follow_last_failure(void);
extern int64_t rt_array_bytes_basis_len(SplArray*);
extern int64_t rt_array_bytes_basis_ptr(SplArray*);
extern void rt_array_free(SplArray*);
extern int64_t rt_string_len(int64_t);
extern const uint8_t* rt_string_data(int64_t);
extern int64_t rt_string_free(int64_t);
extern void* __real_malloc(size_t);
extern void* __real_realloc(void*, size_t);
extern void __real_free(void*);
extern int __real_open(const char*, int, ...);
extern int __real_close(int);
extern int __real_fstat(int, struct stat*);
extern ssize_t __real_read(int, void*, size_t);
extern ssize_t __real___read_chk(int, void*, size_t, size_t);

enum Edge { NORMAL, INTERRUPT, READ_ERROR, STAT_ERROR, GROW, SHRINK, SWAP_PATH,
            ALLOC_ERROR, GROW_ALLOC_ERROR };
static int active, watched_fd = -1, fd_balance, fired, buffer_freed;
static enum Edge edge;
static void* read_buffer;
static size_t first_alloc, largest_alloc, max_request, allocations, reallocations;
static char test_path[4096], old_path[4096], target_path[4096];
static const uint8_t tail[] = {0, 255, 7, 8, 9, 10, 11, 12};
static unsigned cases;

void* __wrap_malloc(size_t n) {
    if (!active) return __real_malloc(n);
    allocations++;
    if (n > largest_alloc) largest_alloc = n;
    if (allocations == 1) {
        first_alloc = n;
        if (edge == ALLOC_ERROR) { errno = ENOMEM; return NULL; }
        read_buffer = __real_malloc(n);
        return read_buffer;
    }
    return __real_malloc(n);
}
void* __wrap_realloc(void* p, size_t n) {
    if (!active || p != read_buffer) return __real_realloc(p, n);
    reallocations++;
    if (n > largest_alloc) largest_alloc = n;
    if (edge == GROW_ALLOC_ERROR) { errno = ENOMEM; return NULL; }
    void* result = __real_realloc(p, n);
    if (result) read_buffer = result;
    return result;
}
void __wrap_free(void* p) {
    if (active && p && p == read_buffer) buffer_freed = 1;
    __real_free(p);
}
int __wrap_open(const char* p, int flags, ...) {
    mode_t mode = 0;
    if (flags & O_CREAT) { va_list ap; va_start(ap, flags); mode = va_arg(ap, int); va_end(ap); }
    int fd = __real_open(p, flags, mode);
    if (active && fd >= 0) {
        assert((flags & O_NOFOLLOW) && (flags & O_CLOEXEC));
        assert(watched_fd == -1);
        watched_fd = fd;
        fd_balance++;
    }
    return fd;
}
int __wrap_close(int fd) {
    if (active && fd == watched_fd) { watched_fd = -1; fd_balance--; }
    return __real_close(fd);
}
int __wrap_fstat(int fd, struct stat* st) {
    if (active && fd == watched_fd && edge == STAT_ERROR) { errno = EIO; return -1; }
    return __real_fstat(fd, st);
}
static ssize_t checked_read(int fd, void* bytes, size_t n, int fortified, size_t object_size) {
    if (active && fd == watched_fd) {
        if (n > max_request) max_request = n;
        if (!fired) {
            fired = 1;
            if (edge == INTERRUPT) { errno = EINTR; return -1; }
            if (edge == READ_ERROR) { errno = EIO; return -1; }
            if (edge == GROW || edge == GROW_ALLOC_ERROR || edge == SHRINK) {
                int writer = __real_open(test_path, O_WRONLY | O_APPEND);
                assert(writer >= 0);
                if (edge == SHRINK) assert(ftruncate(writer, 0) == 0);
                else assert(write(writer, tail, sizeof(tail)) == (ssize_t)sizeof(tail));
                assert(__real_close(writer) == 0);
            }
            if (edge == SWAP_PATH) {
                assert(rename(test_path, old_path) == 0);
                assert(symlink(target_path, test_path) == 0);
            }
        }
    }
    return fortified ? __real___read_chk(fd, bytes, n, object_size) : __real_read(fd, bytes, n);
}
ssize_t __wrap_read(int fd, void* bytes, size_t n) {
    return checked_read(fd, bytes, n, 0, 0);
}
ssize_t __wrap___read_chk(int fd, void* bytes, size_t n, size_t object_size) {
    return checked_read(fd, bytes, n, 1, object_size);
}
static void put_file(const char* path, const uint8_t* bytes, size_t n) {
    int fd = __real_open(path, O_CREAT | O_TRUNC | O_WRONLY, 0600);
    assert(fd >= 0);
    size_t done = 0;
    while (done < n) { ssize_t count = write(fd, bytes + done, n - done); assert(count > 0); done += (size_t)count; }
    assert(__real_close(fd) == 0);
}
static int64_t invoke(int binary, const char* path, uint64_t path_len, int64_t limit, enum Edge inject) {
    edge = inject; fired = 0; watched_fd = -1; fd_balance = 0; buffer_freed = 0;
    read_buffer = NULL; first_alloc = largest_alloc = max_request = allocations = reallocations = 0;
    active = 1;
    int64_t result = binary
        ? rt_file_read_regular_no_follow_bounded_bytes((const uint8_t*)path, path_len, limit)
        : rt_file_read_regular_no_follow_bounded((const uint8_t*)path, path_len, limit);
    active = 0;
    assert(fd_balance == 0 && watched_fd == -1);
    assert(!read_buffer || buffer_freed);
    return result;
}
static void content(int binary, int64_t result, const uint8_t* expected, size_t n) {
    assert(result != 3);
    int64_t length = binary ? rt_array_bytes_basis_len((SplArray*)(uintptr_t)result) : rt_string_len(result);
    const uint8_t* bytes = binary ? (const uint8_t*)(uintptr_t)rt_array_bytes_basis_ptr((SplArray*)(uintptr_t)result) : rt_string_data(result);
    assert(length == (int64_t)n);
    assert(n == 0 || (bytes && memcmp(bytes, expected, n) == 0));
    assert(rt_file_read_regular_no_follow_last_failure() == 100);
    if (binary) rt_array_free((SplArray*)(uintptr_t)result); else assert(rt_string_free(result) == (n > 1 ? 1 : 0));
    cases++;
}
static void rejected(int64_t result, int expected) {
    assert(result == 3);
    assert(rt_file_read_regular_no_follow_last_failure() == expected);
    cases++;
}
static void paths(const char* dir) {
    assert(snprintf(test_path, sizeof(test_path), "%s/read.bin", dir) < (int)sizeof(test_path));
    assert(snprintf(old_path, sizeof(old_path), "%s/opened.bin", dir) < (int)sizeof(old_path));
    assert(snprintf(target_path, sizeof(target_path), "%s/target.bin", dir) < (int)sizeof(target_path));
}
static void logic(const char* dir, int bounded) {
    const uint8_t initial[] = {'a', 0, 'b', 'c'};
    const uint8_t target[] = {'z', 'z', 'z'};
    uint8_t grown[sizeof(initial) + sizeof(tail)];
    memcpy(grown, initial, sizeof(initial)); memcpy(grown + sizeof(initial), tail, sizeof(tail));
    paths(dir);
    for (int binary = 0; binary < 2; binary++) {
        put_file(test_path, initial, sizeof(initial));
        content(binary, invoke(binary, test_path, strlen(test_path), sizeof(initial), NORMAL), initial, sizeof(initial));
        rejected(invoke(binary, test_path, strlen(test_path), sizeof(initial) - 1, NORMAL), 5);
        rejected(invoke(binary, test_path, strlen(test_path), -1, NORMAL), 2);
        rejected(invoke(binary, test_path, 0, 4, NORMAL), 2);
        rejected(invoke(binary, NULL, 1, 4, NORMAL), 2);
        rejected(invoke(binary, dir, strlen(dir), 16, NORMAL), 5);
        rejected(invoke(binary, test_path, strlen(test_path), 16, STAT_ERROR), 5);
        rejected(invoke(binary, test_path, strlen(test_path), 16, READ_ERROR), 9);
        rejected(invoke(binary, test_path, strlen(test_path), 16, ALLOC_ERROR), 9);
        content(binary, invoke(binary, test_path, strlen(test_path), 16, INTERRUPT), initial, sizeof(initial));
        assert(fired);
        content(binary, invoke(binary, test_path, strlen(test_path), sizeof(grown), GROW), grown, sizeof(grown));
        if (bounded) assert(reallocations > 0);
        put_file(test_path, initial, sizeof(initial));
        rejected(invoke(binary, test_path, strlen(test_path), sizeof(initial), GROW), 7);
        put_file(test_path, initial, sizeof(initial));
        if (bounded) {
            rejected(invoke(binary, test_path, strlen(test_path), sizeof(grown), GROW_ALLOC_ERROR), 9);
            assert(reallocations == 1);
            put_file(test_path, initial, sizeof(initial));
        }
        content(binary, invoke(binary, test_path, strlen(test_path), 16, SHRINK), NULL, 0);
        put_file(test_path, NULL, 0);
        content(binary, invoke(binary, test_path, strlen(test_path), 0, NORMAL), NULL, 0);
        rejected(invoke(binary, test_path, strlen(test_path), 0, GROW), 7);
        put_file(test_path, initial, sizeof(initial));
        assert(chmod(test_path, 0000) == 0);
        assert(geteuid() != 0); /* Permission denial needs an unprivileged test owner. */
        rejected(invoke(binary, test_path, strlen(test_path), 16, NORMAL), 4);
        assert(chmod(test_path, 0600) == 0);
        put_file(target_path, target, sizeof(target));
        content(binary, invoke(binary, test_path, strlen(test_path), 16, SWAP_PATH), initial, sizeof(initial));
        rejected(invoke(binary, test_path, strlen(test_path), 16, NORMAL), 4);
        assert(unlink(test_path) == 0); assert(rename(old_path, test_path) == 0);
        if (bounded) {
            content(binary, invoke(binary, test_path, strlen(test_path), INT64_MAX, NORMAL), initial, sizeof(initial));
            assert(first_alloc == sizeof(initial) + 1 && max_request <= sizeof(initial) + 1);
        }
        assert(unlink(test_path) == 0);
        rejected(invoke(binary, test_path, strlen(test_path), 16, NORMAL), 4);
    }
    assert(unlink(target_path) == 0);
    printf("PASS cases=%u nofollow growth oversize EINTR NUL cleanup allocation-failure\n", cases);
}
static uint64_t clock_ns(void) { struct timespec t; assert(clock_gettime(CLOCK_MONOTONIC, &t) == 0); return (uint64_t)t.tv_sec * 1000000000 + t.tv_nsec; }
static long rss_kib(void) {
    FILE* f = fopen("/proc/self/status", "r"); assert(f); char line[256]; long n = 0;
    while (fgets(line, sizeof(line), f)) if (sscanf(line, "VmRSS: %ld kB", &n) == 1) break;
    fclose(f); return n;
}
int main(int argc, char** argv) {
    assert(argc >= 4);
    if (strcmp(argv[1], "logic") == 0) { logic(argv[2], strcmp(argv[3], "bounded") == 0); return 0; }
    assert(strcmp(argv[1], "bench") == 0 && argc == 6);
    paths(argv[2]); size_t n = strtoull(argv[3], NULL, 10); int64_t limit = strtoll(argv[4], NULL, 10); int iterations = atoi(argv[5]);
    assert(iterations > 0 && iterations <= 100 && n <= 64 * 1024 * 1024);
    uint8_t* expected = malloc(n ? n : 1); assert(expected);
    for (size_t i = 0; i < n; i++) expected[i] = (uint8_t)(i * 37);
    put_file(test_path, expected, n);
    long before = rss_kib(); uint64_t start = clock_ns(); size_t peak_request = 0, peak_allocation = 0;
    for (int i = 0; i < iterations; i++) {
        content(1, invoke(1, test_path, strlen(test_path), limit, NORMAL), expected, n);
        if (max_request > peak_request) peak_request = max_request;
        if (largest_alloc > peak_allocation) peak_allocation = largest_alloc;
    }
    uint64_t elapsed = clock_ns() - start; long after = rss_kib();
    assert(unlink(test_path) == 0); free(expected);
    printf("{\"bytes\":%zu,\"limit\":%" PRId64 ",\"iterations\":%d,\"elapsed_ns\":%" PRIu64 ",\"max_read_request\":%zu,\"max_malloc_request\":%zu,\"rss_before_KiB\":%ld,\"rss_after_KiB\":%ld,\"asserted_reads\":%u}\n", n, limit, iterations, elapsed, peak_request, peak_allocation, before, after, cases);
    return 0;
}
