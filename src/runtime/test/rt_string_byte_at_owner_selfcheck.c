/* Counted text data borrows must use their live owner's length. Foreign C
 * buffers keep the NUL-terminated fallback, including subsequent mutations.
 * BYTE_AT_RUNTIME_SOURCE is an explicit diagnostic baseline source override. */
#ifndef BYTE_AT_RUNTIME_SOURCE
#define BYTE_AT_RUNTIME_SOURCE "../runtime_native.c"
#endif
#include BYTE_AT_RUNTIME_SOURCE
#include <assert.h>
#include <limits.h>
#include <time.h>
#ifndef _WIN32
#include <sys/resource.h>
#include <sys/mman.h>
#endif

static int64_t (*volatile byte_at_abi)(int64_t, int64_t) = __simple_rt_string_byte_at;

static void check_counted_and_foreign(void) {
    static const uint8_t bytes[] = {'a', 0, 0xc3, 0xa9, 'z'};
    int64_t owned = rt_string_new(bytes, sizeof(bytes));
    int64_t raw = (int64_t)(uintptr_t)rt_string_data(owned);
    assert(rt_core_string_from_data_pointer(raw) != NULL);
    for (int64_t i = 0; i < (int64_t)sizeof(bytes); i++) {
        assert(byte_at_abi(owned, i) == bytes[i]);
        assert(byte_at_abi(raw, i) == bytes[i]);
    }
    assert(byte_at_abi(raw, -1) == 0);
    assert(byte_at_abi(raw, sizeof(bytes)) == 0);
    assert(byte_at_abi(raw, INT64_MAX) == 0);
    int64_t empty = rt_string_new(bytes, 0);
    assert(byte_at_abi(empty, 0) == 0);
    assert(byte_at_abi((int64_t)(uintptr_t)rt_string_data(empty), 0) == 0);
    /* May be the shared empty singleton; both ownership cases permit release. */
    (void)rt_string_free(empty);

    /* No header read before registry admission for foreign/unaligned data. */
    char foreign[] = {'a', 0, 'b', 0};
    int64_t cstr = (int64_t)(uintptr_t)foreign;
    assert(rt_core_string_from_data_pointer(cstr) == NULL);
    assert(byte_at_abi(cstr, 2) == 0);
    foreign[1] = 'x';
    assert(byte_at_abi(cstr, 2) == 'b');
    foreign[1] = 0;
    assert(byte_at_abi(cstr, 2) == 0);
    assert(byte_at_abi(cstr + 2, 0) == 'b');
    assert(byte_at_abi(cstr, -1) == 0);
    assert(byte_at_abi(0, 0) == 0);

#ifndef _WIN32
    /* The candidate owner header lies in an unreadable page. A foreign data
     * pointer must fail registry admission before any header dereference. */
    long page = sysconf(_SC_PAGESIZE);
    assert(page > 0);
    uint8_t *guarded = mmap(NULL, (size_t)page * 2, PROT_READ | PROT_WRITE,
                            MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
    assert(guarded != MAP_FAILED);
    assert(mprotect(guarded, (size_t)page, PROT_NONE) == 0);
    uint8_t *foreign_page = guarded + page;
    foreign_page[0] = 'q'; foreign_page[1] = 0;
    int64_t guarded_raw = (int64_t)(uintptr_t)foreign_page;
    assert(rt_core_string_from_data_pointer(guarded_raw) == NULL);
    assert(byte_at_abi(guarded_raw, 0) == 'q');
    assert(byte_at_abi(guarded_raw, 1) == 0);
    assert(munmap(guarded, (size_t)page * 2) == 0);
#endif

    /* Check registry retirement only; never dereference the freed data. */
    int64_t retired = rt_string_new((const uint8_t*)"retired-owner", 13);
    int64_t retired_raw = (int64_t)(uintptr_t)rt_string_data(retired);
    assert(rt_core_string_from_data_pointer(retired_raw) != NULL);
    assert(rt_string_free(retired) == 1);
    assert(rt_core_string_from_data_pointer(retired_raw) == NULL);
    assert(rt_string_free(owned) == 1);
}

#ifndef _WIN32
static uint64_t monotonic_ns(void) {
    struct timespec ts;
    assert(clock_gettime(CLOCK_MONOTONIC, &ts) == 0);
    return (uint64_t)ts.tv_sec * 1000000000ull + ts.tv_nsec;
}
static int u64_order(const void *a, const void *b) {
    uint64_t x = *(const uint64_t*)a, y = *(const uint64_t*)b;
    return (x > y) - (x < y);
}
static void benchmark(void) {
    const size_t sizes[] = {65536, 131072, 262144};
    for (size_t s = 0; s < 3; s++) {
        size_t n = sizes[s];
        uint8_t *input = malloc(n);
        assert(input != NULL);
        memset(input, 'x', n);
        int64_t owned = rt_string_new(input, n);
        int64_t raw = (int64_t)(uintptr_t)rt_string_data(owned);
        free(input);
        uint64_t samples[5];
        for (size_t repeat = 0; repeat < 5; repeat++) {
            uint64_t started = monotonic_ns();
            int64_t sum = 0;
            for (size_t i = 0; i < n; i++) sum += byte_at_abi(raw, i);
            samples[repeat] = monotonic_ns() - started;
            assert(sum == (int64_t)n * 'x');
        }
        qsort(samples, 5, sizeof(samples[0]), u64_order);
        struct rusage usage;
        assert(getrusage(RUSAGE_SELF, &usage) == 0);
        printf("n=%zu p50_ns=%llu p95_ns=%llu peak_rss_native=%lld\n", n,
               (unsigned long long)samples[2], (unsigned long long)samples[4],
               (long long)usage.ru_maxrss);
        assert(rt_string_free(owned) == 1);
    }
}
#endif

int main(int argc, char **argv) {
#ifndef _WIN32
    if (argc == 2 && strcmp(argv[1], "--bench") == 0) { benchmark(); return 0; }
#endif
    check_counted_and_foreign();
    puts("PASS rt_string_byte_at counted owner, ABI wrapper, bounds, foreign mutation and retirement");
    return 0;
}
