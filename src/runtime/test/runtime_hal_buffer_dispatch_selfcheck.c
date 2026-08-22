#include "../runtime_hal_buffer_dispatch.h"

#include <stdint.h>
#include <stdio.h>
#include <string.h>
#include <sys/resource.h>
#include <time.h>

static uint64_t fake_owner_calls;

static int32_t fake_owner(
        int64_t op, int64_t fixture, int32_t status, int32_t domain,
        int64_t code, int64_t detail, const uint8_t *captured, int64_t length,
        uint8_t *output, int64_t capacity, int64_t hi, int64_t lo,
        int64_t cursor, int64_t trace_length, int64_t trace_capacity) {
    (void)op; (void)fixture; (void)status; (void)domain; (void)code;
    (void)detail; (void)hi; (void)lo; (void)cursor; (void)trace_length;
    (void)trace_capacity;
    ++fake_owner_calls;
    if (!captured || !output || length < 0 || length > capacity) return 1;
    if (length > 0) memmove(output, captured, (size_t)length);
    return 0;
}

static uint64_t nanos(void) {
    struct timespec ts;
    (void)clock_gettime(CLOCK_MONOTONIC, &ts);
    return (uint64_t)ts.tv_sec * UINT64_C(1000000000) + (uint64_t)ts.tv_nsec;
}

static long rss_kib(void) {
    struct rusage usage;
    (void)getrusage(RUSAGE_SELF, &usage);
#ifdef __APPLE__
    return usage.ru_maxrss / 1024;
#else
    return usage.ru_maxrss;
#endif
}

int main(void) {
    uint8_t input[32], output[32];
    uint64_t start, direct_elapsed, configured_elapsed, compare_elapsed;
    long rss_before, rss_after;
    int i;
    memset(input, 0x5a, sizeof(input));
    memset(output, 0xa5, sizeof(output));
    if (rt_hal_buffer_dispatch_direct_v3(1001, 1, 0, 0, 0, 0,
            input, 32, output, 32, 1, 2, 0, 1, 1) != 0) return 1;
    if (memcmp(input, output, sizeof(input)) != 0) return 2;
    memset(output, 0xa5, sizeof(output));
    if (rt_hal_buffer_dispatch_direct_v3(1001, 1, 9, 2, 7, 0,
            input, 32, output, 32, 1, 2, 0, 1, 1) != 3) return 3;
    if (output[0] != 0xa5) return 4;
    if (rt_hal_buffer_dispatch_direct_v3(1001, 1, 0, 0, 0, 0,
            input, 32, output, 32, 0, 2, 0, 1, 1) != 1) return 5;
    if (output[0] != 0xa5) return 6;
    if (rt_hal_buffer_dispatch_direct_v3(1012, 1, 0, 0, 0, 0,
            input, 32, output, 32, 1, 2, 0, 2, 2) != 1) return 21;
    if (output[0] != 0xa5) return 22;
    if (rt_hal_buffer_dispatch_compare_v3(1001, 1, 0, 0, 0, 0,
            input, 32, output, 32, 1, 2, 0, 1, 1) != 1) return 7;
    if (output[0] != 0xa5) return 8;
    rss_before = rss_kib();
    start = nanos();
    for (i = 0; i < 1000000; ++i)
        if (rt_hal_buffer_dispatch_direct_v3(1001, 1, 0, 0, 0, 0,
                input, 32, output, 32, 1, 2, 0, 1, 1) != 0)
            return 7;
    direct_elapsed = nanos() - start;
    if (rt_hal_buffer_dispatch_bind_owner_v3(fake_owner, 2, 1) != 0) return 8;
    if (rt_hal_buffer_dispatch_mode_v3() != 2 ||
        rt_hal_buffer_dispatch_provider_v3() != 1) return 9;
    start = nanos();
    for (i = 0; i < 1000000; ++i)
        if (rt_hal_buffer_dispatch_configured_v3(1012, 1, 0, 0, 0, 0,
                input, 32, output, 32, 1, 2, 0, 1, 1) != 0)
            return 10;
    configured_elapsed = nanos() - start;
    if (fake_owner_calls != 0) return 11;
    if (rt_hal_buffer_dispatch_configured_v3(1008, 1, 0, 0, 0, 0,
            input, 32, output, 32, 1, 2, 0, 1, 1) != 1) return 23;
    if (rt_hal_buffer_dispatch_unbind_owner_v3() != 0) return 12;
    if (rt_hal_buffer_dispatch_bind_owner_v3(fake_owner, 0, 1) != 0) return 13;
    start = nanos();
    for (i = 0; i < 1000000; ++i)
        if (rt_hal_buffer_dispatch_compare_v3(1001, 1, 0, 0, 0, 0,
                input, 32, output, 32, 1, 2, 0, 1, 1) != 0)
            return 14;
    compare_elapsed = nanos() - start;
    rss_after = rss_kib();
    if (fake_owner_calls != 1000000) return 15;
    if (memcmp(input, output, sizeof(input)) != 0) return 16;
    if (rt_hal_buffer_dispatch_hot_allocation_count_v3() != 0) return 17;
    if (rss_after > rss_before + 1024) return 18;
    if (direct_elapsed >= compare_elapsed) return 19;
    if (rt_hal_buffer_dispatch_unbind_owner_v3() != 0) return 20;
    printf("runtime_hal_buffer_v3 calls=1000000 direct_ns_per_call=%llu configured_normal_ns_per_call=%llu compare_ns_per_call=%llu rss_before_kib=%ld rss_after_kib=%ld hot_allocations=0\n",
           (unsigned long long)(direct_elapsed / 1000000),
           (unsigned long long)(configured_elapsed / 1000000),
           (unsigned long long)(compare_elapsed / 1000000),
           rss_before, rss_after);
    return 0;
}
