#include "../runtime_hal_buffer_dispatch.h"

#include <stdatomic.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>
#include <sys/resource.h>
#include <threads.h>
#include <time.h>

static _Atomic int owner_entered;
static _Atomic int owner_release;
static uint64_t nanos(void);

static int32_t blocking_owner(
        int64_t op, int64_t fixture, int32_t status, int32_t domain,
        int64_t code, int64_t detail, const uint8_t *captured, int64_t length,
        uint8_t *output, int64_t capacity, int64_t hi, int64_t lo,
        int64_t cursor, int64_t trace_length, int64_t trace_capacity) {
    uint64_t deadline;
    (void)op; (void)fixture; (void)status; (void)domain; (void)code;
    (void)detail; (void)hi; (void)lo; (void)cursor; (void)trace_length;
    (void)trace_capacity;
    atomic_fetch_add_explicit(&owner_entered, 1, memory_order_acq_rel);
    deadline = nanos() + UINT64_C(2000000000);
    while (!atomic_load_explicit(&owner_release, memory_order_acquire)) {
        if (nanos() > deadline) return 1;
        thrd_yield();
    }
    if (!captured || !output || length < 0 || length > capacity) return 1;
    if (length > 0) memmove(output, captured, (size_t)length);
    return 0;
}

typedef struct ThreadCall {
    uint8_t input[8];
    uint8_t output[8];
    int64_t fixture;
    int64_t identity_hi;
    int64_t identity_lo;
    int32_t status;
} ThreadCall;

static int run_blocked_compare(void *raw) {
    ThreadCall *call = (ThreadCall *)raw;
    call->status = rt_hal_process_wait_dispatch_compare_v4(
        call->fixture, 0, 0, 0, 0, call->input, 8, call->output, 8,
        call->identity_hi, call->identity_lo, 1, 2, 8);
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
    uint8_t input[8], output[8];
    ThreadCall threaded, distinct_a, distinct_b;
    thrd_t worker, worker_a, worker_b;
    uint64_t start, elapsed, deadline;
    long rss_before, rss_after;
    int i;
    memset(input, 0x5a, sizeof(input));
    memset(output, 0xa5, sizeof(output));

    /* Before init and invalid init fail without touching caller output. */
    if (rt_hal_process_wait_dispatch_direct_v4(1, 0, 0, 0, 0,
            input, 8, output, 8, 11, 12, 1, 2, 8) != 1) return 1;
    if (output[0] != 0xa5) return 2;
    if (rt_hal_process_socket_lifecycle_init_v4(0) != 1) return 3;
    if (rt_hal_process_socket_lifecycle_init_v4(8) != 0) return 4;
    if (rt_hal_process_socket_lifecycle_init_v4(8) != 1) return 5;

    if (rt_hal_process_socket_register_spawn_v4(
            101, 1, 11, 12, 0, 1, 8) != 0) return 6;
    if (rt_hal_process_wait_dispatch_direct_v4(101, 0, 0, 0, 0,
            input, 8, output, 8, 11, 12, 1, 2, 8) != 0) return 7;
    if (memcmp(input, output, sizeof(input)) != 0) return 8;
    memset(output, 0xa5, sizeof(output));
    if (rt_hal_process_wait_dispatch_direct_v4(101, 0, 0, 0, 0,
            input, 8, output, 8, 11, 12, 1, 2, 8) != 1) return 9;
    if (output[0] != 0xa5) return 10;

    /* Failed dispatch poisons the generation and commits no caller bytes. */
    if (rt_hal_process_socket_register_spawn_v4(
            102, 1, 21, 22, 0, 1, 8) != 0) return 11;
    if (rt_hal_process_wait_dispatch_direct_v4(102, 9, 2, 7, 0,
            input, 8, output, 8, 21, 22, 1, 2, 8) != 3) return 12;
    if (output[0] != 0xa5) return 13;
    if (rt_hal_process_wait_dispatch_direct_v4(102, 0, 0, 0, 0,
            input, 8, output, 8, 21, 22, 1, 2, 8) != 1) return 14;
    if (rt_hal_process_socket_register_spawn_v4(
            102, 1, 21, 22, 0, 1, 8) != 1) return 15;

    if (rt_hal_process_socket_register_attempt_v4(
            103, 1, 31, 32, 0, 1, 8) != 0) return 16;
    if (rt_hal_socket_connect_dispatch_direct_v4(103, 9, 2, 7, 0,
            input, 8, output, 8, 31, 32, 0, 1, 8) != 3) return 17;
    if (rt_hal_socket_connect_dispatch_direct_v4(103, 0, 0, 0, 0,
            input, 8, output, 8, 31, 32, 0, 1, 8) != 1) return 18;
    if (rt_hal_process_socket_register_attempt_v4(
            103, 2, 41, 42, 0, 1, 8) != 0) return 19;
    if (rt_hal_socket_connect_dispatch_direct_v4(103, 0, 0, 0, 0,
            input, 8, output, 8, 41, 42, 0, 1, 8) != 0) return 20;
    if (rt_hal_socket_connect_dispatch_direct_v4(103, 0, 0, 0, 0,
            input, 8, output, 8, 41, 42, 0, 1, 8) != 1) return 21;

    /* A modulo collision rejects without evicting the resident generation. */
    if (rt_hal_process_socket_register_spawn_v4(
            104, 1, 51, 52, 0, 1, 8) != 0) return 22;
    if (rt_hal_process_socket_register_spawn_v4(
            112, 1, 61, 62, 0, 1, 8) != 1) return 23;
    if (rt_hal_process_wait_dispatch_direct_v4(104, 0, 0, 0, 0,
            input, 8, output, 8, 51, 52, 1, 2, 8) != 0) return 24;

    /* Same-slot concurrency admits exactly one receipt. */
    if (rt_hal_buffer_dispatch_bind_owner_v3(blocking_owner, 0, 1) != 0)
        return 25;
    if (rt_hal_process_socket_register_spawn_v4(
            107, 1, 701, 702, 0, 1, 8) != 0) return 26;
    memset(&threaded, 0, sizeof(threaded));
    memset(threaded.input, 0x77, sizeof(threaded.input));
    memset(threaded.output, 0xa5, sizeof(threaded.output));
    threaded.fixture = 107;
    threaded.identity_hi = 701;
    threaded.identity_lo = 702;
    if (thrd_create(&worker, run_blocked_compare, &threaded) != thrd_success)
        return 27;
    deadline = nanos() + UINT64_C(2000000000);
    while (!atomic_load_explicit(&owner_entered, memory_order_acquire)) {
        if (nanos() > deadline) {
            atomic_store_explicit(&owner_release, 1, memory_order_release);
            (void)thrd_join(worker, NULL);
            return 40;
        }
        thrd_yield();
    }
    if (rt_hal_process_wait_dispatch_compare_v4(107, 0, 0, 0, 0,
            input, 8, output, 8, 701, 702, 1, 2, 8) != 1) return 28;
    atomic_store_explicit(&owner_release, 1, memory_order_release);
    if (thrd_join(worker, NULL) != thrd_success || threaded.status != 0)
        return 29;

    /* Distinct slots execute concurrently without sharing mutable authority. */
    atomic_store_explicit(&owner_entered, 0, memory_order_release);
    atomic_store_explicit(&owner_release, 0, memory_order_release);
    if (rt_hal_process_socket_register_spawn_v4(
            104, 2, 711, 712, 0, 1, 8) != 0) return 35;
    if (rt_hal_process_socket_register_spawn_v4(
            107, 2, 721, 722, 0, 1, 8) != 0) return 36;
    memset(&distinct_a, 0, sizeof(distinct_a));
    memset(&distinct_b, 0, sizeof(distinct_b));
    memset(distinct_a.input, 0x31, sizeof(distinct_a.input));
    memset(distinct_b.input, 0x32, sizeof(distinct_b.input));
    distinct_a.fixture = 104;
    distinct_a.identity_hi = 711;
    distinct_a.identity_lo = 712;
    distinct_b.fixture = 107;
    distinct_b.identity_hi = 721;
    distinct_b.identity_lo = 722;
    if (thrd_create(&worker_a, run_blocked_compare, &distinct_a) != thrd_success)
        return 37;
    if (thrd_create(&worker_b, run_blocked_compare, &distinct_b) != thrd_success)
        return 38;
    deadline = nanos() + UINT64_C(2000000000);
    while (atomic_load_explicit(&owner_entered, memory_order_acquire) != 2) {
        if (nanos() > deadline) {
            atomic_store_explicit(&owner_release, 1, memory_order_release);
            (void)thrd_join(worker_a, NULL);
            (void)thrd_join(worker_b, NULL);
            return 41;
        }
        thrd_yield();
    }
    atomic_store_explicit(&owner_release, 1, memory_order_release);
    if (thrd_join(worker_a, NULL) != thrd_success ||
        thrd_join(worker_b, NULL) != thrd_success ||
        distinct_a.status != 0 || distinct_b.status != 0)
        return 39;
    if (rt_hal_buffer_dispatch_unbind_owner_v3() != 0) return 30;

    rss_before = rss_kib();
    start = nanos();
    for (i = 1; i <= 100000; ++i) {
        if (rt_hal_process_socket_register_spawn_v4(
                105, i, 801 + i, 901 + i, 0, 1, 8) != 0) return 31;
        if (rt_hal_process_wait_dispatch_direct_v4(105, 0, 0, 0, 0,
                input, 8, output, 8, 801 + i, 901 + i, 1, 2, 8) != 0)
            return 32;
    }
    elapsed = nanos() - start;
    rss_after = rss_kib();
    if (rt_hal_process_socket_hot_allocation_count_v4() != 0) return 33;
    if (rss_after > rss_before + 1024) return 34;
    printf("runtime_hal_process_socket_v4 calls=100000 ns_per_register_dispatch=%llu rss_before_kib=%ld rss_after_kib=%ld hot_allocations=0\n",
        (unsigned long long)(elapsed / 100000), rss_before, rss_after);
    return 0;
}
