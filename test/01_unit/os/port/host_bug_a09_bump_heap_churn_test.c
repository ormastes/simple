#include <stdint.h>
#include <stddef.h>
#include <stdio.h>
#include <time.h>
#include <pthread.h>

extern void *malloc(size_t size);
extern void free(void *ptr);
extern void *calloc(size_t count, size_t size);
extern void *realloc(void *ptr, size_t size);
extern void rt_baremetal_heap_test_reset(void);
extern size_t rt_baremetal_heap_test_capacity(void);
extern size_t rt_baremetal_heap_test_high_water(void);

#ifndef HOST_BUG_A09_LIVE_COUNT
#define HOST_BUG_A09_LIVE_COUNT 24
#endif

static void fill(uint8_t *bytes, size_t count, uint8_t value)
{
    for (size_t i = 0; i < count; ++i) bytes[i] = (uint8_t)(value + i);
}

static int intact(const uint8_t *bytes, size_t count, uint8_t value)
{
    for (size_t i = 0; i < count; ++i)
        if (bytes[i] != (uint8_t)(value + i)) return 0;
    return 1;
}

static volatile int worker_failed = 0;
static unsigned long clear_calls;
static unsigned long locked_clear_calls;
static size_t largest_clear;

void rt_baremetal_heap_test_payload_clear(size_t size, unsigned int lock_owned)
{
    __atomic_fetch_add(&clear_calls, 1UL, __ATOMIC_RELAXED);
    if (lock_owned) __atomic_fetch_add(&locked_clear_calls, 1UL, __ATOMIC_RELAXED);
    size_t observed = __atomic_load_n(&largest_clear, __ATOMIC_RELAXED);
    while (size > observed && !__atomic_compare_exchange_n(
        &largest_clear, &observed, size, 0, __ATOMIC_RELAXED, __ATOMIC_RELAXED)) {}
}

static int all_zero(const uint8_t *bytes, size_t count)
{
    for (size_t i = 0; i < count; ++i) if (bytes[i] != 0) return 0;
    return 1;
}

typedef struct {
    long ticks;
    size_t retained_committed;
} LatencySample;

static int measure_allocator_latency(size_t live_count, LatencySample *sample)
{
    static uint8_t *live[4096];
    if (live_count > 4096) return 0;
    for (size_t i = 0; i < live_count; ++i) {
        live[i] = (uint8_t *)malloc(64);
        if (!live[i]) return 0;
    }
    clock_t start = clock();
    for (size_t i = 0; i < 20000; ++i) {
        void *block = malloc(64);
        if (!block) return 0;
        free(block);
    }
    sample->ticks = (long)(clock() - start);
    sample->retained_committed = rt_baremetal_heap_test_high_water();
    for (size_t i = 0; i < live_count; ++i) free(live[i]);
    return rt_baremetal_heap_test_high_water() == 0;
}

static int measure_fragmented_allocator_latency(LatencySample *sample)
{
    static uint8_t *live[4096];
    uint8_t *small_hole = (uint8_t *)malloc(16);
    if (!small_hole) return 0;
    for (size_t i = 0; i < 4096; ++i) {
        live[i] = (uint8_t *)malloc(64);
        if (!live[i]) return 0;
    }
    free(small_hole);
    clock_t start = clock();
    for (size_t i = 0; i < 20000; ++i) {
        void *block = malloc(128);
        if (!block) return 0;
        free(block);
    }
    sample->ticks = (long)(clock() - start);
    sample->retained_committed = rt_baremetal_heap_test_high_water();
    for (size_t i = 0; i < 4096; ++i) free(live[i]);
    return rt_baremetal_heap_test_high_water() == 0;
}

static void *concurrent_allocator_worker(void *arg)
{
    uintptr_t seed = (uintptr_t)arg;
    for (size_t i = 0; i < 2000; ++i) {
        uint8_t *block = (uint8_t *)malloc(256 + ((i + seed) & 15U));
        if (!block) { worker_failed = 1; return 0; }
        fill(block, 256, (uint8_t)(i + seed));
        if (!intact(block, 256, (uint8_t)(i + seed))) { worker_failed = 1; return 0; }
        free(block);
    }
    return 0;
}

int main(void)
{
    enum {
        LIVE_COUNT = HOST_BUG_A09_LIVE_COUNT, LIVE_BYTES = 1024 * 1024, CHURN_BYTES = 2 * 1024 * 1024,
        TAIL_INITIAL_BYTES = 100 * 1024 * 1024, TAIL_GROWN_BYTES = 110 * 1024 * 1024
    };
    uint8_t *live[LIVE_COUNT];
    volatile size_t overflow = (size_t)-1;
    rt_baremetal_heap_test_reset();
    LatencySample latency_8;
    LatencySample latency_4096;
    LatencySample latency_fragmented;
    if (!measure_allocator_latency(8, &latency_8) ||
        !measure_allocator_latency(4096, &latency_4096) ||
        !measure_fragmented_allocator_latency(&latency_fragmented)) return 19;
    /* The retired first-fit implementation scanned every live block while
     * IRQs were masked. A 4096-block session must keep churn latency bounded,
     * not scale linearly with the retained object count. */
    if (latency_4096.ticks > (latency_8.ticks + 100) * 8) {
        fprintf(stderr, "allocator_latency_regression live8_ticks=%ld live4096_ticks=%ld\n",
                latency_8.ticks, latency_4096.ticks);
        return 20;
    }
    if (latency_fragmented.ticks > (latency_8.ticks + 100) * 8) {
        fprintf(stderr, "allocator_fragmentation_latency_regression live8_ticks=%ld fragmented_ticks=%ld\n",
                latency_8.ticks, latency_fragmented.ticks);
        return 28;
    }

    for (size_t i = 0; i < LIVE_COUNT; ++i) {
        live[i] = (uint8_t *)malloc(LIVE_BYTES);
        if (!live[i] || ((uintptr_t)live[i] & 15U) != 0U) return 2;
        fill(live[i], LIVE_BYTES, (uint8_t)i);
    }

    /* 100 * 2 MiB exceeds the complete arena while only 24 MiB stays live. */
    for (size_t round = 0; round < 100; ++round) {
        uint8_t *scratch = (uint8_t *)malloc(CHURN_BYTES);
        if (!scratch) return 3;
        fill(scratch, CHURN_BYTES, (uint8_t)round);
        if (!intact(scratch, CHURN_BYTES, (uint8_t)round)) return 4;
        for (size_t i = 0; i < LIVE_COUNT; ++i)
            if (!intact(live[i], LIVE_BYTES, (uint8_t)i)) return 5;
        free(scratch);
    }
    if (rt_baremetal_heap_test_high_water() >= rt_baremetal_heap_test_capacity()) return 6;
    if (malloc(0) != 0 || malloc(overflow) != 0 || calloc(overflow, 2) != 0) return 14;

    /* A tail block must grow in place near capacity: moving it would require
     * a second 110 MiB block although the final 110 MiB allocation fits. */
    uint8_t *tail = (uint8_t *)malloc(TAIL_INITIAL_BYTES);
    if (!tail) return 15;
    fill(tail, TAIL_INITIAL_BYTES, 61);
    uint8_t *tail_grown = (uint8_t *)realloc(tail, TAIL_GROWN_BYTES);
    if (tail_grown != tail || !intact(tail_grown, TAIL_INITIAL_BYTES, 61)) return 16;
    if (!all_zero(tail_grown + TAIL_INITIAL_BYTES,
                  TAIL_GROWN_BYTES - TAIL_INITIAL_BYTES)) return 29;
    size_t peak_high_water = rt_baremetal_heap_test_high_water();
    free(tail_grown);

    uint8_t *first = (uint8_t *)malloc(1024);
    uint8_t *second = (uint8_t *)malloc(1024);
    uint8_t *third = (uint8_t *)malloc(1024);
    if (!first || !second || !third) return 7;
    fill(third, 1024, 99);
    free(first);
    free(second);
    uint8_t *coalesced = (uint8_t *)malloc(1536);
    if (coalesced != first) return 8;
    free((void *)(uintptr_t)((uintptr_t)coalesced + 1U)); /* invalid pointer must not change adjacent live data */
    uintptr_t released_address = (uintptr_t)coalesced;
    free(coalesced);
    free((void *)released_address); /* double free is ignored */
    if (!intact(third, 1024, 99)) return 9;
    free(third);

    uint8_t *left = (uint8_t *)malloc(256);
    uint8_t *middle = (uint8_t *)malloc(512);
    uint8_t *right = (uint8_t *)malloc(256);
    if (!left || !middle || !right) return 21;
    fill(left, 256, 31);
    fill(middle, 512, 63);
    fill(right, 256, 47);
    free(middle);
    uint8_t *left_grown = (uint8_t *)realloc(left, 640);
    if (left_grown != left || !intact(left_grown, 256, 31) || !intact(right, 256, 47)) return 22;
    if (!all_zero(left_grown + 256, 640 - 256)) return 30;
    free(left_grown);
    free(right);

    uint8_t *dirty = (uint8_t *)malloc(4096);
    if (!dirty) return 25;
    fill(dirty, 4096, 73);
    free(dirty);
    uint8_t *fresh = (uint8_t *)malloc(4096);
    if (!fresh) return 26;
    for (size_t i = 0; i < 4096; ++i)
        if (fresh[i] != 0) return 27;
    free(fresh);

    unsigned long calls_before_calloc = clear_calls;
    uint8_t *zeroed = (uint8_t *)calloc(4096, 4);
    if (!zeroed) return 23;
    if (clear_calls != calls_before_calloc + 1) return 31;
    for (size_t i = 0; i < 4096 * 4; ++i)
        if (zeroed[i] != 0) return 24;
    free(zeroed);

    uint8_t *grown = (uint8_t *)malloc(64);
    if (!grown) return 10;
    uint8_t *growth_blocker = (uint8_t *)malloc(64);
    if (!growth_blocker) return 32;
    fill(growth_blocker, 64, 55);
    fill(grown, 64, 17);
    grown = (uint8_t *)realloc(grown, 128);
    if (!grown || !intact(grown, 64, 17)) return 11;
    if (!all_zero(grown + 64, 64) || !intact(growth_blocker, 64, 55)) return 33;
    free(grown);
    free(growth_blocker);

    uint8_t *null_grown = (uint8_t *)realloc(NULL, 4096);
    if (!null_grown || !all_zero(null_grown, 4096)) return 34;
    free(null_grown);

    for (size_t i = 0; i < LIVE_COUNT; ++i) {
        if (!intact(live[i], LIVE_BYTES, (uint8_t)i)) return 12;
        free(live[i]);
    }
    int final_status = rt_baremetal_heap_test_high_water() == 0 ? 0 : 13;

    pthread_t workers[2];
    if (pthread_create(&workers[0], 0, concurrent_allocator_worker, (void *)1) != 0 ||
        pthread_create(&workers[1], 0, concurrent_allocator_worker, (void *)2) != 0) return 17;
    if (pthread_join(workers[0], 0) != 0 || pthread_join(workers[1], 0) != 0 || worker_failed) return 18;
    if (locked_clear_calls != 0 || largest_clear < TAIL_INITIAL_BYTES) return 35;
    printf("payload_clear calls=%lu locked_calls=%lu largest_bytes=%zu\n",
           clear_calls, locked_clear_calls, largest_clear);
    printf("allocator_latency live_blocks=8 operations=20000 cpu_ticks=%ld retained_committed_bytes=%zu\n",
           latency_8.ticks, latency_8.retained_committed);
    printf("allocator_latency live_blocks=4096 operations=20000 cpu_ticks=%ld retained_committed_bytes=%zu\n",
           latency_4096.ticks, latency_4096.retained_committed);
    printf("allocator_latency fragmented_live_blocks=4096 operations=20000 cpu_ticks=%ld retained_committed_bytes=%zu\n",
           latency_fragmented.ticks, latency_fragmented.retained_committed);
    printf("churn_live_blocks=%u peak_committed_bytes=%zu live_bytes=%u\n",
           (unsigned)LIVE_COUNT, peak_high_water, (unsigned)(LIVE_COUNT * LIVE_BYTES));
    return final_status;
}
