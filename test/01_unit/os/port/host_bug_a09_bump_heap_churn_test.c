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

typedef struct {
    long ticks;
    size_t retained_committed;
} LatencySample;

static int measure_allocator_latency(size_t live_count, LatencySample *sample)
{
    uint8_t *live[24];
    if (live_count > 24) return 0;
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
    LatencySample latency_24;
    if (!measure_allocator_latency(8, &latency_8) || !measure_allocator_latency(24, &latency_24)) return 19;

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
    free(coalesced);
    free(coalesced);     /* double free is ignored */
    if (!intact(third, 1024, 99)) return 9;
    free(third);

    uint8_t *grown = (uint8_t *)malloc(64);
    if (!grown) return 10;
    fill(grown, 64, 17);
    grown = (uint8_t *)realloc(grown, 128);
    if (!grown || !intact(grown, 64, 17)) return 11;
    free(grown);

    for (size_t i = 0; i < LIVE_COUNT; ++i) {
        if (!intact(live[i], LIVE_BYTES, (uint8_t)i)) return 12;
        free(live[i]);
    }
    int final_status = rt_baremetal_heap_test_high_water() == 0 ? 0 : 13;

    pthread_t workers[2];
    if (pthread_create(&workers[0], 0, concurrent_allocator_worker, (void *)1) != 0 ||
        pthread_create(&workers[1], 0, concurrent_allocator_worker, (void *)2) != 0) return 17;
    if (pthread_join(workers[0], 0) != 0 || pthread_join(workers[1], 0) != 0 || worker_failed) return 18;
    printf("allocator_latency live_blocks=8 operations=20000 cpu_ticks=%ld retained_committed_bytes=%zu\n",
           latency_8.ticks, latency_8.retained_committed);
    printf("allocator_latency live_blocks=24 operations=20000 cpu_ticks=%ld retained_committed_bytes=%zu\n",
           latency_24.ticks, latency_24.retained_committed);
    printf("churn_live_blocks=%u peak_committed_bytes=%zu live_bytes=%u\n",
           (unsigned)LIVE_COUNT, peak_high_water, (unsigned)(LIVE_COUNT * LIVE_BYTES));
    return final_status;
}
