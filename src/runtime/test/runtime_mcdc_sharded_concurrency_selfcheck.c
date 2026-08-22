#define _POSIX_C_SOURCE 200809L
#include <assert.h>
#include <pthread.h>
#include <stdatomic.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include "../runtime_mcdc_v1.h"

enum { WORKERS = 8, EVENTS_PER_WORKER = 20000 };

static _Atomic int start_workers;
static _Atomic uint64_t allocation_calls;
static _Atomic int count_allocations;

void *__real_malloc(size_t);
void *__real_calloc(size_t, size_t);
void *__real_realloc(void *, size_t);
void __real_free(void *);
void *__wrap_malloc(size_t n) {
    if (atomic_load_explicit(&count_allocations, memory_order_relaxed))
        atomic_fetch_add_explicit(&allocation_calls, 1, memory_order_relaxed);
    return __real_malloc(n);
}
void *__wrap_calloc(size_t n, size_t size) {
    if (atomic_load_explicit(&count_allocations, memory_order_relaxed))
        atomic_fetch_add_explicit(&allocation_calls, 1, memory_order_relaxed);
    return __real_calloc(n, size);
}
void *__wrap_realloc(void *p, size_t n) {
    if (atomic_load_explicit(&count_allocations, memory_order_relaxed))
        atomic_fetch_add_explicit(&allocation_calls, 1, memory_order_relaxed);
    return __real_realloc(p, n);
}
void __wrap_free(void *p) { __real_free(p); }

/* Unused dependency of the coverage object in this focused link. */
int64_t rt_string_new(const uint8_t *bytes, uint64_t len) {
    (void)bytes; (void)len;
    return 0;
}

typedef struct { uint64_t owner_id; } Worker;

static void *record_worker(void *raw) {
    const Worker *worker = (const Worker *)raw;
    while (!atomic_load_explicit(&start_workers, memory_order_acquire)) {}
    for (uint64_t i = 0; i < EVENTS_PER_WORKER; ++i) {
        const int32_t status = rt_mcdc_record_vector_v1(
            77, 100 + worker->owner_id, 2, 900 + worker->owner_id,
            3, i & 3u, worker->owner_id, i, (uint8_t)(i & 1u));
        assert(status == SIMPLE_MCDC_V1_OK);
    }
    return NULL;
}

static uint64_t elapsed_ns(struct timespec start, struct timespec finish) {
    return (uint64_t)(finish.tv_sec - start.tv_sec) * UINT64_C(1000000000) +
           (uint64_t)(finish.tv_nsec - start.tv_nsec);
}

int main(void) {
    const size_t event_count = (size_t)WORKERS * EVENTS_PER_WORKER;
    SimpleMcdcVectorV1 *storage = calloc(event_count, sizeof(*storage));
    SimpleMcdcVectorV1 *snapshot_events = calloc(event_count, sizeof(*snapshot_events));
    assert(storage && snapshot_events);
    assert(rt_mcdc_collector_init_sharded_v1(
               storage, event_count * sizeof(*storage), 77, WORKERS) ==
           SIMPLE_MCDC_V1_OK);

    pthread_t threads[WORKERS];
    Worker workers[WORKERS];
    for (uint64_t i = 0; i < WORKERS; ++i) {
        workers[i].owner_id = i + 1;
        assert(pthread_create(&threads[i], NULL, record_worker, &workers[i]) == 0);
    }
    atomic_store_explicit(&allocation_calls, 0, memory_order_relaxed);
    atomic_store_explicit(&count_allocations, 1, memory_order_release);
    struct timespec start, finish;
    assert(clock_gettime(CLOCK_MONOTONIC, &start) == 0);
    atomic_store_explicit(&start_workers, 1, memory_order_release);
    for (size_t i = 0; i < WORKERS; ++i)
        assert(pthread_join(threads[i], NULL) == 0);
    assert(clock_gettime(CLOCK_MONOTONIC, &finish) == 0);
    atomic_store_explicit(&count_allocations, 0, memory_order_release);

    assert(atomic_load_explicit(&allocation_calls, memory_order_relaxed) == 0);
    assert(rt_mcdc_collector_seal_v1(77) == SIMPLE_MCDC_V1_OK);
    SimpleMcdcSnapshotV1 snapshot;
    assert(rt_mcdc_snapshot_v1(snapshot_events, event_count, &snapshot) ==
           SIMPLE_MCDC_V1_OK);
    assert(snapshot.written == event_count && !snapshot.overflowed);
    uint64_t per_owner[WORKERS] = {0};
    for (size_t i = 0; i < event_count; ++i) {
        assert(snapshot_events[i].owner_id >= 1 &&
               snapshot_events[i].owner_id <= WORKERS);
        ++per_owner[snapshot_events[i].owner_id - 1];
    }
    for (size_t i = 0; i < WORKERS; ++i)
        assert(per_owner[i] == EVENTS_PER_WORKER);

    const uint64_t duration = elapsed_ns(start, finish);
    /* A broad regression tripwire, not a platform performance claim: the
       focused host must sustain at least 50k fully validated probes/second. */
    assert(duration < (uint64_t)event_count * UINT64_C(20000));
    assert(rt_mcdc_collector_reset_checked_v1() == SIMPLE_MCDC_V1_OK);
    free(snapshot_events);
    free(storage);
    return 0;
}
