/* Immortal heap-registry membership reads must not take the writer lock.
 *
 * Bug: doc/08_tracking/bug/immortal_registry_global_spinlock_serializes_threads_2026-11-16.md
 * Every rt_array_get/push, rt_enum_check_variant, text decode, ... validates
 * its pointer through rt_core_is_registered_immortal_ptr. That lookup took the
 * single process-wide spinlock, so N isolated-thread workers spun on one cache
 * line: the internal ELF linker's parallel phases ran ~3x SLOWER at 16 jobs
 * than at 1 (5182 CPU-s for 112 s of wall at 116 workers).
 *
 * Checks:
 *   1. a lookup completes while another thread holds the writer lock;
 *   2. stress: writer threads register/erase their own pointers and force
 *      table growth and same-capacity tombstone rehashes while reader threads
 *      look up pointers that are registered for their whole lifetime; a
 *      reader must never see one of them as unregistered (no false negative
 *      across a resize), and an erased pointer must read as unregistered.
 */
#include "../runtime_native.c"
#include <assert.h>
#include <pthread.h>
#include <stdio.h>
#include <time.h>

#define STABLE_COUNT 4096
#define WRITERS 4
#define READERS 8
#define WRITER_ROUNDS 40
#define WRITER_BATCH 20000

static uintptr_t stable_ptrs[STABLE_COUNT];
static atomic_int stop_readers;
static atomic_long reader_lookups;
static atomic_int false_negatives;

static uintptr_t fake_ptr(uint64_t salt, uint64_t i) {
    /* aligned, never dereferenced by the membership probe */
    return (uintptr_t)(0x100000000ULL + ((salt << 32) | (i << 4)));
}

static atomic_int locked_lookup_done;

static void* lookup_while_locked(void* arg) {
    (void)arg;
    int found = rt_core_is_registered_immortal_ptr((void*)stable_ptrs[7]);
    atomic_store(&locked_lookup_done, found ? 1 : 2);
    return NULL;
}

static void* reader_main(void* arg) {
    uint64_t seed = (uint64_t)(uintptr_t)arg * 2654435761u + 1;
    long n = 0;
    while (!atomic_load(&stop_readers)) {
        seed = seed * 6364136223846793005ULL + 1442695040888963407ULL;
        uintptr_t p = stable_ptrs[(seed >> 33) % STABLE_COUNT];
        if (!rt_core_is_registered_immortal_ptr((void*)p)) atomic_fetch_add(&false_negatives, 1);
        n++;
    }
    atomic_fetch_add(&reader_lookups, n);
    return NULL;
}

static void* writer_main(void* arg) {
    uint64_t salt = 16 + (uint64_t)(uintptr_t)arg;
    for (int round = 0; round < WRITER_ROUNDS; round++) {
        for (uint64_t i = 0; i < WRITER_BATCH; i++) {
            assert(rt_core_register_immortal_ptr((void*)fake_ptr(salt, (uint64_t)round * WRITER_BATCH + i)));
        }
        for (uint64_t i = 0; i < WRITER_BATCH; i++) {
            uintptr_t p = fake_ptr(salt, (uint64_t)round * WRITER_BATCH + i);
            int erased = rt_core_immortal_registry_erase(p);
            assert(erased);
            assert(!rt_core_is_registered_immortal_ptr((void*)p));
        }
    }
    return NULL;
}

static double now_s(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (double)ts.tv_sec + (double)ts.tv_nsec / 1e9;
}

int main(void) {
    for (uint64_t i = 0; i < STABLE_COUNT; i++) {
        stable_ptrs[i] = fake_ptr(1, i);
        assert(rt_core_register_immortal_ptr((void*)stable_ptrs[i]));
    }

    /* 1. reader must not wait for the writer lock */
    core_immortal_shard_acquire(core_immortal_shard(stable_ptrs[7]));
    pthread_t t;
    assert(pthread_create(&t, NULL, lookup_while_locked, NULL) == 0);
    double deadline = now_s() + 5.0;
    while (atomic_load(&locked_lookup_done) == 0 && now_s() < deadline) {}
    int verdict = atomic_load(&locked_lookup_done);
    core_immortal_shard_release(core_immortal_shard(stable_ptrs[7]));
    pthread_join(t, NULL);
    if (verdict != 1) {
        fprintf(stderr, "FAIL: membership lookup %s while the writer lock was held\n",
            verdict == 0 ? "blocked" : "missed a registered pointer");
        return 1;
    }

    /* 2. stress */
    pthread_t readers[READERS], writers[WRITERS];
    for (int i = 0; i < READERS; i++) assert(pthread_create(&readers[i], NULL, reader_main, (void*)(uintptr_t)i) == 0);
    for (int i = 0; i < WRITERS; i++) assert(pthread_create(&writers[i], NULL, writer_main, (void*)(uintptr_t)i) == 0);
    for (int i = 0; i < WRITERS; i++) pthread_join(writers[i], NULL);
    atomic_store(&stop_readers, 1);
    for (int i = 0; i < READERS; i++) pthread_join(readers[i], NULL);
    if (atomic_load(&false_negatives) != 0) {
        fprintf(stderr, "FAIL: %d false negatives across concurrent resizes\n", atomic_load(&false_negatives));
        return 1;
    }
    for (uint64_t i = 0; i < STABLE_COUNT; i++) assert(rt_core_is_registered_immortal_ptr((void*)stable_ptrs[i]));
    printf("PASS: lock-free registry reads (%ld lookups, 0 false negatives)\n", atomic_load(&reader_lookups));
    return 0;
}
