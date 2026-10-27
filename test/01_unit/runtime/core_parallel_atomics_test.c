#include "runtime.h"

#include <stdint.h>
#include <stdatomic.h>
#include <stdio.h>
#include <limits.h>
#ifdef _WIN32
#include <windows.h>
#else
#include <pthread.h>
#endif

#define CHECK(test) do { if (!(test)) { fprintf(stderr, "atomic check failed: line %d\n", __LINE__); return 1; } } while (0)
#define THREADS 8
#define ITERATIONS 20000
static _Atomic int64_t counter;
static int64_t sums[THREADS];

#ifdef _WIN32
static DWORD WINAPI increment(LPVOID argument) {
#else
static void* increment(void* argument) {
#endif
    intptr_t index = (intptr_t)argument;
    int64_t sum = 0;
    for (int i = 0; i < ITERATIONS; ++i)
        sum += rt_par_atomic_add_i64((int64_t*)&counter, 1);
    sums[index] = sum;
    return 0;
}

int main(void) {
    _Atomic int64_t value = 7;
    int64_t* ptr = (int64_t*)&value;
    CHECK(rt_par_atomic_i64_is_lock_free(NULL) == 0);
    if (_Alignof(_Atomic int64_t) > 1) {
        unsigned char unaligned_storage[sizeof(_Atomic int64_t) + _Alignof(_Atomic int64_t)];
        uintptr_t unaligned_addr = (uintptr_t)unaligned_storage + 1;
        if (unaligned_addr % _Alignof(_Atomic int64_t) == 0) unaligned_addr += 1;
        CHECK(rt_par_atomic_i64_is_lock_free((int64_t*)unaligned_addr) == 0);
    }
    int64_t expected_lock_free = sizeof(_Atomic int64_t) == sizeof(int64_t) &&
        _Alignof(_Atomic int64_t) <= sizeof(int64_t) && atomic_is_lock_free(&value) ? 1 : 0;
    CHECK(rt_par_atomic_i64_is_lock_free(ptr) == expected_lock_free);
    CHECK(rt_par_atomic_add_i64(ptr, 5) == 7 && atomic_load(&value) == 12);
    CHECK(rt_par_atomic_sub_i64(ptr, 3) == 12 && atomic_load(&value) == 9);
    CHECK(rt_par_atomic_xchg_i64(ptr, -4) == 9 && atomic_load(&value) == -4);
    CHECK(rt_par_atomic_cmpxchg_i64(ptr, -4, 19) == -4 && atomic_load(&value) == 19);
    CHECK(rt_par_atomic_cmpxchg_i64(ptr, -4, 23) == 19 && atomic_load(&value) == 19);
    CHECK(rt_par_atomic_min_i64(ptr, 30) == 19 && atomic_load(&value) == 19);
    CHECK(rt_par_atomic_min_i64(ptr, INT64_MIN) == 19 && atomic_load(&value) == INT64_MIN);
    CHECK(rt_par_atomic_min_i64(ptr, INT64_MIN) == INT64_MIN && atomic_load(&value) == INT64_MIN);
    CHECK(rt_par_atomic_max_i64(ptr, INT64_MAX) == INT64_MIN && atomic_load(&value) == INT64_MAX);
    CHECK(rt_par_atomic_max_i64(ptr, INT64_MIN) == INT64_MAX && atomic_load(&value) == INT64_MAX);
    CHECK(rt_par_atomic_add_i64(ptr, 1) == INT64_MAX && atomic_load(&value) == INT64_MIN);
    CHECK(rt_par_atomic_sub_i64(ptr, 1) == INT64_MIN && atomic_load(&value) == INT64_MAX);
#ifdef _WIN32
    HANDLE threads[THREADS];
    for (intptr_t i = 0; i < THREADS; ++i) {
        threads[i] = CreateThread(NULL, 0, increment, (void*)i, 0, NULL);
        CHECK(threads[i] != NULL);
    }
    CHECK(WaitForMultipleObjects(THREADS, threads, TRUE, INFINITE) == WAIT_OBJECT_0);
    for (int i = 0; i < THREADS; ++i) CloseHandle(threads[i]);
#else
    pthread_t threads[THREADS];
    for (intptr_t i = 0; i < THREADS; ++i)
        CHECK(pthread_create(&threads[i], NULL, increment, (void*)i) == 0);
    for (int i = 0; i < THREADS; ++i) CHECK(pthread_join(threads[i], NULL) == 0);
#endif
    int64_t sum = 0;
    for (int i = 0; i < THREADS; ++i) sum += sums[i];
    int64_t count = THREADS * ITERATIONS;
    CHECK(atomic_load(&counter) == count);
    CHECK(sum == count * (count - 1) / 2);
    puts("PASS core parallel atomics: lock-free capability ABI, null/alignment rejection, old values, cmpxchg failure, signed boundaries, 160000 contended increments");
    return 0;
}
