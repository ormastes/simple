/* Host contention and ABI values for the AArch64/RV64 freestanding provider.
 * SIMPLEOS_FREESTANDING_ATOMIC_PROBE compiles the same provider without libc. */
typedef long long spl_i64;
typedef unsigned long long spl_u64;

#define RT_VALUE_SPECIAL_TRUE 1ULL
#define RT_VALUE_SPECIAL_FALSE 2ULL
static spl_i64 rt_special(spl_u64 payload) {
    return (spl_i64)((payload << 3) | 3ULL);
}

#ifdef SIMPLEOS_FREESTANDING_ATOMIC_PROBE
static spl_i64 probe_cells[8];
static spl_i64 probe_next;
static void *rt_alloc(spl_i64 bytes) {
    if (bytes != (spl_i64)sizeof(spl_i64) || probe_next >= 8) return (void *)0;
    return &probe_cells[probe_next++];
}
#else
#include <pthread.h>
#include <stdlib.h>
static void *rt_alloc(spl_i64 bytes) { return malloc((size_t)bytes); }
#endif

#include "../../../../src/runtime/startup/baremetal/atomic_runtime.inc.c"

#ifndef SIMPLEOS_FREESTANDING_ATOMIC_PROBE
enum { THREADS = 4, ITERATIONS = 50000 };
static spl_i64 fetch_handle;
static spl_i64 cas_handle;

static void *atomic_worker(void *ignored) {
    (void)ignored;
    for (int i = 0; i < ITERATIONS; ++i) {
        rt_atomic_int_fetch_add(fetch_handle, 1);
        for (;;) {
            spl_i64 before = rt_atomic_int_load(cas_handle);
            if (rt_atomic_int_compare_exchange(cas_handle, before, before + 1))
                break;
        }
    }
    return (void *)0;
}

int main(void) {
    pthread_t threads[THREADS];
    spl_i64 raw = rt_atomic_int_new(8);
    if (!raw || rt_atomic_int_load(raw) != 8) return 1;
    if (!rt_atomic_int_compare_exchange(raw, 8, 16)) return 2;
    if (rt_atomic_int_fetch_add(raw, 8) != 16) return 3;
    if (rt_atomic_int_load(raw) != 24) return 4;
    if (rt_atomic_int_fetch_and(raw, 7) != 24 || rt_atomic_int_load(raw) != 0) return 5;

    spl_i64 flag = rt_atomic_bool_new(rt_special(RT_VALUE_SPECIAL_FALSE));
    if (!flag || rt_atomic_bool_load(flag)) return 6;
    rt_atomic_bool_store(flag, rt_special(RT_VALUE_SPECIAL_TRUE));
    if (!rt_atomic_bool_load(flag)) return 7;
    if (!rt_atomic_bool_fetch_not(flag) || rt_atomic_bool_load(flag)) return 8;
    if (!rt_atomic_bool_compare_exchange(flag, 0, 1) || !rt_atomic_bool_load(flag)) return 9;

    fetch_handle = rt_atomic_int_new(0);
    cas_handle = rt_atomic_int_new(0);
    if (!fetch_handle || !cas_handle) return 10;
    for (int i = 0; i < THREADS; ++i)
        if (pthread_create(&threads[i], 0, atomic_worker, 0)) return 11;
    for (int i = 0; i < THREADS; ++i)
        if (pthread_join(threads[i], 0)) return 12;
    if (rt_atomic_int_load(fetch_handle) != THREADS * ITERATIONS) return 13;
    if (rt_atomic_int_load(cas_handle) != THREADS * ITERATIONS) return 14;
    return 0;
}
#endif
