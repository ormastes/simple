/* runtime_file_exists_probe_impl.h -- private rt_file_exists failed-probe
 * counter shared by runtime.c and runtime_native.c.
 *
 * Not a public header: include it exactly once, from one translation unit,
 * after <stdint.h> and <stdatomic.h>. Everything here is static; the exported
 * rt_file_exists_probe_* entry points stay hand-written in each includer as
 * one-line wrappers over the *_impl helpers below, so each lane keeps its own
 * linkage (weak twin in runtime.c, strong in runtime_native.c) and no rt_*
 * symbol is defined by a header.
 *
 * Failed existence probes are measured at the rt_file_exists facade, never at
 * spl_file_exists or at a libc/syscall boundary.  A gate holds accepting and
 * in-flight leases; a separate monotonic generation is captured by each lease.
 * end() first closes the gate, then drains those leases before it snapshots.
 */
#ifndef SIMPLE_RUNTIME_FILE_EXISTS_PROBE_IMPL_H
#define SIMPLE_RUNTIME_FILE_EXISTS_PROBE_IMPL_H

#define RT_FILE_EXISTS_PROBE_ACCEPTING    (UINT64_C(1) << 63)
#define RT_FILE_EXISTS_PROBE_TRANSITION   (UINT64_C(1) << 62)
#define RT_FILE_EXISTS_PROBE_LEASE_MASK   (RT_FILE_EXISTS_PROBE_TRANSITION - 1)
#define RT_FILE_EXISTS_PROBE_GENERATION_MAX UINT64_C(0x7fffffffffffffff)
#define RT_FILE_EXISTS_PROBE_TOTAL_MAX    UINT64_C(0x7fffffff)

static atomic_uint_fast64_t rt_file_exists_probe_state = 0;
static atomic_uint_fast64_t rt_file_exists_probe_generation = 0;
static atomic_uint_fast64_t rt_file_exists_probe_total = 0;
static atomic_uint_fast64_t rt_file_exists_probe_failed = 0;

/* Reserve one total slot. A failed slot is incremented only after this succeeds,
 * so concurrent records preserve failed <= total <= TOTAL_MAX. */
static int rt_file_exists_probe_try_add_total(void) {
    uint_fast64_t current = atomic_load_explicit(
        &rt_file_exists_probe_total, memory_order_relaxed);
    while (current < RT_FILE_EXISTS_PROBE_TOTAL_MAX) {
        if (atomic_compare_exchange_weak_explicit(
                &rt_file_exists_probe_total, &current, current + 1,
                memory_order_relaxed, memory_order_relaxed)) {
            return 1;
        }
    }
    return 0;
}

static uint_fast64_t rt_file_exists_probe_lease_admit(void) {
    /* Disabled source path: one relaxed gate load, without assembly claims. */
    uint_fast64_t state = atomic_load_explicit(
        &rt_file_exists_probe_state, memory_order_relaxed);
    if ((state & RT_FILE_EXISTS_PROBE_ACCEPTING) == 0) return 0;

    for (;;) {
        if ((state & RT_FILE_EXISTS_PROBE_ACCEPTING) == 0) return 0;
        if ((state & RT_FILE_EXISTS_PROBE_LEASE_MASK) ==
            RT_FILE_EXISTS_PROBE_LEASE_MASK) return 0;
        if (atomic_compare_exchange_weak_explicit(
                &rt_file_exists_probe_state, &state, state + UINT64_C(1),
                memory_order_acquire, memory_order_relaxed)) {
            uint_fast64_t generation = atomic_load_explicit(
                &rt_file_exists_probe_generation, memory_order_acquire);
            if (generation != 0) return generation;
            atomic_fetch_sub_explicit(
                &rt_file_exists_probe_state, UINT64_C(1), memory_order_release);
            return 0;
        }
    }
}

static void rt_file_exists_probe_record(uint_fast64_t lease, int exists) {
    if (lease != 0 && atomic_load_explicit(
            &rt_file_exists_probe_generation, memory_order_acquire) == lease) {
        if (rt_file_exists_probe_try_add_total() && !exists) {
            uint_fast64_t failed = atomic_load_explicit(
                &rt_file_exists_probe_failed, memory_order_relaxed);
            while (failed < RT_FILE_EXISTS_PROBE_TOTAL_MAX) {
                if (atomic_compare_exchange_weak_explicit(
                        &rt_file_exists_probe_failed, &failed, failed + 1,
                        memory_order_relaxed, memory_order_relaxed)) {
                    break;
                }
            }
        }
    }
    if (lease != 0) {
        atomic_fetch_sub_explicit(
            &rt_file_exists_probe_state, UINT64_C(1), memory_order_release);
    }
}

static int64_t rt_file_exists_probe_begin_impl(void) {
    uint_fast64_t idle = 0;
    if (!atomic_compare_exchange_strong_explicit(
            &rt_file_exists_probe_state, &idle, RT_FILE_EXISTS_PROBE_TRANSITION,
            memory_order_acq_rel, memory_order_acquire)) {
        return -1;
    }
    uint_fast64_t generation = atomic_load_explicit(
        &rt_file_exists_probe_generation, memory_order_acquire);
    if (generation >= RT_FILE_EXISTS_PROBE_GENERATION_MAX) {
        atomic_store_explicit(&rt_file_exists_probe_state, 0, memory_order_release);
        return -3;
    }
    generation += 1;
    atomic_store_explicit(
        &rt_file_exists_probe_generation, generation, memory_order_release);
    atomic_store_explicit(&rt_file_exists_probe_total, 0, memory_order_relaxed);
    atomic_store_explicit(&rt_file_exists_probe_failed, 0, memory_order_relaxed);
    atomic_store_explicit(
        &rt_file_exists_probe_state, RT_FILE_EXISTS_PROBE_ACCEPTING,
        memory_order_release);
    return (int64_t)generation;
}

static int64_t rt_file_exists_probe_end_impl(int64_t token) {
    if (token <= 0 || (uint_fast64_t)token > RT_FILE_EXISTS_PROBE_GENERATION_MAX ||
        atomic_load_explicit(&rt_file_exists_probe_generation, memory_order_acquire) !=
            (uint_fast64_t)token) return -2;

    uint_fast64_t state = atomic_load_explicit(
        &rt_file_exists_probe_state, memory_order_acquire);
    for (;;) {
        if ((state & RT_FILE_EXISTS_PROBE_ACCEPTING) == 0 ||
            atomic_load_explicit(&rt_file_exists_probe_generation, memory_order_acquire) !=
                (uint_fast64_t)token) {
            return -2;
        }
        uint_fast64_t closing =
            (state & RT_FILE_EXISTS_PROBE_LEASE_MASK) |
            RT_FILE_EXISTS_PROBE_TRANSITION;
        if (atomic_compare_exchange_weak_explicit(
                &rt_file_exists_probe_state, &state, closing,
                memory_order_acq_rel, memory_order_acquire)) {
            break;
        }
    }

    do {
        state = atomic_load_explicit(
            &rt_file_exists_probe_state, memory_order_acquire);
    } while ((state & RT_FILE_EXISTS_PROBE_LEASE_MASK) != 0);

    uint_fast64_t total = atomic_load_explicit(
        &rt_file_exists_probe_total, memory_order_acquire);
    uint_fast64_t failed = atomic_load_explicit(
        &rt_file_exists_probe_failed, memory_order_acquire);
    if (total > RT_FILE_EXISTS_PROBE_TOTAL_MAX) total = RT_FILE_EXISTS_PROBE_TOTAL_MAX;
    if (failed > RT_FILE_EXISTS_PROBE_TOTAL_MAX) {
        failed = RT_FILE_EXISTS_PROBE_TOTAL_MAX;
    }
    atomic_store_explicit(
        &rt_file_exists_probe_state,
        0,
        memory_order_release);
    return (int64_t)((total << 32) | failed);
}

#if defined(SIMPLE_RUNTIME_TESTING)
static int64_t rt_file_exists_probe_test_seed_generation_impl(int64_t generation) {
    if (generation < 0 || (uint_fast64_t)generation >
            RT_FILE_EXISTS_PROBE_GENERATION_MAX) return -3;
    uint_fast64_t idle = 0;
    if (!atomic_compare_exchange_strong_explicit(
            &rt_file_exists_probe_state, &idle, RT_FILE_EXISTS_PROBE_TRANSITION,
            memory_order_acq_rel, memory_order_acquire)) return -1;
    atomic_store_explicit(
        &rt_file_exists_probe_generation, (uint_fast64_t)generation,
        memory_order_release);
    atomic_store_explicit(&rt_file_exists_probe_total, 0, memory_order_relaxed);
    atomic_store_explicit(&rt_file_exists_probe_failed, 0, memory_order_relaxed);
    atomic_store_explicit(&rt_file_exists_probe_state, 0, memory_order_release);
    return 0;
}

static int64_t rt_file_exists_probe_test_seed_counters_impl(int64_t total, int64_t failed) {
    if (total < 0 || failed < 0 || (uint_fast64_t)total >
            RT_FILE_EXISTS_PROBE_TOTAL_MAX || (uint_fast64_t)failed >
            (uint_fast64_t)total) return -3;
    uint_fast64_t state = atomic_load_explicit(
        &rt_file_exists_probe_state, memory_order_acquire);
    if ((state & RT_FILE_EXISTS_PROBE_ACCEPTING) == 0 ||
        (state & RT_FILE_EXISTS_PROBE_LEASE_MASK) != 0) return -1;
    atomic_store_explicit(
        &rt_file_exists_probe_total, (uint_fast64_t)total, memory_order_relaxed);
    atomic_store_explicit(
        &rt_file_exists_probe_failed, (uint_fast64_t)failed, memory_order_relaxed);
    return 0;
}
#endif

#endif /* SIMPLE_RUNTIME_FILE_EXISTS_PROBE_IMPL_H */
