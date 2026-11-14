#ifndef SIMPLE_XRAY_RESIDENT_ADMISSION_V1_H
#define SIMPLE_XRAY_RESIDENT_ADMISSION_V1_H

/* Private native atomic leaf. Control operations are externally serialized by
 * the process-wide provider owner. Descriptors and everything reachable from
 * them remain resident until process exit. A closed gate never reclaims code.
 * Both attachment and event writers pin BEFORE loading the descriptor. */
#include <stdint.h>
#include <stddef.h>
#include <stdatomic.h>
#include <limits.h>

_Static_assert(ATOMIC_LLONG_LOCK_FREE == 2,
               "resident observation needs lock-free 64-bit admissions");
_Static_assert(ATOMIC_LONG_LOCK_FREE == 2 && sizeof(uint64_t) == 8,
               "resident observation needs a lock-free uint64_t representation");
_Static_assert(ATOMIC_POINTER_LOCK_FREE == 2,
               "resident observation needs lock-free descriptor publication");

typedef struct {
    _Atomic uint64_t gate; /* bit 0 closed, remaining bits reservation count */
    _Atomic(void *) descriptor;
} simple_xray_resident_admission_v1;

#define SIMPLE_XRAY_RESIDENT_ADMISSION_INIT_V1 \
    { ATOMIC_VAR_INIT(UINT64_C(1)), ATOMIC_VAR_INIT(NULL) }

/* Control owner only: publish is allowed after the previous generation closes
 * and drains. A failed publish changes neither descriptor nor admission. */
static inline int simple_xray_resident_publish_v1(
        simple_xray_resident_admission_v1 *owner, void *descriptor) {
    if (!owner || !descriptor ||
        atomic_load_explicit(&owner->gate, memory_order_acquire) != UINT64_C(1))
        return 0;
    atomic_store_explicit(&owner->descriptor, descriptor, memory_order_relaxed);
    atomic_store_explicit(&owner->gate, UINT64_C(0), memory_order_release);
    return 1;
}

/* Bounded, nonblocking acquisition. Contention/saturation is a dropped
 * observation, not a reason to spin on application threads. */
static inline void *simple_xray_resident_acquire_v1(
        simple_xray_resident_admission_v1 *owner) {
    uint64_t observed = atomic_load_explicit(&owner->gate, memory_order_relaxed);
    for (unsigned attempt = 0; attempt != 8; ++attempt) {
        if ((observed & UINT64_C(1)) || observed > UINT64_MAX - UINT64_C(2))
            return NULL;
        if (atomic_compare_exchange_weak_explicit(&owner->gate, &observed,
                observed + UINT64_C(2), memory_order_acquire,
                memory_order_relaxed))
            return atomic_load_explicit(&owner->descriptor, memory_order_relaxed);
    }
    return NULL;
}

/* Exactly one release for each successful acquire; never call after failure. */
static inline void simple_xray_resident_release_v1(
        simple_xray_resident_admission_v1 *owner) {
    atomic_fetch_sub_explicit(&owner->gate, UINT64_C(2), memory_order_release);
}

static inline void simple_xray_resident_close_v1(
        simple_xray_resident_admission_v1 *owner) {
    atomic_fetch_or_explicit(&owner->gate, UINT64_C(1), memory_order_acq_rel);
}

static inline int simple_xray_resident_drained_v1(
        simple_xray_resident_admission_v1 *owner) {
    return atomic_load_explicit(&owner->gate, memory_order_acquire) == UINT64_C(1);
}

#endif
