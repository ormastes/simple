/* Minimal decision/condition coverage owner for the core-c-bootstrap bundle. */
#ifdef _WIN32
#include <windows.h>
#else
#include <pthread.h>
#include <errno.h>
#endif
#include <stdbool.h>
#include <stdint.h>
#include <stdatomic.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "runtime_mcdc_v1.h"

typedef struct {
    uint32_t decision_id;
    uint32_t condition_id;
    char *file;
    uint32_t line;
    uint32_t column;
    uint64_t true_count;
    uint64_t false_count;
} CoverageRow;

/* Correlated MC/DC V1 collector. Storage is supplied before the critical
 * entry boundary; record/snapshot never allocate and overflow is sticky. */
typedef struct {
    SimpleMcdcVectorV1 *events;
    size_t capacity;
    size_t count;
    uint64_t next_sequence;
    uint64_t overflow_first;
    uint64_t overflow_count;
    uint64_t session_id;
    uint64_t interpreter_owner_id;
    uint64_t compiled_owner_id;
    uint64_t compiled_owner_sequence;
    bool initialized;
    bool overflowed;
    bool sealed;
} McdcCollectorV1;

static McdcCollectorV1 g_mcdc;
static _Atomic int32_t g_mcdc_compiled_last_status = SIMPLE_MCDC_V1_OK;
static _Atomic(SimpleMcdcDynamicTargetV1) g_mcdc_dynamic_target = NULL;
static _Atomic uint64_t g_mcdc_dynamic_active_calls = 0;
/* Even = stable reader epoch; odd = bind/unbind writer owns publication. */
static _Atomic uint64_t g_mcdc_dynamic_epoch = 0;
#define MCDC_DYNAMIC_COMPILED_HANDLE UINT64_C(1)
#define MCDC_DYNAMIC_TARGET_CAPACITY 8u
typedef struct {
    uint64_t handle;
    uint64_t owner_cookie;
    SimpleMcdcDynamicTargetV1 target;
} McdcDynamicTargetEntryV1;
static McdcDynamicTargetEntryV1
    g_mcdc_dynamic_targets[MCDC_DYNAMIC_TARGET_CAPACITY];
static uint64_t g_mcdc_dynamic_next_handle = 2;
static _Atomic uint64_t g_mcdc_dynamic_bound_handle = 0;

static bool mcdc_dynamic_target_from_handle(
        uint64_t handle, SimpleMcdcDynamicTargetV1 *target) {
    if (!handle || handle > (uint64_t)UINTPTR_MAX || !target ||
        sizeof(*target) > sizeof(uintptr_t)) return false;
    const uintptr_t raw = (uintptr_t)handle;
    *target = NULL;
    memcpy(target, &raw, sizeof(*target));
    return *target != NULL;
}

static SimpleMcdcDynamicTargetV1 mcdc_dynamic_registered_target(
        uint64_t handle) {
    if (handle == MCDC_DYNAMIC_COMPILED_HANDLE)
        return rt_mcdc_record_compiled_vector_v1;
    for (size_t i = 0; i < MCDC_DYNAMIC_TARGET_CAPACITY; ++i)
        if (g_mcdc_dynamic_targets[i].handle == handle)
            return g_mcdc_dynamic_targets[i].target;
    return NULL;
}

static void mcdc_compiled_note_status(int32_t status) {
    if (status == SIMPLE_MCDC_V1_OK) return;
    int32_t expected = SIMPLE_MCDC_V1_OK;
    (void)atomic_compare_exchange_strong_explicit(
        &g_mcdc_compiled_last_status, &expected, status,
        memory_order_relaxed, memory_order_relaxed);
}

static CoverageRow *g_decisions;
static size_t g_decision_count;
static CoverageRow *g_conditions;
static size_t g_condition_count;

#ifdef _WIN32
static INIT_ONCE g_coverage_lock_once = INIT_ONCE_STATIC_INIT;
static CRITICAL_SECTION g_coverage_lock;
static INIT_ONCE g_mcdc_lock_once = INIT_ONCE_STATIC_INIT;
static CRITICAL_SECTION g_mcdc_lock;
static BOOL CALLBACK coverage_init_lock(PINIT_ONCE once, PVOID parameter, PVOID *context) {
    (void)once; (void)parameter; (void)context;
    InitializeCriticalSection(&g_coverage_lock);
    return TRUE;
}
static void coverage_lock(void) {
    if (!InitOnceExecuteOnce(&g_coverage_lock_once, coverage_init_lock, NULL, NULL)) abort();
    EnterCriticalSection(&g_coverage_lock);
}
static void coverage_unlock(void) { LeaveCriticalSection(&g_coverage_lock); }
static BOOL CALLBACK mcdc_init_lock(PINIT_ONCE once, PVOID parameter, PVOID *context) {
    (void)once; (void)parameter; (void)context;
    InitializeCriticalSection(&g_mcdc_lock);
    return TRUE;
}
static void mcdc_lock(void) {
    if (!InitOnceExecuteOnce(&g_mcdc_lock_once, mcdc_init_lock, NULL, NULL)) abort();
    EnterCriticalSection(&g_mcdc_lock);
}
static bool mcdc_try_lock(void) {
    if (!InitOnceExecuteOnce(&g_mcdc_lock_once, mcdc_init_lock, NULL, NULL)) abort();
    return TryEnterCriticalSection(&g_mcdc_lock) != 0;
}
static void mcdc_unlock(void) { LeaveCriticalSection(&g_mcdc_lock); }
#else
static pthread_mutex_t g_coverage_lock = PTHREAD_MUTEX_INITIALIZER;
static pthread_mutex_t g_mcdc_lock = PTHREAD_MUTEX_INITIALIZER;
static void coverage_lock(void) { if (pthread_mutex_lock(&g_coverage_lock) != 0) abort(); }
static void coverage_unlock(void) { if (pthread_mutex_unlock(&g_coverage_lock) != 0) abort(); }
static void mcdc_lock(void) { if (pthread_mutex_lock(&g_mcdc_lock) != 0) abort(); }
static bool mcdc_try_lock(void) {
    int result = pthread_mutex_trylock(&g_mcdc_lock);
    if (result == 0) return true;
    if (result == EBUSY) return false;
    abort();
}
static void mcdc_unlock(void) { if (pthread_mutex_unlock(&g_mcdc_lock) != 0) abort(); }
#endif

int32_t rt_mcdc_collector_init_v1(void *storage, uint64_t storage_bytes,
                                  uint64_t session_id) {
    if (!storage || !session_id || storage_bytes < sizeof(SimpleMcdcVectorV1))
        return SIMPLE_MCDC_V1_INVALID;
    if (((uintptr_t)storage % _Alignof(SimpleMcdcVectorV1)) != 0)
        return SIMPLE_MCDC_V1_INVALID;
    if (storage_bytes > SIZE_MAX) return SIMPLE_MCDC_V1_INVALID;
    mcdc_lock();
    if (g_mcdc.initialized) { mcdc_unlock(); return SIMPLE_MCDC_V1_BUSY; }
    g_mcdc.events = (SimpleMcdcVectorV1 *)storage;
    g_mcdc.capacity = (size_t)storage_bytes / sizeof(SimpleMcdcVectorV1);
    g_mcdc.count = 0;
    g_mcdc.next_sequence = 0;
    g_mcdc.overflow_first = UINT64_MAX;
    g_mcdc.overflow_count = 0;
    g_mcdc.session_id = session_id;
    g_mcdc.interpreter_owner_id = 0;
    g_mcdc.compiled_owner_id = 0;
    g_mcdc.compiled_owner_sequence = 0;
    atomic_store_explicit(&g_mcdc_compiled_last_status,
                          SIMPLE_MCDC_V1_OK, memory_order_relaxed);
    g_mcdc.overflowed = false;
    g_mcdc.sealed = false;
    g_mcdc.initialized = true;
    mcdc_unlock();
    return SIMPLE_MCDC_V1_OK;
}

static int32_t mcdc_record_vector_locked_v1(
        uint64_t session_id, uint64_t decision_id, uint32_t condition_count,
        uint64_t source_digest, uint64_t evaluated_mask, uint64_t true_mask,
        uint64_t owner_id, uint64_t owner_sequence, uint8_t outcome) {
    if (!session_id || !decision_id || !condition_count || condition_count > 62u ||
        !source_digest ||
        !owner_id || outcome > 1u) return SIMPLE_MCDC_V1_INVALID;
    const uint64_t admitted = (UINT64_C(1) << condition_count) - UINT64_C(1);
    if ((evaluated_mask & ~admitted) || (true_mask & ~evaluated_mask))
        return SIMPLE_MCDC_V1_INVALID;
    if (!g_mcdc.initialized) {
        return SIMPLE_MCDC_V1_NOT_INITIALIZED;
    }
    if (g_mcdc.session_id != session_id) return SIMPLE_MCDC_V1_SESSION_MISMATCH;
    if (g_mcdc.sealed) return SIMPLE_MCDC_V1_NOT_SEALED;
    if (g_mcdc.next_sequence == UINT64_MAX) {
        if (!g_mcdc.overflowed) g_mcdc.overflow_first = UINT64_MAX;
        g_mcdc.overflowed = true;
        if (g_mcdc.overflow_count != UINT64_MAX) ++g_mcdc.overflow_count;
        return SIMPLE_MCDC_V1_OVERFLOW;
    }
    const uint64_t sequence = g_mcdc.next_sequence++;
    if (g_mcdc.count == g_mcdc.capacity) {
        if (!g_mcdc.overflowed) g_mcdc.overflow_first = sequence;
        g_mcdc.overflowed = true;
        if (g_mcdc.overflow_count != UINT64_MAX) ++g_mcdc.overflow_count;
        return SIMPLE_MCDC_V1_OVERFLOW;
    }
    g_mcdc.events[g_mcdc.count++] = (SimpleMcdcVectorV1){
        decision_id, condition_count, 0u, source_digest, evaluated_mask, true_mask,
        owner_id, owner_sequence, outcome, {0}
    };
    return SIMPLE_MCDC_V1_OK;
}

int32_t rt_mcdc_record_vector_v1(uint64_t session_id, uint64_t decision_id,
                                 uint32_t condition_count,
                                 uint64_t source_digest,
                                 uint64_t evaluated_mask, uint64_t true_mask,
                                 uint64_t owner_id, uint64_t owner_sequence,
                                 uint8_t outcome) {
    if (!mcdc_try_lock()) return SIMPLE_MCDC_V1_BUSY;
    const int32_t status = mcdc_record_vector_locked_v1(
        session_id, decision_id, condition_count, source_digest,
        evaluated_mask, true_mask, owner_id, owner_sequence, outcome);
    mcdc_unlock();
    return status;
}

int32_t rt_mcdc_configure_compiled_owner_v1(uint64_t session_id,
                                            uint64_t owner_id) {
    if (!session_id || !owner_id) return SIMPLE_MCDC_V1_INVALID;
    mcdc_lock();
    int32_t status = SIMPLE_MCDC_V1_OK;
    if (!g_mcdc.initialized) status = SIMPLE_MCDC_V1_NOT_INITIALIZED;
    else if (g_mcdc.session_id != session_id) status = SIMPLE_MCDC_V1_SESSION_MISMATCH;
    else if (g_mcdc.sealed) status = SIMPLE_MCDC_V1_NOT_SEALED;
    else if (g_mcdc.compiled_owner_id != 0) status = SIMPLE_MCDC_V1_BUSY;
    else {
        g_mcdc.compiled_owner_id = owner_id;
        g_mcdc.compiled_owner_sequence = 0;
        atomic_store_explicit(&g_mcdc_compiled_last_status,
                              SIMPLE_MCDC_V1_OK, memory_order_relaxed);
    }
    mcdc_unlock();
    return status;
}

int32_t rt_mcdc_release_compiled_owner_v1(uint64_t session_id,
                                          uint64_t owner_id) {
    if (!session_id || !owner_id) return SIMPLE_MCDC_V1_INVALID;
    mcdc_lock();
    int32_t status = SIMPLE_MCDC_V1_OK;
    if (!g_mcdc.initialized) status = SIMPLE_MCDC_V1_NOT_INITIALIZED;
    else if (g_mcdc.session_id != session_id) status = SIMPLE_MCDC_V1_SESSION_MISMATCH;
    else if (g_mcdc.compiled_owner_id != owner_id) status = SIMPLE_MCDC_V1_INVALID;
    else {
        g_mcdc.compiled_owner_id = 0;
        g_mcdc.compiled_owner_sequence = 0;
    }
    mcdc_unlock();
    return status;
}

int32_t rt_mcdc_record_compiled_vector_v1(uint64_t decision_id,
                                          uint32_t condition_count,
                                          uint64_t source_digest,
                                          uint64_t evaluated_mask,
                                          uint64_t true_mask,
                                          uint8_t outcome) {
    if (!mcdc_try_lock()) {
        mcdc_compiled_note_status(SIMPLE_MCDC_V1_BUSY);
        return SIMPLE_MCDC_V1_BUSY;
    }
    int32_t status;
    if (!g_mcdc.compiled_owner_id) {
        status = SIMPLE_MCDC_V1_NOT_INITIALIZED;
    } else if (g_mcdc.compiled_owner_sequence == UINT64_MAX) {
        status = SIMPLE_MCDC_V1_OVERFLOW;
    } else {
        status = mcdc_record_vector_locked_v1(
            g_mcdc.session_id, decision_id, condition_count, source_digest,
            evaluated_mask, true_mask, g_mcdc.compiled_owner_id,
            g_mcdc.compiled_owner_sequence, outcome);
        if (status == SIMPLE_MCDC_V1_OK) ++g_mcdc.compiled_owner_sequence;
    }
    mcdc_compiled_note_status(status);
    mcdc_unlock();
    return status;
}

int32_t rt_mcdc_compiled_last_status_v1(void) {
    return atomic_load_explicit(&g_mcdc_compiled_last_status,
                                memory_order_relaxed);
}

uint64_t rt_mcdc_compiled_target_v1(void) {
    return MCDC_DYNAMIC_COMPILED_HANDLE;
}

int32_t rt_mcdc_dynamic_bind_v1(uint64_t target_handle) {
    mcdc_lock();
    SimpleMcdcDynamicTargetV1 target = mcdc_dynamic_registered_target(target_handle);
    if (!target) { mcdc_unlock(); return SIMPLE_MCDC_V1_INVALID; }
    uint64_t epoch = atomic_load_explicit(&g_mcdc_dynamic_epoch,
                                          memory_order_acquire);
    if ((epoch & 1u) || !atomic_compare_exchange_strong_explicit(
            &g_mcdc_dynamic_epoch, &epoch, epoch + 1,
            memory_order_acq_rel, memory_order_relaxed))
        { mcdc_unlock(); return SIMPLE_MCDC_V1_BUSY; }
    if (atomic_load_explicit(&g_mcdc_dynamic_active_calls,
                             memory_order_acquire) != 0 ||
        atomic_load_explicit(&g_mcdc_dynamic_target,
                             memory_order_relaxed) != NULL) {
        atomic_store_explicit(&g_mcdc_dynamic_epoch, epoch + 2,
                              memory_order_release);
        mcdc_unlock();
        return SIMPLE_MCDC_V1_BUSY;
    }
    atomic_store_explicit(&g_mcdc_dynamic_target, target, memory_order_relaxed);
    atomic_store_explicit(&g_mcdc_dynamic_bound_handle, target_handle,
                          memory_order_relaxed);
    atomic_store_explicit(&g_mcdc_dynamic_epoch, epoch + 2,
                          memory_order_release);
    mcdc_unlock();
    return SIMPLE_MCDC_V1_OK;
}

int32_t rt_mcdc_dynamic_unbind_v1(uint64_t target_handle) {
    mcdc_lock();
    SimpleMcdcDynamicTargetV1 target = mcdc_dynamic_registered_target(target_handle);
    if (!target || atomic_load_explicit(&g_mcdc_dynamic_bound_handle,
                                        memory_order_relaxed) != target_handle) {
        mcdc_unlock();
        return SIMPLE_MCDC_V1_INVALID;
    }
    uint64_t epoch = atomic_load_explicit(&g_mcdc_dynamic_epoch,
                                          memory_order_acquire);
    if ((epoch & 1u) || !atomic_compare_exchange_strong_explicit(
            &g_mcdc_dynamic_epoch, &epoch, epoch + 1,
            memory_order_acq_rel, memory_order_relaxed))
        { mcdc_unlock(); return SIMPLE_MCDC_V1_BUSY; }
    if (atomic_load_explicit(&g_mcdc_dynamic_target,
                             memory_order_relaxed) != target) {
        atomic_store_explicit(&g_mcdc_dynamic_epoch, epoch + 2,
                              memory_order_release);
        mcdc_unlock();
        return SIMPLE_MCDC_V1_INVALID;
    }
    atomic_store_explicit(&g_mcdc_dynamic_target, NULL, memory_order_relaxed);
    atomic_store_explicit(&g_mcdc_dynamic_bound_handle, 0,
                          memory_order_relaxed);
    if (atomic_load_explicit(&g_mcdc_dynamic_active_calls,
                             memory_order_acquire) == 0) {
        atomic_store_explicit(&g_mcdc_dynamic_epoch, epoch + 2,
                              memory_order_release);
        mcdc_unlock();
        return SIMPLE_MCDC_V1_OK;
    }
    /* Keep the epoch odd until settle observes the last prior reader exit. */
    mcdc_unlock();
    return SIMPLE_MCDC_V1_DRAINING;
}

uint64_t rt_mcdc_dynamic_register_target_v1(uint64_t target_address,
                                             uint64_t owner_cookie) {
    SimpleMcdcDynamicTargetV1 target = NULL;
    if (!owner_cookie || !mcdc_dynamic_target_from_handle(target_address, &target))
        return 0;
    mcdc_lock();
    size_t free_index = MCDC_DYNAMIC_TARGET_CAPACITY;
    for (size_t i = 0; i < MCDC_DYNAMIC_TARGET_CAPACITY; ++i) {
        if (g_mcdc_dynamic_targets[i].handle == 0 &&
            free_index == MCDC_DYNAMIC_TARGET_CAPACITY) free_index = i;
    }
    if (free_index == MCDC_DYNAMIC_TARGET_CAPACITY ||
        g_mcdc_dynamic_next_handle == UINT64_MAX) {
        mcdc_unlock();
        return 0;
    }
    const uint64_t handle = g_mcdc_dynamic_next_handle++;
    g_mcdc_dynamic_targets[free_index] = (McdcDynamicTargetEntryV1){
        handle, owner_cookie, target
    };
    mcdc_unlock();
    return handle;
}

int32_t rt_mcdc_dynamic_unregister_target_v1(uint64_t target_handle,
                                              uint64_t owner_cookie) {
    if (target_handle <= MCDC_DYNAMIC_COMPILED_HANDLE || !owner_cookie)
        return SIMPLE_MCDC_V1_INVALID;
    mcdc_lock();
    if (atomic_load_explicit(&g_mcdc_dynamic_bound_handle,
                             memory_order_acquire) == target_handle ||
        (atomic_load_explicit(&g_mcdc_dynamic_epoch,
                              memory_order_acquire) & 1u) ||
        atomic_load_explicit(&g_mcdc_dynamic_active_calls,
                             memory_order_acquire) != 0) {
        mcdc_unlock();
        return SIMPLE_MCDC_V1_BUSY;
    }
    for (size_t i = 0; i < MCDC_DYNAMIC_TARGET_CAPACITY; ++i) {
        if (g_mcdc_dynamic_targets[i].handle == target_handle) {
            if (g_mcdc_dynamic_targets[i].owner_cookie != owner_cookie) {
                mcdc_unlock();
                return SIMPLE_MCDC_V1_INVALID;
            }
            g_mcdc_dynamic_targets[i] = (McdcDynamicTargetEntryV1){0};
            mcdc_unlock();
            return SIMPLE_MCDC_V1_OK;
        }
    }
    mcdc_unlock();
    return SIMPLE_MCDC_V1_INVALID;
}

int32_t rt_mcdc_dynamic_settled_v1(void) {
    uint64_t epoch = atomic_load_explicit(&g_mcdc_dynamic_epoch,
                                          memory_order_acquire);
    if (!(epoch & 1u))
        return atomic_load_explicit(&g_mcdc_dynamic_target,
                                    memory_order_acquire) == NULL
            ? SIMPLE_MCDC_V1_OK : SIMPLE_MCDC_V1_BUSY;
    if (atomic_load_explicit(&g_mcdc_dynamic_active_calls,
                             memory_order_acquire) != 0)
        return SIMPLE_MCDC_V1_BUSY;
    if (!atomic_compare_exchange_strong_explicit(
            &g_mcdc_dynamic_epoch, &epoch, epoch + 1,
            memory_order_release, memory_order_relaxed))
        return SIMPLE_MCDC_V1_BUSY;
    return SIMPLE_MCDC_V1_OK;
}

int32_t rt_mcdc_dynamic_vector_patchpoint_v1(uint64_t decision_id,
                                             uint32_t condition_count,
                                             uint64_t source_digest,
                                             uint64_t evaluated_mask,
                                             uint64_t true_mask,
                                             uint8_t outcome) {
    const uint64_t epoch = atomic_load_explicit(&g_mcdc_dynamic_epoch,
                                                memory_order_acquire);
    if (epoch & 1u) return SIMPLE_MCDC_V1_OK;
    atomic_fetch_add_explicit(&g_mcdc_dynamic_active_calls, 1,
                              memory_order_acquire);
    if (atomic_load_explicit(&g_mcdc_dynamic_epoch,
                             memory_order_acquire) != epoch) {
        atomic_fetch_sub_explicit(&g_mcdc_dynamic_active_calls, 1,
                                  memory_order_release);
        return SIMPLE_MCDC_V1_OK;
    }
    SimpleMcdcDynamicTargetV1 target = atomic_load_explicit(
        &g_mcdc_dynamic_target, memory_order_relaxed);
    if (!target) {
        atomic_fetch_sub_explicit(&g_mcdc_dynamic_active_calls, 1,
                                  memory_order_release);
        return SIMPLE_MCDC_V1_OK;
    }
    const int32_t status = target(decision_id, condition_count, source_digest,
                                  evaluated_mask, true_mask, outcome);
    atomic_fetch_sub_explicit(&g_mcdc_dynamic_active_calls, 1,
                              memory_order_release);
    return status;
}

int32_t rt_mcdc_collector_seal_v1(uint64_t session_id) {
    mcdc_lock();
    if (!g_mcdc.initialized) { mcdc_unlock(); return SIMPLE_MCDC_V1_NOT_INITIALIZED; }
    if (g_mcdc.session_id != session_id) { mcdc_unlock(); return SIMPLE_MCDC_V1_SESSION_MISMATCH; }
    g_mcdc.sealed = true;
    mcdc_unlock();
    return SIMPLE_MCDC_V1_OK;
}

int32_t rt_mcdc_claim_interpreter_owner_v1(uint64_t session_id,
                                           uint64_t owner_id) {
    if (!session_id || !owner_id) return SIMPLE_MCDC_V1_INVALID;
    mcdc_lock();
    if (!g_mcdc.initialized) { mcdc_unlock(); return SIMPLE_MCDC_V1_NOT_INITIALIZED; }
    if (g_mcdc.session_id != session_id) { mcdc_unlock(); return SIMPLE_MCDC_V1_SESSION_MISMATCH; }
    if (g_mcdc.interpreter_owner_id != 0) { mcdc_unlock(); return SIMPLE_MCDC_V1_BUSY; }
    g_mcdc.interpreter_owner_id = owner_id;
    mcdc_unlock();
    return SIMPLE_MCDC_V1_OK;
}

int32_t rt_mcdc_release_interpreter_owner_v1(uint64_t session_id,
                                             uint64_t owner_id) {
    if (!session_id || !owner_id) return SIMPLE_MCDC_V1_INVALID;
    mcdc_lock();
    if (!g_mcdc.initialized) { mcdc_unlock(); return SIMPLE_MCDC_V1_NOT_INITIALIZED; }
    if (g_mcdc.session_id != session_id) { mcdc_unlock(); return SIMPLE_MCDC_V1_SESSION_MISMATCH; }
    if (g_mcdc.interpreter_owner_id != owner_id) { mcdc_unlock(); return SIMPLE_MCDC_V1_SESSION_MISMATCH; }
    g_mcdc.interpreter_owner_id = 0;
    mcdc_unlock();
    return SIMPLE_MCDC_V1_OK;
}

int32_t rt_mcdc_snapshot_v1(SimpleMcdcVectorV1 *output, uint64_t output_capacity,
                            SimpleMcdcSnapshotV1 *snapshot) {
    if (!snapshot || output_capacity > SIZE_MAX) return SIMPLE_MCDC_V1_INVALID;
    mcdc_lock();
    if (!g_mcdc.initialized) {
        mcdc_unlock();
        return SIMPLE_MCDC_V1_NOT_INITIALIZED;
    }
    if (!g_mcdc.sealed) { mcdc_unlock(); return SIMPLE_MCDC_V1_NOT_SEALED; }
    if (g_mcdc.count > output_capacity || (g_mcdc.count && !output)) {
        mcdc_unlock();
        return SIMPLE_MCDC_V1_OUTPUT_TOO_SMALL;
    }
    if (g_mcdc.count) memmove(output, g_mcdc.events, g_mcdc.count * sizeof(*output));
    *snapshot = (SimpleMcdcSnapshotV1){
        (uint64_t)g_mcdc.count, g_mcdc.overflow_first, g_mcdc.overflow_count,
        g_mcdc.session_id, g_mcdc.overflowed ? 1u : 0u, {0}
    };
    mcdc_unlock();
    return SIMPLE_MCDC_V1_OK;
}

int32_t rt_mcdc_collector_reset_checked_v1(void) {
    mcdc_lock();
    if (g_mcdc.interpreter_owner_id != 0 || g_mcdc.compiled_owner_id != 0 ||
        atomic_load_explicit(&g_mcdc_dynamic_active_calls,
                             memory_order_acquire) != 0 ||
        atomic_load_explicit(&g_mcdc_dynamic_target,
                             memory_order_acquire) != NULL ||
        (atomic_load_explicit(&g_mcdc_dynamic_epoch,
                              memory_order_acquire) & 1u)) {
        mcdc_unlock();
        return SIMPLE_MCDC_V1_BUSY;
    }
    g_mcdc.events = NULL;
    g_mcdc.capacity = 0;
    g_mcdc.count = 0;
    g_mcdc.next_sequence = 0;
    g_mcdc.overflow_first = UINT64_MAX;
    g_mcdc.overflow_count = 0;
    g_mcdc.session_id = 0;
    g_mcdc.interpreter_owner_id = 0;
    g_mcdc.compiled_owner_id = 0;
    g_mcdc.compiled_owner_sequence = 0;
    atomic_store_explicit(&g_mcdc_compiled_last_status,
                          SIMPLE_MCDC_V1_OK, memory_order_relaxed);
    g_mcdc.initialized = false;
    g_mcdc.overflowed = false;
    g_mcdc.sealed = false;
    mcdc_unlock();
    return SIMPLE_MCDC_V1_OK;
}

void rt_mcdc_collector_reset_v1(void) {
    (void)rt_mcdc_collector_reset_checked_v1();
}

static bool mcdc_vector_valid(const SimpleMcdcVectorV1 *event) {
    if (!event->decision_id || !event->source_digest || !event->owner_id ||
        !event->condition_count || event->condition_count > 62u || event->outcome > 1u)
        return false;
    if (event->reserved0 != 0) return false;
    for (size_t i = 0; i < sizeof(event->reserved); ++i)
        if (event->reserved[i] != 0) return false;
    const uint64_t admitted = (UINT64_C(1) << event->condition_count) - UINT64_C(1);
    return !(event->evaluated_mask & ~admitted) &&
           !(event->true_mask & ~event->evaluated_mask);
}

static bool mcdc_same_identity(const SimpleMcdcVectorV1 *a,
                               const SimpleMcdcVectorV1 *b) {
    return a->decision_id == b->decision_id &&
           a->source_digest == b->source_digest &&
           a->condition_count == b->condition_count;
}

static int mcdc_vector_order(const SimpleMcdcVectorV1 *a,
                             const SimpleMcdcVectorV1 *b) {
    if (a->source_digest != b->source_digest) return a->source_digest < b->source_digest ? -1 : 1;
    if (a->decision_id != b->decision_id) return a->decision_id < b->decision_id ? -1 : 1;
    if (a->owner_id != b->owner_id) return a->owner_id < b->owner_id ? -1 : 1;
    if (a->owner_sequence != b->owner_sequence) return a->owner_sequence < b->owner_sequence ? -1 : 1;
    return 0;
}

static int mcdc_vector_qsort_compare(const void *left, const void *right) {
    return mcdc_vector_order((const SimpleMcdcVectorV1 *)left,
                             (const SimpleMcdcVectorV1 *)right);
}

int32_t rt_mcdc_sort_vectors_v1(SimpleMcdcVectorV1 *events,
                                uint64_t event_count) {
    if ((event_count && !events) || event_count > SIZE_MAX ||
        event_count > SIZE_MAX / sizeof(*events) ||
        (events && ((uintptr_t)events % _Alignof(SimpleMcdcVectorV1)) != 0))
        return SIMPLE_MCDC_V1_INVALID;
    for (size_t i = 0; i < (size_t)event_count; ++i)
        if (!mcdc_vector_valid(&events[i])) return SIMPLE_MCDC_V1_INVALID;
    if (event_count > 1)
        qsort(events, (size_t)event_count, sizeof(*events), mcdc_vector_qsort_compare);
    return SIMPLE_MCDC_V1_OK;
}

static bool mcdc_ranges_overlap(const void *a, size_t a_bytes,
                                const void *b, size_t b_bytes) {
    if (!a_bytes || !b_bytes) return false;
    const uintptr_t a_start = (uintptr_t)a;
    const uintptr_t b_start = (uintptr_t)b;
    if (a_start > UINTPTR_MAX - a_bytes || b_start > UINTPTR_MAX - b_bytes) return true;
    const uintptr_t a_end = a_start + a_bytes;
    const uintptr_t b_end = b_start + b_bytes;
    return a_start < b_end && b_start < a_end;
}

int32_t rt_mcdc_analyze_unique_v1(const SimpleMcdcVectorV1 *events,
                                  uint64_t event_count,
                                  SimpleMcdcWitnessV1 *witnesses,
                                  uint64_t witness_capacity,
                                  uint64_t pair_budget,
                                  SimpleMcdcAnalysisV1 *analysis) {
    if (!analysis || (event_count && !events) || (witness_capacity && !witnesses) ||
        event_count > SIZE_MAX || witness_capacity > SIZE_MAX)
        return SIMPLE_MCDC_V1_INVALID;
    if (((uintptr_t)analysis % _Alignof(SimpleMcdcAnalysisV1)) != 0 ||
        (events && ((uintptr_t)events % _Alignof(SimpleMcdcVectorV1)) != 0) ||
        (witnesses && ((uintptr_t)witnesses % _Alignof(SimpleMcdcWitnessV1)) != 0))
        return SIMPLE_MCDC_V1_INVALID;
    if (event_count > SIZE_MAX / sizeof(*events) ||
        witness_capacity > SIZE_MAX / sizeof(*witnesses))
        return SIMPLE_MCDC_V1_INVALID;
    const size_t event_bytes = (size_t)event_count * sizeof(*events);
    const size_t witness_bytes = (size_t)witness_capacity * sizeof(*witnesses);
    if (mcdc_ranges_overlap(events, event_bytes, witnesses, witness_bytes) ||
        mcdc_ranges_overlap(events, event_bytes, analysis, sizeof(*analysis)) ||
        mcdc_ranges_overlap(witnesses, witness_bytes, analysis, sizeof(*analysis)))
        return SIMPLE_MCDC_V1_INVALID;
    *analysis = (SimpleMcdcAnalysisV1){0, 0, 0, 0, 0, pair_budget};
    for (size_t i = 0; i < (size_t)event_count; ++i) {
        if (!mcdc_vector_valid(&events[i])) return SIMPLE_MCDC_V1_INVALID;
        if (i > 0) {
            const int order = mcdc_vector_order(&events[i - 1], &events[i]);
            if (order >= 0) return SIMPLE_MCDC_V1_INVALID;
            if (events[i - 1].source_digest == events[i].source_digest &&
                events[i - 1].decision_id == events[i].decision_id &&
                events[i - 1].condition_count != events[i].condition_count)
                return SIMPLE_MCDC_V1_INVALID;
        }
    }
    bool output_overflow = false;
    size_t group_start = 0;
    while (group_start < (size_t)event_count) {
        size_t group_end = group_start + 1;
        while (group_end < (size_t)event_count &&
               mcdc_same_identity(&events[group_start], &events[group_end]))
            ++group_end;
        if (analysis->decisions == UINT64_MAX ||
            analysis->gross_conditions > UINT64_MAX - events[group_start].condition_count)
            return SIMPLE_MCDC_V1_OVERFLOW;
        ++analysis->decisions;
        analysis->gross_conditions += events[group_start].condition_count;
        uint64_t covered_mask = 0;
        const uint64_t complete_mask =
            (UINT64_C(1) << events[group_start].condition_count) - UINT64_C(1);
        for (size_t a = group_start; a < group_end && covered_mask != complete_mask; ++a) {
            for (size_t b = a + 1; b < group_end && covered_mask != complete_mask; ++b) {
                if (analysis->pair_checks == pair_budget)
                    return SIMPLE_MCDC_V1_BUDGET_EXHAUSTED;
                ++analysis->pair_checks;
                if (events[a].outcome == events[b].outcome) continue;
                const uint64_t changed = (events[a].true_mask ^ events[b].true_mask) |
                                         (events[a].evaluated_mask ^ events[b].evaluated_mask);
                if (!changed || (changed & (changed - UINT64_C(1))) != 0) continue;
                if ((covered_mask & changed) != 0 ||
                    !(events[a].evaluated_mask & changed) ||
                    !(events[b].evaluated_mask & changed)) continue;
                uint32_t condition = 0;
                while ((UINT64_C(1) << condition) != changed) ++condition;
                if (analysis->witness_count == UINT64_MAX ||
                    analysis->covered_conditions == UINT64_MAX)
                    return SIMPLE_MCDC_V1_OVERFLOW;
                const SimpleMcdcWitnessV1 witness = {
                    events[group_start].decision_id, events[group_start].source_digest,
                    condition, 0u, events[a].owner_id, events[a].owner_sequence,
                    events[b].owner_id, events[b].owner_sequence
                };
                if (analysis->witness_count < witness_capacity)
                    witnesses[analysis->witness_count] = witness;
                else output_overflow = true;
                ++analysis->witness_count;
                ++analysis->covered_conditions;
                covered_mask |= changed;
            }
        }
        group_start = group_end;
    }
    return output_overflow ? SIMPLE_MCDC_V1_OUTPUT_TOO_SMALL : SIMPLE_MCDC_V1_OK;
}

static bool coverage_add_size(size_t a, size_t b, size_t *result) {
    if (a > SIZE_MAX - b) return false;
    *result = a + b;
    return true;
}

static bool coverage_mul_size(size_t a, size_t b, size_t *result) {
    if (a && b > SIZE_MAX / a) return false;
    *result = a * b;
    return true;
}

static char *coverage_file_copy(const char *file) {
    const char *source = file ? file : "";
    size_t size;
    if (!coverage_add_size(strlen(source), 1, &size)) abort();
    char *copy = (char *)malloc(size);
    if (copy) memcpy(copy, source, size);
    return copy;
}

static size_t coverage_escaped_file_size(const char *file) {
    size_t size = 0;
    for (const unsigned char *p = (const unsigned char *)file; *p; ++p) {
        size_t width = (*p == '%' || *p == ',' || *p == '\r' || *p == '\n') ? 3u : 1u;
        if (!coverage_add_size(size, width, &size)) abort();
    }
    return size;
}

static size_t coverage_write_escaped_file(char *out, const char *file) {
    char *start = out;
    for (const unsigned char *p = (const unsigned char *)file; *p; ++p) {
        const char *escape = NULL;
        if (*p == '%') escape = "%25";
        else if (*p == ',') escape = "%2C";
        else if (*p == '\r' || *p == '\n') escape = "%0A";
        if (escape) { memcpy(out, escape, 3); out += 3; }
        else *out++ = (char)*p;
    }
    return (size_t)(out - start);
}

static void coverage_record(CoverageRow **rows, size_t *count, uint32_t decision_id,
                            uint32_t condition_id, bool result, const char *file,
                            uint32_t line, uint32_t column) {
    char *file_copy = coverage_file_copy(file);
    if (!file_copy) abort();
    coverage_lock();
    for (size_t i = 0; i < *count; ++i) {
        CoverageRow *row = &(*rows)[i];
        if (row->decision_id == decision_id && row->condition_id == condition_id &&
            row->line == line && row->column == column && strcmp(row->file, file_copy) == 0) {
            uint64_t *counter = result ? &row->true_count : &row->false_count;
            if (*counter != UINT64_MAX) ++*counter;
            coverage_unlock();
            free(file_copy);
            return;
        }
    }
    size_t next_count;
    size_t bytes;
    if (!coverage_add_size(*count, 1, &next_count) ||
        !coverage_mul_size(next_count, sizeof(**rows), &bytes)) {
        coverage_unlock(); free(file_copy); abort();
    }
    CoverageRow *grown = (CoverageRow *)realloc(*rows, bytes);
    if (!grown) { coverage_unlock(); free(file_copy); abort(); }
    *rows = grown;
    (*rows)[*count] = (CoverageRow){decision_id, condition_id, file_copy, line, column,
                                   result ? 1u : 0u, result ? 0u : 1u};
    *count = next_count;
    coverage_unlock();
}

bool rt_coverage_enabled(void) {
    const char *value = getenv("SIMPLE_COVERAGE");
    return value && strcmp(value, "1") == 0;
}

void rt_coverage_decision_probe(uint32_t decision_id, bool result, const char *file,
                                uint32_t line, uint32_t column) {
    if (rt_coverage_enabled()) coverage_record(&g_decisions, &g_decision_count, decision_id, 0, result, file, line, column);
}

void rt_coverage_condition_probe(uint32_t decision_id, uint32_t condition_id, bool result,
                                 const char *file, uint32_t line, uint32_t column) {
    if (rt_coverage_enabled()) coverage_record(&g_conditions, &g_condition_count, decision_id, condition_id, result, file, line, column);
}

static int coverage_row_compare(const void *left, const void *right) {
    const CoverageRow *a = *(const CoverageRow * const *)left;
    const CoverageRow *b = *(const CoverageRow * const *)right;
    if (a->decision_id != b->decision_id) return a->decision_id < b->decision_id ? -1 : 1;
    if (a->condition_id != b->condition_id) return a->condition_id < b->condition_id ? -1 : 1;
    int file_order = strcmp(a->file, b->file);
    if (file_order) return file_order;
    if (a->line != b->line) return a->line < b->line ? -1 : 1;
    if (a->column != b->column) return a->column < b->column ? -1 : 1;
    return 0;
}

static void coverage_require_capacity(size_t *capacity, size_t addition) {
    if (!coverage_add_size(*capacity, addition, capacity)) abort();
}

static void coverage_append(char *out, size_t capacity, size_t *offset, const char *text) {
    size_t length = strlen(text);
    if (*offset > capacity || length > capacity - *offset) abort();
    memcpy(out + *offset, text, length);
    *offset += length;
}

/* Raw producer. `rt_coverage_dump_sdn` itself is DECLARED as a Simple `text`
 * return in every Simple declaration (src/lib/nogc_sync_mut/{ffi,sffi,io,
 * test_runner}/coverage*.spl, compiler_rust/lib/std/src/tooling/coverage.spl)
 * and as `&[I64]` (RuntimeValue) in RuntimeFuncSpec (runtime_sffi.rs:1350).
 * A malloc'd `char*` is an UNTAGGED word: tag bits 0, not TAG_HEAP, so the
 * caller decodes it as a non-string RuntimeValue. MEASURED 2026-08-10 through
 * the compiler's emitted ABI in all three C link orders. Same class as the
 * rt_file_read_text defect. The raw form is kept under an explicit _cstr name
 * for the in-process Rust caller (compiler/src/coverage.rs) and the C
 * selfcheck, both of which want the malloc'd buffer and free it with
 * rt_coverage_free_sdn. */
char *rt_coverage_dump_sdn_cstr(void) {
    static const char decision_header[] = "# Coverage Report\nversion: 1.0\ncoverage_extension: decision-condition-v1\n\ndecisions |id, file, line, column, true_count, false_count|\n";
    static const char condition_header[] = "\nconditions |decision_id, condition_id, file, line, column, true_count, false_count|\n";
    coverage_lock();
    size_t capacity = sizeof(decision_header) - 1;
    coverage_require_capacity(&capacity, sizeof(condition_header) - 1);
    for (size_t i = 0; i < g_decision_count; ++i) {
        coverage_require_capacity(&capacity, coverage_escaped_file_size(g_decisions[i].file));
        coverage_require_capacity(&capacity, 96);
    }
    for (size_t i = 0; i < g_condition_count; ++i) {
        coverage_require_capacity(&capacity, coverage_escaped_file_size(g_conditions[i].file));
        coverage_require_capacity(&capacity, 112);
    }
    coverage_require_capacity(&capacity, 1);
    size_t decision_bytes;
    size_t condition_bytes;
    if (!coverage_mul_size(g_decision_count, sizeof(CoverageRow *), &decision_bytes) ||
        !coverage_mul_size(g_condition_count, sizeof(CoverageRow *), &condition_bytes)) {
        coverage_unlock(); abort();
    }
    char *out = (char *)malloc(capacity);
    CoverageRow **decisions = decision_bytes ? (CoverageRow **)malloc(decision_bytes) : NULL;
    CoverageRow **conditions = condition_bytes ? (CoverageRow **)malloc(condition_bytes) : NULL;
    if (!out || (decision_bytes && !decisions) || (condition_bytes && !conditions)) {
        free(out); free(decisions); free(conditions); coverage_unlock(); abort();
    }
    for (size_t i = 0; i < g_decision_count; ++i) decisions[i] = &g_decisions[i];
    for (size_t i = 0; i < g_condition_count; ++i) conditions[i] = &g_conditions[i];
    if (g_decision_count > 1) qsort(decisions, g_decision_count, sizeof(*decisions), coverage_row_compare);
    if (g_condition_count > 1) qsort(conditions, g_condition_count, sizeof(*conditions), coverage_row_compare);
    size_t offset = 0;
    coverage_append(out, capacity, &offset, decision_header);
    for (size_t i = 0; i < g_decision_count; ++i) {
        const CoverageRow *row = decisions[i];
        int written = snprintf(out + offset, capacity - offset, "    %u, ", row->decision_id);
        if (written < 0 || (size_t)written >= capacity - offset) abort();
        offset += (size_t)written;
        offset += coverage_write_escaped_file(out + offset, row->file);
        written = snprintf(out + offset, capacity - offset, ", %u, %u, %llu, %llu\n", row->line, row->column,
                           (unsigned long long)row->true_count, (unsigned long long)row->false_count);
        if (written < 0 || (size_t)written >= capacity - offset) abort();
        offset += (size_t)written;
    }
    coverage_append(out, capacity, &offset, condition_header);
    for (size_t i = 0; i < g_condition_count; ++i) {
        const CoverageRow *row = conditions[i];
        int written = snprintf(out + offset, capacity - offset, "    %u, %u, ", row->decision_id, row->condition_id);
        if (written < 0 || (size_t)written >= capacity - offset) abort();
        offset += (size_t)written;
        offset += coverage_write_escaped_file(out + offset, row->file);
        written = snprintf(out + offset, capacity - offset, ", %u, %u, %llu, %llu\n", row->line, row->column,
                           (unsigned long long)row->true_count, (unsigned long long)row->false_count);
        if (written < 0 || (size_t)written >= capacity - offset) abort();
        offset += (size_t)written;
    }
    out[offset] = '\0';
    free(decisions); free(conditions); coverage_unlock();
    return out;
}

void rt_coverage_free_sdn(char *report) { free(report); }

/* Declared in runtime_native.c, which is present in every bundle that carries
 * runtime_coverage_core.c (see scripts/check/build-core-c-bootstrap-runtime-
 * capsule.shs). Returns a TAG_HEAP RuntimeValue. */
extern int64_t rt_string_new(const uint8_t *bytes, uint64_t len);

/* The ABI-correct entry point: what every Simple `extern fn
 * rt_coverage_dump_sdn() -> text` declaration and RuntimeFuncSpec promise. */
int64_t rt_coverage_dump_sdn(void) {
    char *raw = rt_coverage_dump_sdn_cstr();
    if (!raw) return rt_string_new(NULL, 0);
    int64_t value = rt_string_new((const uint8_t *)raw, (uint64_t)strlen(raw));
    free(raw);
    return value;
}

void rt_coverage_clear(void) {
    coverage_lock();
    for (size_t i = 0; i < g_decision_count; ++i) free(g_decisions[i].file);
    for (size_t i = 0; i < g_condition_count; ++i) free(g_conditions[i].file);
    free(g_decisions); free(g_conditions);
    g_decisions = NULL; g_conditions = NULL;
    g_decision_count = 0; g_condition_count = 0;
    coverage_unlock();
}
