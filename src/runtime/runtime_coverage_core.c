/* Minimal decision/condition coverage owner for the core-c-bootstrap bundle. */
#ifdef _WIN32
#include <windows.h>
#else
#include <pthread.h>
#include <sched.h>
#endif
#include <stdbool.h>
#include <stdint.h>
#include <stdatomic.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "runtime_mcdc_v1.h"

#define MCDC_COLLECTOR_MAX_SHARDS 64u
#define MCDC_WRITER_GATE_CLOSED (UINT64_C(1) << 63)
#define MCDC_WRITER_GATE_COUNT (MCDC_WRITER_GATE_CLOSED - 1u)
enum {
    MCDC_COLLECTOR_UNINITIALIZED = 0,
    MCDC_COLLECTOR_ACTIVE = 1,
    MCDC_COLLECTOR_SEALING = 2,
    MCDC_COLLECTOR_SEALED = 3
};

/* One producer reservation counter per cache line prevents independent owner
 * shards from cohering on the same hot cache line. */
typedef struct {
    size_t offset;
    size_t capacity;
    _Atomic size_t next;
    _Atomic uint64_t active_writers;
    _Atomic uint64_t compiled_writers;
    uint8_t reserved[64u - sizeof(size_t) * 3u - sizeof(uint64_t) * 2u];
} McdcCollectorShardV1;
_Static_assert(sizeof(McdcCollectorShardV1) == 64u,
               "MC/DC collector shard cache-line ABI");

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
    _Atomic uint32_t shard_count;
    _Alignas(64) McdcCollectorShardV1 shards[MCDC_COLLECTOR_MAX_SHARDS];
    _Atomic uint64_t overflow_first;
    _Atomic uint64_t overflow_count;
    _Atomic uint64_t session_id;
    uint64_t interpreter_owner_id;
    _Atomic uint64_t compiled_owner_id;
    _Atomic uint64_t compiled_owner_sequence;
    _Atomic uint64_t compiled_owner_epoch;
    _Atomic uint64_t generation;
    _Atomic uint32_t state;
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
static void mcdc_unlock(void) { LeaveCriticalSection(&g_mcdc_lock); }
#else
static pthread_mutex_t g_coverage_lock = PTHREAD_MUTEX_INITIALIZER;
static pthread_mutex_t g_mcdc_lock = PTHREAD_MUTEX_INITIALIZER;
static void coverage_lock(void) { if (pthread_mutex_lock(&g_coverage_lock) != 0) abort(); }
static void coverage_unlock(void) { if (pthread_mutex_unlock(&g_coverage_lock) != 0) abort(); }
static void mcdc_lock(void) { if (pthread_mutex_lock(&g_mcdc_lock) != 0) abort(); }
static void mcdc_unlock(void) { if (pthread_mutex_unlock(&g_mcdc_lock) != 0) abort(); }
#endif

static void mcdc_yield(void) {
#ifdef _WIN32
    (void)SwitchToThread();
#else
    (void)sched_yield();
#endif
}

int32_t rt_mcdc_collector_init_sharded_v1(void *storage,
                                         uint64_t storage_bytes,
                                         uint64_t session_id,
                                         uint32_t shard_count) {
    if (!storage || !session_id || storage_bytes < sizeof(SimpleMcdcVectorV1))
        return SIMPLE_MCDC_V1_INVALID;
    if (!shard_count || shard_count > MCDC_COLLECTOR_MAX_SHARDS)
        return SIMPLE_MCDC_V1_INVALID;
    if (((uintptr_t)storage % _Alignof(SimpleMcdcVectorV1)) != 0)
        return SIMPLE_MCDC_V1_INVALID;
    if (storage_bytes > SIZE_MAX) return SIMPLE_MCDC_V1_INVALID;
    mcdc_lock();
    if (atomic_load_explicit(&g_mcdc.state, memory_order_acquire) !=
        MCDC_COLLECTOR_UNINITIALIZED) {
        mcdc_unlock();
        return SIMPLE_MCDC_V1_BUSY;
    }
    g_mcdc.events = (SimpleMcdcVectorV1 *)storage;
    g_mcdc.capacity = (size_t)storage_bytes / sizeof(SimpleMcdcVectorV1);
    if (g_mcdc.capacity < shard_count) {
        mcdc_unlock();
        return SIMPLE_MCDC_V1_INVALID;
    }
    const uint64_t generation = atomic_load_explicit(&g_mcdc.generation,
                                                      memory_order_relaxed);
    if (generation == UINT64_MAX) {
        mcdc_unlock();
        return SIMPLE_MCDC_V1_OVERFLOW;
    }
    atomic_store_explicit(&g_mcdc.shard_count, shard_count,
                          memory_order_relaxed);
    const size_t base_capacity = g_mcdc.capacity / shard_count;
    const size_t remainder = g_mcdc.capacity % shard_count;
    size_t offset = 0;
    for (uint32_t shard = 0; shard < shard_count; ++shard) {
        const size_t capacity = base_capacity + (shard < remainder ? 1u : 0u);
        g_mcdc.shards[shard].offset = offset;
        g_mcdc.shards[shard].capacity = capacity;
        atomic_store_explicit(&g_mcdc.shards[shard].next, 0,
                              memory_order_relaxed);
        atomic_store_explicit(&g_mcdc.shards[shard].active_writers, 0,
                              memory_order_relaxed);
        atomic_store_explicit(&g_mcdc.shards[shard].compiled_writers,
                              MCDC_WRITER_GATE_CLOSED, memory_order_relaxed);
        offset += capacity;
    }
    atomic_store_explicit(&g_mcdc.overflow_first, UINT64_MAX,
                          memory_order_relaxed);
    atomic_store_explicit(&g_mcdc.overflow_count, 0, memory_order_relaxed);
    atomic_store_explicit(&g_mcdc.session_id, session_id,
                          memory_order_relaxed);
    g_mcdc.interpreter_owner_id = 0;
    atomic_store_explicit(&g_mcdc.compiled_owner_id, 0, memory_order_relaxed);
    atomic_store_explicit(&g_mcdc.compiled_owner_sequence, 0,
                          memory_order_relaxed);
    atomic_store_explicit(&g_mcdc_compiled_last_status,
                          SIMPLE_MCDC_V1_OK, memory_order_relaxed);
    atomic_store_explicit(&g_mcdc.generation, generation + 1,
                          memory_order_release);
    atomic_store_explicit(&g_mcdc.state, MCDC_COLLECTOR_ACTIVE,
                          memory_order_release);
    mcdc_unlock();
    return SIMPLE_MCDC_V1_OK;
}

int32_t rt_mcdc_collector_init_v1(void *storage, uint64_t storage_bytes,
                                  uint64_t session_id) {
    return rt_mcdc_collector_init_sharded_v1(storage, storage_bytes,
                                             session_id, 1);
}

static void mcdc_note_overflow_v1(uint64_t logical_sequence) {
    uint64_t first = atomic_load_explicit(&g_mcdc.overflow_first,
                                          memory_order_relaxed);
    while (logical_sequence < first &&
           !atomic_compare_exchange_weak_explicit(
               &g_mcdc.overflow_first, &first, logical_sequence,
               memory_order_relaxed, memory_order_relaxed)) {}
    uint64_t count = atomic_load_explicit(&g_mcdc.overflow_count,
                                          memory_order_relaxed);
    while (count != UINT64_MAX &&
           !atomic_compare_exchange_weak_explicit(
               &g_mcdc.overflow_count, &count, count + 1,
               memory_order_relaxed, memory_order_relaxed)) {}
}

static bool mcdc_reserve_shard_slot_v1(_Atomic size_t *next,
                                       size_t capacity, size_t *slot) {
    size_t current = atomic_load_explicit(next, memory_order_relaxed);
    while (current < capacity &&
           !atomic_compare_exchange_weak_explicit(
               next, &current, current + 1, memory_order_relaxed,
               memory_order_relaxed)) {}
    if (current >= capacity) return false;
    *slot = current;
    return true;
}

static bool mcdc_gate_enter_v1(_Atomic uint64_t *gate) {
    uint64_t active = atomic_load_explicit(gate, memory_order_relaxed);
    while (!(active & MCDC_WRITER_GATE_CLOSED) &&
           (active & MCDC_WRITER_GATE_COUNT) != MCDC_WRITER_GATE_COUNT &&
           !atomic_compare_exchange_weak_explicit(
               gate, &active, active + 1,
               memory_order_acquire, memory_order_relaxed)) {}
    return !(active & MCDC_WRITER_GATE_CLOSED) &&
           (active & MCDC_WRITER_GATE_COUNT) != MCDC_WRITER_GATE_COUNT;
}

static void mcdc_gate_leave_v1(_Atomic uint64_t *gate) {
    atomic_fetch_sub_explicit(gate, 1, memory_order_release);
}

static int32_t mcdc_writer_enter_v1(uint64_t generation, uint32_t shard) {
    if (!mcdc_gate_enter_v1(&g_mcdc.shards[shard].active_writers)) {
        const uint32_t state = atomic_load_explicit(&g_mcdc.state,
                                                    memory_order_acquire);
        if (state == MCDC_COLLECTOR_UNINITIALIZED)
            return SIMPLE_MCDC_V1_NOT_INITIALIZED;
        return state == MCDC_COLLECTOR_ACTIVE
            ? SIMPLE_MCDC_V1_BUSY : SIMPLE_MCDC_V1_NOT_SEALED;
    }
    const uint32_t state = atomic_load_explicit(&g_mcdc.state,
                                                memory_order_acquire);
    if (state != MCDC_COLLECTOR_ACTIVE ||
        atomic_load_explicit(&g_mcdc.generation, memory_order_acquire) !=
        generation) {
        atomic_fetch_sub_explicit(&g_mcdc.shards[shard].active_writers, 1,
                                  memory_order_release);
        return state == MCDC_COLLECTOR_UNINITIALIZED
            ? SIMPLE_MCDC_V1_NOT_INITIALIZED : SIMPLE_MCDC_V1_NOT_SEALED;
    }
    return SIMPLE_MCDC_V1_OK;
}

static void mcdc_writer_leave_v1(uint32_t shard) {
    mcdc_gate_leave_v1(&g_mcdc.shards[shard].active_writers);
}

static void mcdc_close_and_wait_writers_v1(bool compiled) {
    const uint32_t shard_count = atomic_load_explicit(&g_mcdc.shard_count,
                                                       memory_order_relaxed);
    for (uint32_t shard = 0; shard < shard_count; ++shard) {
        _Atomic uint64_t *gate = compiled
            ? &g_mcdc.shards[shard].compiled_writers
            : &g_mcdc.shards[shard].active_writers;
        atomic_fetch_or_explicit(gate, MCDC_WRITER_GATE_CLOSED,
                                 memory_order_acq_rel);
    }
    for (uint32_t shard = 0; shard < shard_count; ++shard) {
        _Atomic uint64_t *gate = compiled
            ? &g_mcdc.shards[shard].compiled_writers
            : &g_mcdc.shards[shard].active_writers;
        while ((atomic_load_explicit(gate, memory_order_acquire) &
                MCDC_WRITER_GATE_COUNT) != 0) mcdc_yield();
    }
}

static int32_t mcdc_record_vector_concurrent_v1(
        uint64_t session_id, uint64_t decision_id, uint32_t condition_count,
        uint64_t source_digest, uint64_t evaluated_mask, uint64_t true_mask,
        uint64_t owner_id, uint64_t owner_sequence, uint8_t outcome,
        uint64_t compiled_epoch) {
    if (!session_id || !decision_id || !condition_count || condition_count > 62u ||
        !source_digest ||
        !owner_id || outcome > 1u) return SIMPLE_MCDC_V1_INVALID;
    const uint64_t admitted = (UINT64_C(1) << condition_count) - UINT64_C(1);
    if ((evaluated_mask & ~admitted) || (true_mask & ~evaluated_mask))
        return SIMPLE_MCDC_V1_INVALID;
    const uint64_t generation = atomic_load_explicit(&g_mcdc.generation,
                                                      memory_order_acquire);
    const uint32_t state = atomic_load_explicit(&g_mcdc.state,
                                                memory_order_acquire);
    if (state == MCDC_COLLECTOR_UNINITIALIZED)
        return SIMPLE_MCDC_V1_NOT_INITIALIZED;
    if (state != MCDC_COLLECTOR_ACTIVE) return SIMPLE_MCDC_V1_NOT_SEALED;
    const uint32_t shard_count = atomic_load_explicit(&g_mcdc.shard_count,
                                                       memory_order_relaxed);
    if (!shard_count) return SIMPLE_MCDC_V1_NOT_INITIALIZED;
    const uint32_t primary = (uint32_t)((owner_id - 1u) % shard_count);
    uint64_t sequence = owner_sequence;
    bool sequence_assigned = compiled_epoch == 0;
    for (uint32_t attempt = 0; attempt < shard_count; ++attempt) {
        const uint32_t shard = (primary + attempt) % shard_count;
        const bool compiled_admitted = compiled_epoch != 0 &&
            mcdc_gate_enter_v1(&g_mcdc.shards[shard].compiled_writers);
        if (compiled_epoch != 0 && !compiled_admitted)
            return SIMPLE_MCDC_V1_BUSY;
        const int32_t admission = mcdc_writer_enter_v1(generation, shard);
        if (admission != SIMPLE_MCDC_V1_OK) {
            if (compiled_admitted)
                mcdc_gate_leave_v1(&g_mcdc.shards[shard].compiled_writers);
            return admission;
        }
        if (atomic_load_explicit(&g_mcdc.session_id, memory_order_relaxed) !=
            session_id) {
            mcdc_writer_leave_v1(shard);
            if (compiled_admitted)
                mcdc_gate_leave_v1(&g_mcdc.shards[shard].compiled_writers);
            return SIMPLE_MCDC_V1_SESSION_MISMATCH;
        }
        if (compiled_epoch != 0 &&
            atomic_load_explicit(&g_mcdc.compiled_owner_epoch,
                                 memory_order_acquire) != compiled_epoch) {
            mcdc_writer_leave_v1(shard);
            mcdc_gate_leave_v1(&g_mcdc.shards[shard].compiled_writers);
            return SIMPLE_MCDC_V1_BUSY;
        }
        if (!sequence_assigned) {
            sequence = atomic_load_explicit(&g_mcdc.compiled_owner_sequence,
                                            memory_order_relaxed);
            while (sequence != UINT64_MAX &&
                   !atomic_compare_exchange_weak_explicit(
                       &g_mcdc.compiled_owner_sequence, &sequence, sequence + 1,
                       memory_order_relaxed, memory_order_relaxed)) {}
            if (sequence == UINT64_MAX) {
                mcdc_note_overflow_v1(UINT64_MAX);
                mcdc_writer_leave_v1(shard);
                mcdc_gate_leave_v1(&g_mcdc.shards[shard].compiled_writers);
                return SIMPLE_MCDC_V1_OVERFLOW;
            }
            sequence_assigned = true;
        }
        size_t local = 0;
        if (mcdc_reserve_shard_slot_v1(&g_mcdc.shards[shard].next,
                                       g_mcdc.shards[shard].capacity, &local)) {
            g_mcdc.events[g_mcdc.shards[shard].offset + local] =
                (SimpleMcdcVectorV1){
                    decision_id, condition_count, 0u, source_digest,
                    evaluated_mask, true_mask, owner_id, sequence, outcome, {0}
                };
            mcdc_writer_leave_v1(shard);
            if (compiled_admitted)
                mcdc_gate_leave_v1(&g_mcdc.shards[shard].compiled_writers);
            return SIMPLE_MCDC_V1_OK;
        }
        if (attempt + 1 == shard_count) {
            mcdc_note_overflow_v1((uint64_t)g_mcdc.capacity);
            mcdc_writer_leave_v1(shard);
            if (compiled_admitted)
                mcdc_gate_leave_v1(&g_mcdc.shards[shard].compiled_writers);
            return SIMPLE_MCDC_V1_OVERFLOW;
        }
        mcdc_writer_leave_v1(shard);
        if (compiled_admitted)
            mcdc_gate_leave_v1(&g_mcdc.shards[shard].compiled_writers);
    }
    return SIMPLE_MCDC_V1_OVERFLOW;
}

int32_t rt_mcdc_record_vector_v1(uint64_t session_id, uint64_t decision_id,
                                 uint32_t condition_count,
                                 uint64_t source_digest,
                                 uint64_t evaluated_mask, uint64_t true_mask,
                                 uint64_t owner_id, uint64_t owner_sequence,
                                 uint8_t outcome) {
    const int32_t status = mcdc_record_vector_concurrent_v1(
        session_id, decision_id, condition_count, source_digest,
        evaluated_mask, true_mask, owner_id, owner_sequence, outcome, 0);
    return status;
}

int32_t rt_mcdc_configure_compiled_owner_v1(uint64_t session_id,
                                            uint64_t owner_id) {
    if (!session_id || !owner_id) return SIMPLE_MCDC_V1_INVALID;
    mcdc_lock();
    int32_t status = SIMPLE_MCDC_V1_OK;
    if (atomic_load_explicit(&g_mcdc.state, memory_order_acquire) ==
        MCDC_COLLECTOR_UNINITIALIZED) status = SIMPLE_MCDC_V1_NOT_INITIALIZED;
    else if (atomic_load_explicit(&g_mcdc.session_id, memory_order_relaxed) !=
             session_id) status = SIMPLE_MCDC_V1_SESSION_MISMATCH;
    else if (atomic_load_explicit(&g_mcdc.state, memory_order_acquire) !=
             MCDC_COLLECTOR_ACTIVE) status = SIMPLE_MCDC_V1_NOT_SEALED;
    else if (atomic_load_explicit(&g_mcdc.compiled_owner_id,
                                  memory_order_relaxed) != 0)
        status = SIMPLE_MCDC_V1_BUSY;
    else {
        const uint64_t epoch = atomic_load_explicit(
            &g_mcdc.compiled_owner_epoch, memory_order_relaxed);
        if ((epoch & 1u) || epoch > UINT64_MAX - 2u) {
            mcdc_unlock();
            return SIMPLE_MCDC_V1_OVERFLOW;
        }
        atomic_store_explicit(&g_mcdc.compiled_owner_epoch, epoch + 1,
                              memory_order_release);
        const uint32_t shard_count = atomic_load_explicit(
            &g_mcdc.shard_count, memory_order_relaxed);
        for (uint32_t shard = 0; shard < shard_count; ++shard)
            atomic_store_explicit(&g_mcdc.shards[shard].compiled_writers, 0,
                                  memory_order_relaxed);
        atomic_store_explicit(&g_mcdc.compiled_owner_sequence, 0,
                              memory_order_relaxed);
        atomic_store_explicit(&g_mcdc.compiled_owner_id, owner_id,
                              memory_order_relaxed);
        atomic_store_explicit(&g_mcdc.compiled_owner_epoch, epoch + 2,
                              memory_order_release);
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
    if (atomic_load_explicit(&g_mcdc.state, memory_order_acquire) ==
        MCDC_COLLECTOR_UNINITIALIZED) status = SIMPLE_MCDC_V1_NOT_INITIALIZED;
    else if (atomic_load_explicit(&g_mcdc.session_id, memory_order_relaxed) !=
             session_id) status = SIMPLE_MCDC_V1_SESSION_MISMATCH;
    else if (atomic_load_explicit(&g_mcdc.compiled_owner_id,
                                  memory_order_acquire) != owner_id)
        status = SIMPLE_MCDC_V1_INVALID;
    else {
        const uint64_t epoch = atomic_load_explicit(
            &g_mcdc.compiled_owner_epoch, memory_order_relaxed);
        if ((epoch & 1u) || epoch > UINT64_MAX - 2u) {
            mcdc_unlock();
            return SIMPLE_MCDC_V1_OVERFLOW;
        }
        atomic_store_explicit(&g_mcdc.compiled_owner_epoch, epoch + 1,
                              memory_order_release);
        atomic_store_explicit(&g_mcdc.compiled_owner_id, 0,
                              memory_order_relaxed);
        mcdc_close_and_wait_writers_v1(true);
        atomic_store_explicit(&g_mcdc.compiled_owner_sequence, 0,
                              memory_order_relaxed);
        atomic_store_explicit(&g_mcdc.compiled_owner_epoch, epoch + 2,
                              memory_order_release);
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
    const uint64_t epoch = atomic_load_explicit(&g_mcdc.compiled_owner_epoch,
                                                memory_order_acquire);
    const uint64_t owner_id = (epoch & 1u) ? 0 : atomic_load_explicit(
        &g_mcdc.compiled_owner_id, memory_order_relaxed);
    int32_t status;
    if (!owner_id || atomic_load_explicit(&g_mcdc.compiled_owner_epoch,
                                          memory_order_acquire) != epoch) {
        status = SIMPLE_MCDC_V1_NOT_INITIALIZED;
    } else {
        status = mcdc_record_vector_concurrent_v1(
            atomic_load_explicit(&g_mcdc.session_id, memory_order_relaxed),
            decision_id, condition_count, source_digest,
            evaluated_mask, true_mask, owner_id, 0, outcome, epoch);
    }
    mcdc_compiled_note_status(status);
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
    uint32_t state = atomic_load_explicit(&g_mcdc.state, memory_order_acquire);
    if (state == MCDC_COLLECTOR_UNINITIALIZED) {
        mcdc_unlock(); return SIMPLE_MCDC_V1_NOT_INITIALIZED;
    }
    if (atomic_load_explicit(&g_mcdc.session_id, memory_order_relaxed) !=
        session_id) { mcdc_unlock(); return SIMPLE_MCDC_V1_SESSION_MISMATCH; }
    if (state == MCDC_COLLECTOR_SEALED) { mcdc_unlock(); return SIMPLE_MCDC_V1_OK; }
    if (state != MCDC_COLLECTOR_ACTIVE) { mcdc_unlock(); return SIMPLE_MCDC_V1_BUSY; }
    atomic_store_explicit(&g_mcdc.state, MCDC_COLLECTOR_SEALING,
                          memory_order_release);
    mcdc_close_and_wait_writers_v1(false);
    atomic_store_explicit(&g_mcdc.state, MCDC_COLLECTOR_SEALED,
                          memory_order_release);
    mcdc_unlock();
    return SIMPLE_MCDC_V1_OK;
}

int32_t rt_mcdc_claim_interpreter_owner_v1(uint64_t session_id,
                                           uint64_t owner_id) {
    if (!session_id || !owner_id) return SIMPLE_MCDC_V1_INVALID;
    mcdc_lock();
    if (atomic_load_explicit(&g_mcdc.state, memory_order_acquire) !=
        MCDC_COLLECTOR_ACTIVE) { mcdc_unlock(); return SIMPLE_MCDC_V1_NOT_INITIALIZED; }
    if (atomic_load_explicit(&g_mcdc.session_id, memory_order_relaxed) !=
        session_id) { mcdc_unlock(); return SIMPLE_MCDC_V1_SESSION_MISMATCH; }
    if (g_mcdc.interpreter_owner_id != 0) { mcdc_unlock(); return SIMPLE_MCDC_V1_BUSY; }
    g_mcdc.interpreter_owner_id = owner_id;
    mcdc_unlock();
    return SIMPLE_MCDC_V1_OK;
}

int32_t rt_mcdc_release_interpreter_owner_v1(uint64_t session_id,
                                             uint64_t owner_id) {
    if (!session_id || !owner_id) return SIMPLE_MCDC_V1_INVALID;
    mcdc_lock();
    if (atomic_load_explicit(&g_mcdc.state, memory_order_acquire) ==
        MCDC_COLLECTOR_UNINITIALIZED) { mcdc_unlock(); return SIMPLE_MCDC_V1_NOT_INITIALIZED; }
    if (atomic_load_explicit(&g_mcdc.session_id, memory_order_relaxed) !=
        session_id) { mcdc_unlock(); return SIMPLE_MCDC_V1_SESSION_MISMATCH; }
    if (g_mcdc.interpreter_owner_id != owner_id) { mcdc_unlock(); return SIMPLE_MCDC_V1_SESSION_MISMATCH; }
    g_mcdc.interpreter_owner_id = 0;
    mcdc_unlock();
    return SIMPLE_MCDC_V1_OK;
}

int32_t rt_mcdc_snapshot_v1(SimpleMcdcVectorV1 *output, uint64_t output_capacity,
                            SimpleMcdcSnapshotV1 *snapshot) {
    if (!snapshot || output_capacity > SIZE_MAX) return SIMPLE_MCDC_V1_INVALID;
    mcdc_lock();
    if (atomic_load_explicit(&g_mcdc.state, memory_order_acquire) ==
        MCDC_COLLECTOR_UNINITIALIZED) {
        mcdc_unlock();
        return SIMPLE_MCDC_V1_NOT_INITIALIZED;
    }
    if (atomic_load_explicit(&g_mcdc.state, memory_order_acquire) !=
        MCDC_COLLECTOR_SEALED) { mcdc_unlock(); return SIMPLE_MCDC_V1_NOT_SEALED; }
    const uint32_t shard_count = atomic_load_explicit(&g_mcdc.shard_count,
                                                       memory_order_relaxed);
    size_t count = 0;
    for (uint32_t shard = 0; shard < shard_count; ++shard) {
        size_t used = atomic_load_explicit(&g_mcdc.shards[shard].next,
                                           memory_order_relaxed);
        if (used > g_mcdc.shards[shard].capacity)
            used = g_mcdc.shards[shard].capacity;
        count += used;
    }
    if (count > output_capacity || (count && !output)) {
        mcdc_unlock();
        return SIMPLE_MCDC_V1_OUTPUT_TOO_SMALL;
    }
    size_t written = 0;
    for (uint32_t shard = 0; shard < shard_count; ++shard) {
        size_t used = atomic_load_explicit(&g_mcdc.shards[shard].next,
                                           memory_order_relaxed);
        if (used > g_mcdc.shards[shard].capacity)
            used = g_mcdc.shards[shard].capacity;
        if (used) memmove(output + written,
                          g_mcdc.events + g_mcdc.shards[shard].offset,
                          used * sizeof(*output));
        written += used;
    }
    const uint64_t overflow_count = atomic_load_explicit(
        &g_mcdc.overflow_count, memory_order_relaxed);
    *snapshot = (SimpleMcdcSnapshotV1){
        (uint64_t)count,
        atomic_load_explicit(&g_mcdc.overflow_first, memory_order_relaxed),
        overflow_count,
        atomic_load_explicit(&g_mcdc.session_id, memory_order_relaxed),
        overflow_count ? 1u : 0u, {0}
    };
    mcdc_unlock();
    return SIMPLE_MCDC_V1_OK;
}

int32_t rt_mcdc_collector_reset_checked_v1(void) {
    mcdc_lock();
    const uint32_t prior_state = atomic_load_explicit(&g_mcdc.state,
                                                       memory_order_acquire);
    if (g_mcdc.interpreter_owner_id != 0 ||
        atomic_load_explicit(&g_mcdc.compiled_owner_id,
                             memory_order_acquire) != 0 ||
        atomic_load_explicit(&g_mcdc_dynamic_active_calls,
                             memory_order_acquire) != 0 ||
        atomic_load_explicit(&g_mcdc_dynamic_target,
                             memory_order_acquire) != NULL ||
        (atomic_load_explicit(&g_mcdc_dynamic_epoch,
                              memory_order_acquire) & 1u)) {
        mcdc_unlock();
        return SIMPLE_MCDC_V1_BUSY;
    }
    atomic_store_explicit(&g_mcdc.state, MCDC_COLLECTOR_SEALING,
                          memory_order_release);
    mcdc_close_and_wait_writers_v1(false);
    g_mcdc.events = NULL;
    g_mcdc.capacity = 0;
    atomic_store_explicit(&g_mcdc.shard_count, 0, memory_order_relaxed);
    atomic_store_explicit(&g_mcdc.overflow_first, UINT64_MAX,
                          memory_order_relaxed);
    atomic_store_explicit(&g_mcdc.overflow_count, 0, memory_order_relaxed);
    atomic_store_explicit(&g_mcdc.session_id, 0, memory_order_relaxed);
    g_mcdc.interpreter_owner_id = 0;
    atomic_store_explicit(&g_mcdc.compiled_owner_id, 0, memory_order_relaxed);
    atomic_store_explicit(&g_mcdc.compiled_owner_sequence, 0,
                          memory_order_relaxed);
    atomic_store_explicit(&g_mcdc_compiled_last_status,
                          SIMPLE_MCDC_V1_OK, memory_order_relaxed);
    (void)prior_state;
    atomic_store_explicit(&g_mcdc.state, MCDC_COLLECTOR_UNINITIALIZED,
                          memory_order_release);
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

#define MCDC_EXPR_TOKEN_LIMIT_V1 256u
#define MCDC_MANIFEST_MAX_BYTES_V1 UINT64_C(67108864)
#define MCDC_MANIFEST_MAX_PROGRAMS_V1 UINT64_C(1048576)
#define MCDC_MANIFEST_MAX_TOKENS_V1 UINT64_C(8388608)

static uint32_t mcdc_wire_u32_v1(const uint8_t *bytes) {
    return (uint32_t)bytes[0] | ((uint32_t)bytes[1] << 8) |
           ((uint32_t)bytes[2] << 16) | ((uint32_t)bytes[3] << 24);
}

static uint64_t mcdc_wire_u64_v1(const uint8_t *bytes) {
    return (uint64_t)mcdc_wire_u32_v1(bytes) |
           ((uint64_t)mcdc_wire_u32_v1(bytes + 4) << 32);
}

static bool mcdc_manifest_identity_valid_v1(const uint8_t *identity) {
    for (size_t i = 0; i < 64; ++i)
        if (!((identity[i] >= '0' && identity[i] <= '9') ||
              (identity[i] >= 'a' && identity[i] <= 'f'))) return false;
    return true;
}

typedef struct {
    uint32_t state[8];
    uint64_t byte_count;
    uint8_t block[64];
    size_t used;
} McdcSha256V1;

static uint32_t mcdc_sha256_rotr_v1(uint32_t value, unsigned shift) {
    return (value >> shift) | (value << (32u - shift));
}

static void mcdc_sha256_compress_v1(McdcSha256V1 *ctx,
                                     const uint8_t block[64]) {
    static const uint32_t k[64] = {
        0x428a2f98u,0x71374491u,0xb5c0fbcfu,0xe9b5dba5u,0x3956c25bu,0x59f111f1u,0x923f82a4u,0xab1c5ed5u,
        0xd807aa98u,0x12835b01u,0x243185beu,0x550c7dc3u,0x72be5d74u,0x80deb1feu,0x9bdc06a7u,0xc19bf174u,
        0xe49b69c1u,0xefbe4786u,0x0fc19dc6u,0x240ca1ccu,0x2de92c6fu,0x4a7484aau,0x5cb0a9dcu,0x76f988dau,
        0x983e5152u,0xa831c66du,0xb00327c8u,0xbf597fc7u,0xc6e00bf3u,0xd5a79147u,0x06ca6351u,0x14292967u,
        0x27b70a85u,0x2e1b2138u,0x4d2c6dfcu,0x53380d13u,0x650a7354u,0x766a0abbu,0x81c2c92eu,0x92722c85u,
        0xa2bfe8a1u,0xa81a664bu,0xc24b8b70u,0xc76c51a3u,0xd192e819u,0xd6990624u,0xf40e3585u,0x106aa070u,
        0x19a4c116u,0x1e376c08u,0x2748774cu,0x34b0bcb5u,0x391c0cb3u,0x4ed8aa4au,0x5b9cca4fu,0x682e6ff3u,
        0x748f82eeu,0x78a5636fu,0x84c87814u,0x8cc70208u,0x90befffau,0xa4506cebu,0xbef9a3f7u,0xc67178f2u
    };
    uint32_t w[64];
    for (size_t i = 0; i < 16u; ++i) {
        const size_t o = i * 4u;
        w[i] = ((uint32_t)block[o] << 24) | ((uint32_t)block[o + 1u] << 16) |
               ((uint32_t)block[o + 2u] << 8) | (uint32_t)block[o + 3u];
    }
    for (size_t i = 16u; i < 64u; ++i) {
        const uint32_t s0 = mcdc_sha256_rotr_v1(w[i - 15u], 7) ^
                            mcdc_sha256_rotr_v1(w[i - 15u], 18) ^ (w[i - 15u] >> 3);
        const uint32_t s1 = mcdc_sha256_rotr_v1(w[i - 2u], 17) ^
                            mcdc_sha256_rotr_v1(w[i - 2u], 19) ^ (w[i - 2u] >> 10);
        w[i] = w[i - 16u] + s0 + w[i - 7u] + s1;
    }
    uint32_t a=ctx->state[0],b=ctx->state[1],c=ctx->state[2],d=ctx->state[3];
    uint32_t e=ctx->state[4],f=ctx->state[5],g=ctx->state[6],h=ctx->state[7];
    for (size_t i = 0; i < 64u; ++i) {
        const uint32_t s1=mcdc_sha256_rotr_v1(e,6)^mcdc_sha256_rotr_v1(e,11)^mcdc_sha256_rotr_v1(e,25);
        const uint32_t t1=h+s1+((e&f)^((~e)&g))+k[i]+w[i];
        const uint32_t s0=mcdc_sha256_rotr_v1(a,2)^mcdc_sha256_rotr_v1(a,13)^mcdc_sha256_rotr_v1(a,22);
        const uint32_t t2=s0+((a&b)^(a&c)^(b&c));
        h=g;g=f;f=e;e=d+t1;d=c;c=b;b=a;a=t1+t2;
    }
    ctx->state[0]+=a;ctx->state[1]+=b;ctx->state[2]+=c;ctx->state[3]+=d;
    ctx->state[4]+=e;ctx->state[5]+=f;ctx->state[6]+=g;ctx->state[7]+=h;
}

static void mcdc_sha256_update_v1(McdcSha256V1 *ctx, const uint8_t *bytes,
                                  size_t count) {
    ctx->byte_count += count;
    while (count) {
        size_t take = 64u - ctx->used;
        if (take > count) take = count;
        memcpy(ctx->block + ctx->used, bytes, take);
        ctx->used += take; bytes += take; count -= take;
        if (ctx->used == 64u) {
            mcdc_sha256_compress_v1(ctx, ctx->block);
            ctx->used = 0;
        }
    }
}

static void mcdc_manifest_identity_compute_v1(const uint8_t *bytes,
                                              size_t byte_count,
                                              uint8_t hex[64]) {
    McdcSha256V1 ctx = {{0x6a09e667u,0xbb67ae85u,0x3c6ef372u,0xa54ff53au,
                         0x510e527fu,0x9b05688cu,0x1f83d9abu,0x5be0cd19u},0,{0},0};
    mcdc_sha256_update_v1(&ctx, bytes, 24u);
    mcdc_sha256_update_v1(&ctx, bytes + 88u, byte_count - 88u);
    const uint64_t bits = ctx.byte_count * 8u;
    const uint8_t one = 0x80u;
    const uint8_t zeroes[64] = {0};
    mcdc_sha256_update_v1(&ctx, &one, 1u);
    const size_t padding = ctx.used <= 56u ? 56u - ctx.used : 120u - ctx.used;
    mcdc_sha256_update_v1(&ctx, zeroes, padding);
    uint8_t length[8];
    for (size_t i = 0; i < 8u; ++i) length[7u - i] = (uint8_t)(bits >> (i * 8u));
    mcdc_sha256_update_v1(&ctx, length, sizeof(length));
    static const uint8_t digits[] = "0123456789abcdef";
    for (size_t i = 0; i < 8u; ++i) for (size_t j = 0; j < 4u; ++j) {
        const uint8_t value = (uint8_t)(ctx.state[i] >> (24u - j * 8u));
        hex[(i * 4u + j) * 2u] = digits[value >> 4];
        hex[(i * 4u + j) * 2u + 1u] = digits[value & 15u];
    }
}

int32_t rt_mcdc_manifest_identity_v1(const uint8_t *bytes,
                                     uint64_t byte_count,
                                     uint8_t identity_sha256[64]) {
    if (!bytes || !identity_sha256 || byte_count < 96u ||
        byte_count > MCDC_MANIFEST_MAX_BYTES_V1 || byte_count > SIZE_MAX ||
        mcdc_ranges_overlap(bytes, (size_t)byte_count, identity_sha256, 64u))
        return SIMPLE_MCDC_V1_INVALID;
    mcdc_manifest_identity_compute_v1(bytes, (size_t)byte_count,
                                      identity_sha256);
    return SIMPLE_MCDC_V1_OK;
}

static int32_t mcdc_manifest_inspect_v1(
        const uint8_t *bytes, uint64_t byte_count,
        SimpleMcdcManifestInfoV1 *info) {
    if (!bytes || !info || byte_count < 96u ||
        byte_count > MCDC_MANIFEST_MAX_BYTES_V1 || byte_count > SIZE_MAX)
        return SIMPLE_MCDC_V1_INVALID;
    if (mcdc_wire_u32_v1(bytes) != UINT32_C(0x5044434d) ||
        mcdc_wire_u32_v1(bytes + 4) != 1u ||
        !mcdc_manifest_identity_valid_v1(bytes + 24))
        return SIMPLE_MCDC_V1_INVALID;
    const uint64_t program_count = mcdc_wire_u64_v1(bytes + 8);
    const uint64_t token_count = mcdc_wire_u64_v1(bytes + 16);
    if (program_count > MCDC_MANIFEST_MAX_PROGRAMS_V1 ||
        token_count > MCDC_MANIFEST_MAX_TOKENS_V1 ||
        program_count > (UINT64_MAX - 88u) / 32u)
        return SIMPLE_MCDC_V1_INVALID;
    const uint64_t token_offset = 88u + program_count * 32u;
    if (token_count > (UINT64_MAX - token_offset) / 8u)
        return SIMPLE_MCDC_V1_INVALID;
    const uint64_t semantic_offset = token_offset + token_count * 8u;
    if (semantic_offset > byte_count || byte_count - semantic_offset < 8u)
        return SIMPLE_MCDC_V1_INVALID;

    uint64_t previous_digest = 0, previous_decision = 0;
    uint64_t expected_token_offset = 0;
    for (uint64_t row = 0; row < program_count; ++row) {
        const uint8_t *wire = bytes + 88u + row * 32u;
        const uint64_t decision = mcdc_wire_u64_v1(wire);
        const uint64_t digest = mcdc_wire_u64_v1(wire + 8);
        const uint32_t conditions = mcdc_wire_u32_v1(wire + 16);
        const uint32_t count = mcdc_wire_u32_v1(wire + 20);
        const uint64_t offset = mcdc_wire_u64_v1(wire + 24);
        if (!decision || !digest || !conditions || conditions > 62u ||
            !count || count > MCDC_EXPR_TOKEN_LIMIT_V1 ||
            offset != expected_token_offset || offset > token_count ||
            count > token_count - offset ||
            (row && (previous_digest > digest ||
                     (previous_digest == digest && previous_decision >= decision))))
            return SIMPLE_MCDC_V1_INVALID;
        size_t depth = 0;
        uint64_t referenced = 0;
        for (uint64_t index = 0; index < count; ++index) {
            const uint8_t *token = bytes + token_offset + (offset + index) * 8u;
            const uint8_t opcode = token[0];
            const uint32_t condition = mcdc_wire_u32_v1(token + 4);
            if (token[1] || token[2] || token[3]) return SIMPLE_MCDC_V1_INVALID;
            if (opcode == SIMPLE_MCDC_EXPR_CONDITION_V1) {
                if (condition >= conditions || depth == MCDC_EXPR_TOKEN_LIMIT_V1)
                    return SIMPLE_MCDC_V1_INVALID;
                const uint64_t bit = UINT64_C(1) << condition;
                if (referenced & bit) return SIMPLE_MCDC_V1_INVALID;
                referenced |= bit;
                ++depth;
            } else if (opcode == SIMPLE_MCDC_EXPR_NOT_V1) {
                if (condition || depth < 1) return SIMPLE_MCDC_V1_INVALID;
            } else if (opcode == SIMPLE_MCDC_EXPR_AND_V1 ||
                       opcode == SIMPLE_MCDC_EXPR_OR_V1) {
                if (condition || depth < 2) return SIMPLE_MCDC_V1_INVALID;
                --depth;
            } else return SIMPLE_MCDC_V1_INVALID;
        }
        if (depth != 1 || referenced != ((UINT64_C(1) << conditions) - 1u))
            return SIMPLE_MCDC_V1_INVALID;
        previous_digest = digest;
        previous_decision = decision;
        expected_token_offset += count;
    }
    if (expected_token_offset != token_count) return SIMPLE_MCDC_V1_INVALID;
    const uint64_t semantic_count = mcdc_wire_u64_v1(bytes + semantic_offset);
    if (semantic_count != program_count) return SIMPLE_MCDC_V1_INVALID;
    uint64_t cursor = semantic_offset + 8u;
    for (uint64_t row = 0; row < semantic_count; ++row) {
        if (cursor > byte_count || byte_count - cursor < 4u)
            return SIMPLE_MCDC_V1_INVALID;
        const uint32_t length = mcdc_wire_u32_v1(bytes + cursor);
        cursor += 4u;
        if (length > 4096u || length > byte_count - cursor)
            return SIMPLE_MCDC_V1_INVALID;
        cursor += length;
    }
    if (cursor != byte_count) return SIMPLE_MCDC_V1_INVALID;
    uint8_t recomputed_identity[64];
    mcdc_manifest_identity_compute_v1(bytes, (size_t)byte_count,
                                      recomputed_identity);
    uint8_t identity_difference = 0;
    for (size_t i = 0; i < sizeof(recomputed_identity); ++i)
        identity_difference |= (uint8_t)(recomputed_identity[i] ^ bytes[24u + i]);
    if (identity_difference) return SIMPLE_MCDC_V1_INVALID;
    *info = (SimpleMcdcManifestInfoV1){program_count, token_count,
                                      semantic_count, semantic_offset, {0}};
    memcpy(info->identity_sha256, bytes + 24, 64);
    return SIMPLE_MCDC_V1_OK;
}

int32_t rt_mcdc_manifest_requirements_v1(
        const uint8_t *bytes, uint64_t byte_count,
        SimpleMcdcManifestInfoV1 *info) {
    if (!info || (uintptr_t)info % _Alignof(SimpleMcdcManifestInfoV1))
        return SIMPLE_MCDC_V1_INVALID;
    if (byte_count <= SIZE_MAX &&
        mcdc_ranges_overlap(bytes, (size_t)byte_count, info, sizeof(*info)))
        return SIMPLE_MCDC_V1_INVALID;
    return mcdc_manifest_inspect_v1(bytes, byte_count, info);
}

int32_t rt_mcdc_manifest_decode_v1(
        const uint8_t *bytes, uint64_t byte_count,
        SimpleMcdcDecisionExprV1 *programs, uint64_t program_capacity,
        SimpleMcdcExprTokenV1 *tokens, uint64_t token_capacity,
        SimpleMcdcManifestInfoV1 *info) {
    if (!info || (uintptr_t)info % _Alignof(SimpleMcdcManifestInfoV1) ||
        (program_capacity && !programs) || (token_capacity && !tokens) ||
        (programs && (uintptr_t)programs % _Alignof(SimpleMcdcDecisionExprV1)) ||
        (tokens && (uintptr_t)tokens % _Alignof(SimpleMcdcExprTokenV1)))
        return SIMPLE_MCDC_V1_INVALID;
    if (byte_count <= SIZE_MAX &&
        mcdc_ranges_overlap(bytes, (size_t)byte_count, info, sizeof(*info)))
        return SIMPLE_MCDC_V1_INVALID;
    int32_t status = mcdc_manifest_inspect_v1(bytes, byte_count, info);
    if (status != SIMPLE_MCDC_V1_OK) return status;
    if (program_capacity < info->program_count || token_capacity < info->token_count)
        return SIMPLE_MCDC_V1_OUTPUT_TOO_SMALL;
    const size_t byte_size = (size_t)byte_count;
    if (mcdc_ranges_overlap(bytes, byte_size, programs,
                            (size_t)info->program_count * sizeof(*programs)) ||
        mcdc_ranges_overlap(bytes, byte_size, tokens,
                            (size_t)info->token_count * sizeof(*tokens)) ||
        mcdc_ranges_overlap(programs,
                            (size_t)info->program_count * sizeof(*programs),
                            tokens, (size_t)info->token_count * sizeof(*tokens)) ||
        mcdc_ranges_overlap(programs,
                            (size_t)info->program_count * sizeof(*programs),
                            info, sizeof(*info)) ||
        mcdc_ranges_overlap(tokens,
                            (size_t)info->token_count * sizeof(*tokens),
                            info, sizeof(*info)))
        return SIMPLE_MCDC_V1_INVALID;
    const uint64_t wire_token_offset = 88u + info->program_count * 32u;
    for (uint64_t row = 0; row < info->program_count; ++row) {
        const uint8_t *wire = bytes + 88u + row * 32u;
        programs[row] = (SimpleMcdcDecisionExprV1){
            mcdc_wire_u64_v1(wire), mcdc_wire_u64_v1(wire + 8),
            mcdc_wire_u32_v1(wire + 16), mcdc_wire_u32_v1(wire + 20),
            mcdc_wire_u64_v1(wire + 24)};
    }
    for (uint64_t index = 0; index < info->token_count; ++index) {
        const uint8_t *wire = bytes + wire_token_offset + index * 8u;
        tokens[index] = (SimpleMcdcExprTokenV1){wire[0], {0, 0, 0},
                                               mcdc_wire_u32_v1(wire + 4)};
    }
    return SIMPLE_MCDC_V1_OK;
}

static bool mcdc_program_valid_v1(const SimpleMcdcDecisionExprV1 *program,
                                  const SimpleMcdcExprTokenV1 *tokens,
                                  size_t token_count) {
    if (!program->decision_id || !program->source_digest ||
        !program->condition_count || program->condition_count > 62u ||
        !program->token_count || program->token_count > MCDC_EXPR_TOKEN_LIMIT_V1 ||
        program->token_offset > token_count ||
        program->token_count > token_count - (size_t)program->token_offset)
        return false;
    size_t depth = 0;
    uint64_t referenced = 0;
    for (size_t i = 0; i < program->token_count; ++i) {
        const SimpleMcdcExprTokenV1 *token = &tokens[program->token_offset + i];
        if (token->reserved[0] || token->reserved[1] || token->reserved[2]) return false;
        if (token->opcode == SIMPLE_MCDC_EXPR_CONDITION_V1) {
            if (token->condition_index >= program->condition_count ||
                depth == MCDC_EXPR_TOKEN_LIMIT_V1) return false;
            referenced |= UINT64_C(1) << token->condition_index;
            ++depth;
        } else if (token->opcode == SIMPLE_MCDC_EXPR_NOT_V1) {
            if (token->condition_index || depth < 1) return false;
        } else if (token->opcode == SIMPLE_MCDC_EXPR_AND_V1 ||
                   token->opcode == SIMPLE_MCDC_EXPR_OR_V1) {
            if (token->condition_index || depth < 2) return false;
            --depth;
        } else return false;
    }
    const uint64_t complete = (UINT64_C(1) << program->condition_count) - 1u;
    return depth == 1 && referenced == complete;
}

static bool mcdc_eval_program_v1(const SimpleMcdcDecisionExprV1 *program,
                                 const SimpleMcdcExprTokenV1 *tokens,
                                 uint64_t values) {
    bool stack[MCDC_EXPR_TOKEN_LIMIT_V1];
    size_t depth = 0;
    for (size_t i = 0; i < program->token_count; ++i) {
        const SimpleMcdcExprTokenV1 *token = &tokens[program->token_offset + i];
        if (token->opcode == SIMPLE_MCDC_EXPR_CONDITION_V1)
            stack[depth++] = (values & (UINT64_C(1) << token->condition_index)) != 0;
        else if (token->opcode == SIMPLE_MCDC_EXPR_NOT_V1)
            stack[depth - 1] = !stack[depth - 1];
        else {
            const bool right = stack[--depth];
            if (token->opcode == SIMPLE_MCDC_EXPR_AND_V1) stack[depth - 1] &= right;
            else stack[depth - 1] |= right;
        }
    }
    return stack[0];
}

static int32_t mcdc_observation_preserved_v1(
    const SimpleMcdcVectorV1 *event, const SimpleMcdcVectorV1 *other,
    uint64_t target, const SimpleMcdcDecisionExprV1 *program,
    const SimpleMcdcExprTokenV1 *tokens, uint64_t budget,
    uint64_t *checks) {
    const uint64_t complete = (UINT64_C(1) << event->condition_count) - 1u;
    const uint64_t changed_values = (event->true_mask ^ other->true_mask) &
                                    event->evaluated_mask & other->evaluated_mask;
    uint64_t variable = ((~event->evaluated_mask & complete) | changed_values) & ~target;
    uint64_t assignment = 0;
    for (;;) {
        if (*checks == budget) return SIMPLE_MCDC_V1_BUDGET_EXHAUSTED;
        ++*checks;
        const uint64_t values = (event->true_mask & ~variable) | assignment;
        if (mcdc_eval_program_v1(program, tokens, values) != (event->outcome != 0))
            return SIMPLE_MCDC_V1_INVALID;
        if (assignment == variable) break;
        assignment = (assignment - variable) & variable;
    }
    return SIMPLE_MCDC_V1_OK;
}

int32_t rt_mcdc_analyze_masking_v1(
    const SimpleMcdcVectorV1 *events, uint64_t event_count,
    const SimpleMcdcDecisionExprV1 *programs, uint64_t program_count,
    const SimpleMcdcExprTokenV1 *tokens, uint64_t token_count,
    SimpleMcdcWitnessV1 *witnesses, uint64_t witness_capacity,
    uint64_t proof_budget, SimpleMcdcAnalysisV1 *analysis) {
    if (!analysis || (event_count && !events) || (program_count && !programs) ||
        (token_count && !tokens) || (witness_capacity && !witnesses) ||
        event_count > SIZE_MAX || program_count > SIZE_MAX || token_count > SIZE_MAX ||
        witness_capacity > SIZE_MAX) return SIMPLE_MCDC_V1_INVALID;
    if ((events && (uintptr_t)events % _Alignof(SimpleMcdcVectorV1)) ||
        (programs && (uintptr_t)programs % _Alignof(SimpleMcdcDecisionExprV1)) ||
        (tokens && (uintptr_t)tokens % _Alignof(SimpleMcdcExprTokenV1)) ||
        (witnesses && (uintptr_t)witnesses % _Alignof(SimpleMcdcWitnessV1)) ||
        ((uintptr_t)analysis % _Alignof(SimpleMcdcAnalysisV1)) ||
        event_count > SIZE_MAX / sizeof(*events) ||
        program_count > SIZE_MAX / sizeof(*programs) ||
        token_count > SIZE_MAX / sizeof(*tokens) ||
        witness_capacity > SIZE_MAX / sizeof(*witnesses))
        return SIMPLE_MCDC_V1_INVALID;
    const size_t event_bytes = (size_t)event_count * sizeof(*events);
    const size_t program_bytes = (size_t)program_count * sizeof(*programs);
    const size_t token_bytes = (size_t)token_count * sizeof(*tokens);
    const size_t witness_bytes = (size_t)witness_capacity * sizeof(*witnesses);
    if (mcdc_ranges_overlap(events, event_bytes, witnesses, witness_bytes) ||
        mcdc_ranges_overlap(programs, program_bytes, witnesses, witness_bytes) ||
        mcdc_ranges_overlap(tokens, token_bytes, witnesses, witness_bytes) ||
        mcdc_ranges_overlap(events, event_bytes, analysis, sizeof(*analysis)) ||
        mcdc_ranges_overlap(programs, program_bytes, analysis, sizeof(*analysis)) ||
        mcdc_ranges_overlap(tokens, token_bytes, analysis, sizeof(*analysis)) ||
        mcdc_ranges_overlap(witnesses, witness_bytes, analysis, sizeof(*analysis)))
        return SIMPLE_MCDC_V1_INVALID;
    *analysis = (SimpleMcdcAnalysisV1){0, 0, 0, 0, 0, proof_budget};
    if (program_count == 0 && event_count != 0) return SIMPLE_MCDC_V1_INVALID;
    for (size_t p = 0; p < (size_t)program_count; ++p) {
        if (!mcdc_program_valid_v1(&programs[p], tokens, (size_t)token_count))
            return SIMPLE_MCDC_V1_INVALID;
        if (p && (programs[p - 1].source_digest > programs[p].source_digest ||
                  (programs[p - 1].source_digest == programs[p].source_digest &&
                   programs[p - 1].decision_id >= programs[p].decision_id)))
            return SIMPLE_MCDC_V1_INVALID;
    }
    bool output_overflow = false;
    size_t start = 0;
    for (size_t p = 0; p < (size_t)program_count; ++p) {
        const SimpleMcdcDecisionExprV1 *program = &programs[p];
        if (analysis->decisions == UINT64_MAX ||
            analysis->gross_conditions > UINT64_MAX - program->condition_count)
            return SIMPLE_MCDC_V1_OVERFLOW;
        ++analysis->decisions;
        analysis->gross_conditions += program->condition_count;
        if (start >= (size_t)event_count) continue;
        if (events[start].source_digest < program->source_digest ||
            (events[start].source_digest == program->source_digest &&
             events[start].decision_id < program->decision_id))
            return SIMPLE_MCDC_V1_INVALID;
        if (events[start].source_digest > program->source_digest ||
            (events[start].source_digest == program->source_digest &&
             events[start].decision_id > program->decision_id))
            continue;
        size_t end = start;
        while (end < (size_t)event_count && events[end].decision_id == program->decision_id &&
               events[end].source_digest == program->source_digest) {
            if (!mcdc_vector_valid(&events[end]) ||
                events[end].condition_count != program->condition_count ||
                (end > start && mcdc_vector_order(&events[end - 1], &events[end]) >= 0))
                return SIMPLE_MCDC_V1_INVALID;
            ++end;
        }
        uint64_t covered = 0;
        for (uint32_t condition = 0; condition < program->condition_count; ++condition) {
            const uint64_t target = UINT64_C(1) << condition;
            for (unsigned policy = 0; policy < 2 && !(covered & target); ++policy) {
                for (size_t a = start; a < end && !(covered & target); ++a) {
                    for (size_t b = a + 1; b < end && !(covered & target); ++b) {
                        if (events[a].outcome == events[b].outcome ||
                            !(events[a].evaluated_mask & target) ||
                            !(events[b].evaluated_mask & target) ||
                            !((events[a].true_mask ^ events[b].true_mask) & target)) continue;
                        const uint64_t changed = (events[a].true_mask ^ events[b].true_mask) |
                                                 (events[a].evaluated_mask ^ events[b].evaluated_mask);
                        if (policy == 0 && changed != target) continue;
                        if (policy == 1 && changed == target) continue;
                        if (policy == 1) {
                            int32_t status = mcdc_observation_preserved_v1(
                                &events[a], &events[b], target, program, tokens,
                                proof_budget, &analysis->pair_checks);
                            if (status == SIMPLE_MCDC_V1_BUDGET_EXHAUSTED) return status;
                            if (status != SIMPLE_MCDC_V1_OK) continue;
                            status = mcdc_observation_preserved_v1(
                                &events[b], &events[a], target, program, tokens,
                                proof_budget, &analysis->pair_checks);
                            if (status == SIMPLE_MCDC_V1_BUDGET_EXHAUSTED) return status;
                            if (status != SIMPLE_MCDC_V1_OK) continue;
                        } else {
                            if (analysis->pair_checks == proof_budget)
                                return SIMPLE_MCDC_V1_BUDGET_EXHAUSTED;
                            ++analysis->pair_checks;
                        }
                        if (analysis->witness_count < witness_capacity)
                            witnesses[analysis->witness_count] = (SimpleMcdcWitnessV1){
                                program->decision_id, program->source_digest, condition,
                                policy, events[a].owner_id, events[a].owner_sequence,
                                events[b].owner_id, events[b].owner_sequence};
                        else output_overflow = true;
                        if (analysis->witness_count == UINT64_MAX ||
                            analysis->covered_conditions == UINT64_MAX)
                            return SIMPLE_MCDC_V1_OVERFLOW;
                        ++analysis->witness_count;
                        ++analysis->covered_conditions;
                        covered |= target;
                    }
                }
            }
        }
        start = end;
    }
    if (start != (size_t)event_count) return SIMPLE_MCDC_V1_INVALID;
    return output_overflow ? SIMPLE_MCDC_V1_OUTPUT_TOO_SMALL : SIMPLE_MCDC_V1_OK;
}

int32_t rt_mcdc_analyze_masking_mcdp_v1(
        const SimpleMcdcVectorV1 *events, uint64_t event_count,
        const uint8_t *bytes, uint64_t byte_count,
        SimpleMcdcDecisionExprV1 *program_workspace,
        uint64_t program_capacity,
        SimpleMcdcExprTokenV1 *token_workspace, uint64_t token_capacity,
        SimpleMcdcWitnessV1 *witnesses, uint64_t witness_capacity,
        uint64_t proof_budget, SimpleMcdcAnalysisV1 *analysis,
        SimpleMcdcManifestInfoV1 *info) {
    if (!analysis || !info || event_count > SIZE_MAX ||
        witness_capacity > SIZE_MAX ||
        program_capacity > MCDC_MANIFEST_MAX_PROGRAMS_V1 ||
        token_capacity > MCDC_MANIFEST_MAX_TOKENS_V1 ||
        event_count > SIZE_MAX / sizeof(*events) ||
        witness_capacity > SIZE_MAX / sizeof(*witnesses))
        return SIMPLE_MCDC_V1_INVALID;
    const size_t event_bytes = (size_t)event_count * sizeof(*events);
    const size_t program_bytes = (size_t)program_capacity * sizeof(*program_workspace);
    const size_t token_bytes = (size_t)token_capacity * sizeof(*token_workspace);
    const size_t witness_bytes = (size_t)witness_capacity * sizeof(*witnesses);
    if (mcdc_ranges_overlap(events, event_bytes, program_workspace, program_bytes) ||
        mcdc_ranges_overlap(events, event_bytes, token_workspace, token_bytes) ||
        mcdc_ranges_overlap(events, event_bytes, info, sizeof(*info)) ||
        mcdc_ranges_overlap(program_workspace, program_bytes,
                            witnesses, witness_bytes) ||
        mcdc_ranges_overlap(token_workspace, token_bytes,
                            witnesses, witness_bytes) ||
        mcdc_ranges_overlap(info, sizeof(*info), witnesses, witness_bytes) ||
        mcdc_ranges_overlap(program_workspace, program_bytes,
                            analysis, sizeof(*analysis)) ||
        mcdc_ranges_overlap(token_workspace, token_bytes,
                            analysis, sizeof(*analysis)) ||
        mcdc_ranges_overlap(info, sizeof(*info), analysis, sizeof(*analysis)))
        return SIMPLE_MCDC_V1_INVALID;
    const int32_t status = rt_mcdc_manifest_decode_v1(
        bytes, byte_count, program_workspace, program_capacity,
        token_workspace, token_capacity, info);
    if (status != SIMPLE_MCDC_V1_OK) return status;
    return rt_mcdc_analyze_masking_v1(
        events, event_count, program_workspace, info->program_count,
        token_workspace, info->token_count, witnesses, witness_capacity,
        proof_budget, analysis);
}

static uint64_t mcdc_popcount_v1(uint64_t value) {
    uint64_t count = 0;
    while (value) { value &= value - UINT64_C(1); ++count; }
    return count;
}

static bool mcdc_reason_equals_ascii_v1(const SimpleMcdcExclusionV1 *row,
                                        const char *literal) {
    const size_t length = strlen(literal);
    if (row->reason_length != length) return false;
    for (size_t i = 0; i < length; ++i) {
        uint8_t c = row->reason[i];
        if (c >= 'A' && c <= 'Z') c = (uint8_t)(c + ('a' - 'A'));
        if (c != (uint8_t)literal[i]) return false;
    }
    return true;
}

static bool mcdc_exclusion_reason_valid_v1(const SimpleMcdcExclusionV1 *row) {
    if (row->reason_length < 12u ||
        row->reason_length > SIMPLE_MCDC_EXCLUSION_REASON_BYTES_V1) return false;
    bool visible = false, separator = false;
    for (uint32_t i = 0; i < row->reason_length; ++i) {
        const uint8_t c = row->reason[i];
        if (c < 0x20u || c > 0x7eu) return false;
        visible |= (c != ' ' && c != '\t');
        separator |= (c == ' ' || c == '-' || c == '_' || c == ':');
    }
    for (uint32_t i = row->reason_length;
         i < SIMPLE_MCDC_EXCLUSION_REASON_BYTES_V1; ++i)
        if (row->reason[i] != 0) return false;
    return visible && separator &&
        !mcdc_reason_equals_ascii_v1(row, "not available") &&
        !mcdc_reason_equals_ascii_v1(row, "cannot reproduce") &&
        !mcdc_reason_equals_ascii_v1(row, "unknown reason") &&
        !mcdc_reason_equals_ascii_v1(row, "skip this test");
}

static int mcdc_exclusion_order_v1(const SimpleMcdcExclusionV1 *a,
                                   const SimpleMcdcExclusionV1 *b) {
    if (a->source_digest != b->source_digest)
        return a->source_digest < b->source_digest ? -1 : 1;
    if (a->decision_id != b->decision_id)
        return a->decision_id < b->decision_id ? -1 : 1;
    return 0;
}

static void mcdc_sha256_scalar_le_v1(McdcSha256V1 *ctx, uint64_t value,
                                     size_t width) {
    uint8_t wire[8];
    for (size_t i = 0; i < width; ++i) wire[i] = (uint8_t)(value >> (i * 8u));
    mcdc_sha256_update_v1(ctx, wire, width);
}

static void mcdc_sha256_finish_hex_v1(McdcSha256V1 *ctx, uint8_t hex[64]) {
    const uint64_t bits = ctx->byte_count * UINT64_C(8);
    const uint8_t one = 0x80u, zeroes[64] = {0};
    mcdc_sha256_update_v1(ctx, &one, 1u);
    const size_t padding = ctx->used <= 56u ? 56u - ctx->used : 120u - ctx->used;
    mcdc_sha256_update_v1(ctx, zeroes, padding);
    uint8_t length[8];
    for (size_t i = 0; i < 8u; ++i) length[7u - i] = (uint8_t)(bits >> (i * 8u));
    mcdc_sha256_update_v1(ctx, length, sizeof(length));
    static const uint8_t digits[] = "0123456789abcdef";
    for (size_t i = 0; i < 8u; ++i) for (size_t j = 0; j < 4u; ++j) {
        const uint8_t value = (uint8_t)(ctx->state[i] >> (24u - j * 8u));
        hex[(i * 4u + j) * 2u] = digits[value >> 4];
        hex[(i * 4u + j) * 2u + 1u] = digits[value & 15u];
    }
}

int32_t rt_mcdc_report_mcdp_v1(
        SimpleMcdcVectorV1 *events, uint64_t event_count,
        const uint8_t *manifest_bytes, uint64_t manifest_byte_count,
        const SimpleMcdcExclusionV1 *exclusions, uint64_t exclusion_count,
        uint64_t current_epoch, uint32_t mode,
        SimpleMcdcDecisionExprV1 *programs, uint64_t program_capacity,
        SimpleMcdcExprTokenV1 *tokens, uint64_t token_capacity,
        SimpleMcdcWitnessV1 *witnesses, uint64_t witness_capacity,
        uint64_t proof_budget, SimpleMcdcReportV1 *report) {
    if (!report || !manifest_bytes || (event_count && !events) ||
        (exclusion_count && !exclusions) || mode > SIMPLE_MCDC_REPORT_BETA_V1 ||
        event_count > SIZE_MAX || exclusion_count > SIZE_MAX ||
        manifest_byte_count > SIZE_MAX ||
        program_capacity > SIZE_MAX / sizeof(*programs) ||
        token_capacity > SIZE_MAX / sizeof(*tokens) ||
        witness_capacity > SIZE_MAX / sizeof(*witnesses) ||
        event_count > SIZE_MAX / sizeof(*events) ||
        exclusion_count > SIZE_MAX / sizeof(*exclusions) ||
        ((uintptr_t)report % _Alignof(SimpleMcdcReportV1)) ||
        (exclusions && (uintptr_t)exclusions % _Alignof(SimpleMcdcExclusionV1)))
        return SIMPLE_MCDC_V1_INVALID;
    const size_t report_event_bytes = (size_t)event_count * sizeof(*events);
    const size_t report_exclusion_bytes =
        (size_t)exclusion_count * sizeof(*exclusions);
    if (mcdc_ranges_overlap(report, sizeof(*report), events, report_event_bytes) ||
        mcdc_ranges_overlap(report, sizeof(*report), manifest_bytes,
                            (size_t)manifest_byte_count) ||
        mcdc_ranges_overlap(report, sizeof(*report), exclusions,
                            report_exclusion_bytes) ||
        mcdc_ranges_overlap(report, sizeof(*report), programs,
                            (size_t)program_capacity * sizeof(*programs)) ||
        mcdc_ranges_overlap(report, sizeof(*report), tokens,
                            (size_t)token_capacity * sizeof(*tokens)) ||
        mcdc_ranges_overlap(report, sizeof(*report), witnesses,
                            (size_t)witness_capacity * sizeof(*witnesses)) ||
        mcdc_ranges_overlap(exclusions, report_exclusion_bytes, events,
                            report_event_bytes) ||
        mcdc_ranges_overlap(events, report_event_bytes, manifest_bytes,
                            (size_t)manifest_byte_count) ||
        mcdc_ranges_overlap(exclusions, report_exclusion_bytes, programs,
                            (size_t)program_capacity * sizeof(*programs)) ||
        mcdc_ranges_overlap(exclusions, report_exclusion_bytes, tokens,
                            (size_t)token_capacity * sizeof(*tokens)) ||
        mcdc_ranges_overlap(exclusions, report_exclusion_bytes, witnesses,
                            (size_t)witness_capacity * sizeof(*witnesses)))
        return SIMPLE_MCDC_V1_INVALID;
    *report = (SimpleMcdcReportV1){0};
    report->mode = mode;
    if (rt_mcdc_sort_vectors_v1(events, event_count) != SIMPLE_MCDC_V1_OK)
        return SIMPLE_MCDC_V1_INVALID;

    SimpleMcdcAnalysisV1 analysis;
    SimpleMcdcManifestInfoV1 info;
    int32_t status = rt_mcdc_analyze_masking_mcdp_v1(
        events, event_count, manifest_bytes, manifest_byte_count,
        programs, program_capacity, tokens, token_capacity,
        witnesses, witness_capacity, proof_budget, &analysis, &info);
    if (status != SIMPLE_MCDC_V1_OK) return status;
    /* A complete report must retain every witness; truncated evidence can
     * never be promoted into a coverage percentage. */
    if (analysis.witness_count > witness_capacity)
        return SIMPLE_MCDC_V1_OUTPUT_TOO_SMALL;

    uint64_t excluded_total = 0;
    size_t exclusion_index = 0;
    for (size_t p = 0; p < (size_t)info.program_count; ++p) {
        const SimpleMcdcDecisionExprV1 *program = &programs[p];
        if (exclusion_index < (size_t)exclusion_count &&
            exclusions[exclusion_index].source_digest < program->source_digest)
            return SIMPLE_MCDC_V1_EXCLUSION_INVALID;
        if (exclusion_index < (size_t)exclusion_count &&
            exclusions[exclusion_index].source_digest == program->source_digest &&
            exclusions[exclusion_index].decision_id < program->decision_id)
            return SIMPLE_MCDC_V1_EXCLUSION_INVALID;
        if (exclusion_index == (size_t)exclusion_count ||
            exclusions[exclusion_index].source_digest != program->source_digest ||
            exclusions[exclusion_index].decision_id != program->decision_id) continue;
        const SimpleMcdcExclusionV1 *row = &exclusions[exclusion_index];
        const uint64_t complete = (UINT64_C(1) << program->condition_count) - 1u;
        if (!row->decision_id || !row->source_digest || !row->condition_mask ||
            (row->condition_mask & ~complete) || !row->capability_id ||
            (!row->evidence_digest_hi && !row->evidence_digest_lo) ||
            !row->owner_id ||
            row->condition_count != program->condition_count || row->reserved0 ||
            row->kind != SIMPLE_MCDC_EXCLUSION_CAPABILITY_UNAVAILABLE_V1 ||
            row->reviewed_epoch > current_epoch || current_epoch > row->expires_epoch ||
            !mcdc_exclusion_reason_valid_v1(row))
            return SIMPLE_MCDC_V1_EXCLUSION_INVALID;
        if (exclusion_index &&
            mcdc_exclusion_order_v1(&exclusions[exclusion_index - 1], row) >= 0)
            return SIMPLE_MCDC_V1_EXCLUSION_INVALID;
        const uint64_t add = mcdc_popcount_v1(row->condition_mask);
        if (excluded_total > UINT64_MAX - add)
            return SIMPLE_MCDC_V1_OVERFLOW;
        excluded_total += add;
        ++exclusion_index;
    }
    if (exclusion_index != (size_t)exclusion_count ||
        excluded_total > analysis.gross_conditions)
        return SIMPLE_MCDC_V1_EXCLUSION_INVALID;

    uint64_t covered_eligible = 0;
    size_t witness_exclusion = 0;
    for (size_t w = 0; w < (size_t)analysis.witness_count; ++w) {
        const SimpleMcdcWitnessV1 *witness = &witnesses[w];
        uint64_t excluded_mask = 0;
        while (witness_exclusion < (size_t)exclusion_count &&
               (exclusions[witness_exclusion].source_digest < witness->source_digest ||
                (exclusions[witness_exclusion].source_digest == witness->source_digest &&
                 exclusions[witness_exclusion].decision_id < witness->decision_id)))
            ++witness_exclusion;
        if (witness_exclusion < (size_t)exclusion_count &&
            exclusions[witness_exclusion].decision_id == witness->decision_id &&
            exclusions[witness_exclusion].source_digest == witness->source_digest)
            excluded_mask = exclusions[witness_exclusion].condition_mask;
        if (!(excluded_mask & (UINT64_C(1) << witness->condition_index)))
            ++covered_eligible;
    }
    const uint64_t eligible = analysis.gross_conditions - excluded_total;
    if (covered_eligible > eligible) return SIMPLE_MCDC_V1_INVALID;

    report->decisions = analysis.decisions;
    report->gross_conditions = analysis.gross_conditions;
    report->excluded_conditions = excluded_total;
    report->eligible_conditions = eligible;
    report->covered_eligible_conditions = covered_eligible;
    report->uncovered_eligible_conditions = eligible - covered_eligible;
    report->validated_exclusions = exclusion_count;
    report->event_count = event_count;
    report->witness_count = analysis.witness_count;
    report->proof_checks = analysis.pair_checks;
    report->gate_passed = covered_eligible == eligible ? 1u : 0u;
    if (!eligible) {
        report->gate_passed = 0;
        return SIMPLE_MCDC_V1_EMPTY_DENOMINATOR;
    }

    McdcSha256V1 digest = {{0x6a09e667u,0xbb67ae85u,0x3c6ef372u,0xa54ff53au,
                            0x510e527fu,0x9b05688cu,0x1f83d9abu,0x5be0cd19u},0,{0},0};
    static const uint8_t domain[] = "simple-mcdc-report-v1";
    mcdc_sha256_update_v1(&digest, domain, sizeof(domain) - 1u);
    mcdc_sha256_update_v1(&digest, info.identity_sha256, 64u);
    mcdc_sha256_scalar_le_v1(&digest, mode, 4u);
    mcdc_sha256_scalar_le_v1(&digest, current_epoch, 8u);
    for (size_t i = 0; i < (size_t)event_count; ++i) {
        const SimpleMcdcVectorV1 *v = &events[i];
        mcdc_sha256_scalar_le_v1(&digest, v->decision_id, 8u);
        mcdc_sha256_scalar_le_v1(&digest, v->condition_count, 4u);
        mcdc_sha256_scalar_le_v1(&digest, v->source_digest, 8u);
        mcdc_sha256_scalar_le_v1(&digest, v->evaluated_mask, 8u);
        mcdc_sha256_scalar_le_v1(&digest, v->true_mask, 8u);
        mcdc_sha256_scalar_le_v1(&digest, v->owner_id, 8u);
        mcdc_sha256_scalar_le_v1(&digest, v->owner_sequence, 8u);
        mcdc_sha256_scalar_le_v1(&digest, v->outcome, 1u);
    }
    for (size_t i = 0; i < (size_t)exclusion_count; ++i) {
        const SimpleMcdcExclusionV1 *x = &exclusions[i];
        mcdc_sha256_scalar_le_v1(&digest, x->decision_id, 8u);
        mcdc_sha256_scalar_le_v1(&digest, x->source_digest, 8u);
        mcdc_sha256_scalar_le_v1(&digest, x->condition_mask, 8u);
        mcdc_sha256_scalar_le_v1(&digest, x->capability_id, 8u);
        mcdc_sha256_scalar_le_v1(&digest, x->evidence_digest_hi, 8u);
        mcdc_sha256_scalar_le_v1(&digest, x->evidence_digest_lo, 8u);
        mcdc_sha256_scalar_le_v1(&digest, x->owner_id, 8u);
        mcdc_sha256_scalar_le_v1(&digest, x->reviewed_epoch, 8u);
        mcdc_sha256_scalar_le_v1(&digest, x->expires_epoch, 8u);
        mcdc_sha256_scalar_le_v1(&digest, x->condition_count, 4u);
        mcdc_sha256_scalar_le_v1(&digest, x->kind, 4u);
        mcdc_sha256_scalar_le_v1(&digest, x->reason_length, 4u);
        mcdc_sha256_update_v1(&digest, x->reason, x->reason_length);
    }
    for (size_t i = 0; i < (size_t)analysis.witness_count; ++i) {
        const SimpleMcdcWitnessV1 *w = &witnesses[i];
        mcdc_sha256_scalar_le_v1(&digest, w->decision_id, 8u);
        mcdc_sha256_scalar_le_v1(&digest, w->source_digest, 8u);
        mcdc_sha256_scalar_le_v1(&digest, w->condition_index, 4u);
        mcdc_sha256_scalar_le_v1(&digest, w->policy, 4u);
        mcdc_sha256_scalar_le_v1(&digest, w->owner_a, 8u);
        mcdc_sha256_scalar_le_v1(&digest, w->sequence_a, 8u);
        mcdc_sha256_scalar_le_v1(&digest, w->owner_b, 8u);
        mcdc_sha256_scalar_le_v1(&digest, w->sequence_b, 8u);
    }
    mcdc_sha256_finish_hex_v1(&digest, report->provenance_sha256);
    if (mode == SIMPLE_MCDC_REPORT_NORMAL_V1 && !report->gate_passed)
        return SIMPLE_MCDC_V1_GATE_FAILED;
    return SIMPLE_MCDC_V1_OK;
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
