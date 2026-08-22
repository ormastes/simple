#include "hal_provider_sealed_facade_v1.h"
#include "hal_provider_sealed_session_v1.h"

#include <stdatomic.h>
#include <stddef.h>
#include <stdio.h>
#include <string.h>

enum { HAL_FACADE_SLOT_COUNT_V1 = 4 };
enum { HAL_CLOCK_OPERATION_ID_V2 = 101 };

static const char *const HAL_LAUNCHER_V1 =
    "/usr/libexec/simple/hal-provider-launcher-v1";
static const char *const HAL_PURE_V1 =
    "/usr/libexec/simple/hal-provider-pure-v1";
static const char *const HAL_C_V1 =
    "/usr/libexec/simple/hal-provider-c-v1";
static const char *const HAL_RUST_V1 =
    "/usr/libexec/simple/hal-provider-rust-v1";

typedef struct {
    HalSealedSessionV1 session;
    HalSealedSessionConfigV1 config;
    int64_t result[HAL_SEALED_FACADE_LANES_V1]
                  [HAL_SEALED_FACADE_RESULT_FIELDS_V1];
    int64_t result_v2[HAL_SEALED_FACADE_LANES_V1]
                     [HAL_SEALED_FACADE_RESULT_FIELDS_V2];
    uint64_t generation;
    _Atomic int state; /* 0 free, 1 maintenance, 2 sealed, 3 invoking */
    int32_t last_status;
    int32_t completed_mask;
    int32_t result_schema;
    int32_t difference_mask_v2;
    int32_t commit_allowed_v2;
    int32_t selected_provider_v2;
    int64_t last_v2_invocation;
} HalSealedFacadeSlotV1;

static HalSealedFacadeSlotV1 g_slots[HAL_FACADE_SLOT_COUNT_V1];
static atomic_flag g_maintenance_lock = ATOMIC_FLAG_INIT;
static _Atomic uint64_t g_generation = 1;

/* Immutable after init. Each entry owns one independently sealed process set;
 * busy is the bounded ingress lease. No hot call allocates, spawns, reads the
 * environment, or waits for another caller. */
typedef struct {
    uint64_t handle[HAL_FACADE_SLOT_COUNT_V1];
    _Atomic int busy[HAL_FACADE_SLOT_COUNT_V1];
    int32_t run_mode;
    int32_t preferred_provider;
    _Atomic uint64_t invocation;
    _Atomic int state; /* 0 empty, 1 initializing, 2 sealed, 3 shutting down */
} HalClockDispatchOwnerV2;

static HalClockDispatchOwnerV2 g_clock_owner_v2;

extern int64_t rt_time_now_nanos(void);

static void maintenance_lock(void) {
    while (atomic_flag_test_and_set_explicit(&g_maintenance_lock,
                                              memory_order_acquire)) { }
}

static void maintenance_unlock(void) {
    atomic_flag_clear_explicit(&g_maintenance_lock, memory_order_release);
}

static uint64_t make_handle(size_t slot, uint64_t generation) {
    return (generation << 8) | (uint64_t)(slot + 1);
}

static HalSealedFacadeSlotV1 *lookup(uint64_t handle, size_t *index_out) {
    size_t index;
    uint64_t generation;
    if (handle == 0) return NULL;
    index = (size_t)((handle & UINT64_C(255)) - 1);
    generation = handle >> 8;
    if (index >= HAL_FACADE_SLOT_COUNT_V1 || generation == 0 ||
        g_slots[index].generation != generation ||
        atomic_load_explicit(&g_slots[index].state,
                             memory_order_acquire) == 0) return NULL;
    if (index_out) *index_out = index;
    return &g_slots[index];
}

static int parse_i64(const unsigned char *p, size_t n, size_t *at,
                     int64_t *out) {
    uint64_t magnitude = 0;
    int negative = 0, digits = 0;
    if (*at < n && p[*at] == '-') { negative = 1; (*at)++; }
    while (*at < n && p[*at] != '|' && p[*at] != '\n') {
        unsigned digit;
        if (p[*at] < '0' || p[*at] > '9') return 0;
        digit = (unsigned)(p[*at] - '0');
        if (magnitude > (UINT64_MAX - digit) / 10) return 0;
        magnitude = magnitude * 10 + digit;
        (*at)++; digits++;
    }
    if (!digits || magnitude > (negative ? UINT64_C(9223372036854775808)
                                         : UINT64_C(9223372036854775807)))
        return 0;
    if (negative && magnitude == UINT64_C(9223372036854775808))
        *out = INT64_MIN;
    else
        *out = negative ? -(int64_t)magnitude : (int64_t)magnitude;
    return 1;
}

static int parse_result(const unsigned char *p, size_t n, int lane,
                        int64_t invocation,
                        int64_t out[HAL_SEALED_FACADE_RESULT_FIELDS_V1]) {
    size_t at = 8;
    int field;
    if (!p || n < 10 || n >= HAL_SEALED_FRAME_CAP_V1 ||
        memcmp(p, "HALRES1|", 8) != 0 || p[n - 1] != '\n') return 0;
    for (field = 0; field < HAL_SEALED_FACADE_RESULT_FIELDS_V1; ++field) {
        if (!parse_i64(p, n, &at, &out[field])) return 0;
        if (field + 1 < HAL_SEALED_FACADE_RESULT_FIELDS_V1) {
            if (at >= n || p[at++] != '|') return 0;
        }
    }
    if (at + 1 != n || p[at] != '\n' || out[0] != lane ||
        out[1] != invocation || out[2] < 0 || out[2] > 7 ||
        out[12] < 0 || out[12] > 4) return 0;
    return 1;
}

static int parse_result_v2(
        const unsigned char *p, size_t n, int lane, int64_t invocation,
        int64_t out[HAL_SEALED_FACADE_RESULT_FIELDS_V2]) {
    size_t at = 8;
    int field;
    if (!p || n < 10 || n >= HAL_SEALED_FRAME_CAP_V1 ||
        memcmp(p, "HALRES2|", 8) != 0 || p[n - 1] != '\n') return 0;
    for (field = 0; field < HAL_SEALED_FACADE_RESULT_FIELDS_V2; ++field) {
        if (!parse_i64(p, n, &at, &out[field])) return 0;
        if (field + 1 < HAL_SEALED_FACADE_RESULT_FIELDS_V2) {
            if (at >= n || p[at++] != '|') return 0;
        }
    }
    if (at + 1 != n || p[at] != '\n' || out[0] != lane ||
        out[1] != invocation || out[2] < 0 || out[2] > 7 ||
        out[3] < 0 || out[3] > 4 || out[4] < 0 || out[5] < 0 ||
        out[6] != 1 || out[8] != 8 || out[9] < 8 || out[9] > 32 ||
        (out[10] == 0 && out[11] == 0) || out[12] != 1 || out[13] != 1 ||
        out[14] <= 0 || out[13] > out[14] || out[15] != 0 ||
        out[16] != -1 || out[17] != 0 || out[18] < 0) return 0;
    if ((out[2] == 0 && (out[3] != 0 || out[4] != 0 || out[5] != 0)) ||
        (out[2] != 0 && (out[3] == 0 || out[4] <= 0))) return 0;
    return 1;
}

static int result_v2_equivalent(const int64_t *a, const int64_t *b) {
    int field;
    /* Provider (0) and elapsed ticks (18) are intentionally lane-local. */
    for (field = 2; field < 18; ++field)
        if (a[field] != b[field]) return 0;
    return 1;
}

static int difference_mask_v2(const int64_t result[3][19]) {
    int difference = 0;
    if (!result_v2_equivalent(result[0], result[1]))
        difference |= HAL_SEALED_DIFFERENCE_PURE_C_V2;
    if (!result_v2_equivalent(result[0], result[2]))
        difference |= HAL_SEALED_DIFFERENCE_PURE_RUST_V2;
    if (!result_v2_equivalent(result[1], result[2]))
        difference |= HAL_SEALED_DIFFERENCE_C_RUST_V2;
    return difference;
}

uint64_t hal_sealed_facade_prepare_config_v1(
    const char *launcher, const char *pure_worker, const char *c_worker,
    const char *rust_worker, int64_t deadline_ms) {
    size_t index;
    uint64_t generation, handle = 0;
    const char *worker[3] = {pure_worker, c_worker, rust_worker};
    if (!launcher || !pure_worker || !c_worker || !rust_worker ||
        launcher[0] != '/' || pure_worker[0] != '/' || c_worker[0] != '/' ||
        rust_worker[0] != '/' || deadline_ms <= 0) return 0;
    maintenance_lock();
    for (index = 0; index < HAL_FACADE_SLOT_COUNT_V1; ++index) {
        int expected = 0;
        if (!atomic_compare_exchange_strong_explicit(
                &g_slots[index].state, &expected, 1,
                memory_order_acq_rel, memory_order_acquire)) continue;
        generation = atomic_fetch_add_explicit(&g_generation, 1,
                                                memory_order_relaxed);
        if (generation == 0 || generation >= (UINT64_MAX >> 8)) {
            atomic_store_explicit(&g_slots[index].state, 0,
                                  memory_order_release);
            break;
        }
        memset(&g_slots[index].session, 0, sizeof(g_slots[index].session));
        memset(g_slots[index].result, 0, sizeof(g_slots[index].result));
        memset(g_slots[index].result_v2, 0, sizeof(g_slots[index].result_v2));
        g_slots[index].config.launcher = launcher;
        g_slots[index].config.worker[0] = worker[0];
        g_slots[index].config.worker[1] = worker[1];
        g_slots[index].config.worker[2] = worker[2];
        g_slots[index].config.deadline_ms = deadline_ms;
        g_slots[index].generation = generation;
        g_slots[index].last_status = HAL_SEALED_FACADE_STATUS_STATE_V1;
        g_slots[index].completed_mask = 0;
        g_slots[index].result_schema = 0;
        g_slots[index].difference_mask_v2 = 0;
        g_slots[index].commit_allowed_v2 = 0;
        g_slots[index].selected_provider_v2 = -1;
        g_slots[index].last_v2_invocation = 0;
        if (!hal_sealed_session_prepare_v1(&g_slots[index].session,
                                           &g_slots[index].config)) {
            g_slots[index].generation = 0;
            atomic_store_explicit(&g_slots[index].state, 0,
                                  memory_order_release);
            break;
        }
        g_slots[index].last_status = HAL_SEALED_FACADE_STATUS_OK_V1;
        handle = make_handle(index, generation);
        break;
    }
    maintenance_unlock();
    return handle;
}

uint64_t rt_hal_sealed_prepare_v1(int64_t deadline_ms) {
    return hal_sealed_facade_prepare_config_v1(
        HAL_LAUNCHER_V1, HAL_PURE_V1, HAL_C_V1, HAL_RUST_V1, deadline_ms);
}

static int32_t clock_dispatch_init_config_v2(
        const char *launcher, const char *pure_worker, const char *c_worker,
        const char *rust_worker, int32_t run_mode, int32_t preferred_provider,
        int64_t deadline_ms) {
    int expected = 0;
    size_t index;
    if (run_mode < HAL_SEALED_RUN_ALPHA_V1 ||
        run_mode > HAL_SEALED_RUN_NORMAL_V1 || preferred_provider < 0 ||
        preferred_provider >= HAL_SEALED_FACADE_LANES_V1 || deadline_ms <= 0)
        return HAL_SEALED_FACADE_STATUS_INVALID_V1;
    if (!atomic_compare_exchange_strong_explicit(
            &g_clock_owner_v2.state, &expected, 1,
            memory_order_acq_rel, memory_order_acquire))
        return HAL_SEALED_FACADE_STATUS_STATE_V1;
    g_clock_owner_v2.run_mode = run_mode;
    g_clock_owner_v2.preferred_provider = preferred_provider;
    atomic_store_explicit(&g_clock_owner_v2.invocation, 0,
                          memory_order_relaxed);
    if (run_mode == HAL_SEALED_RUN_NORMAL_V1) {
        for (index = 0; index < HAL_FACADE_SLOT_COUNT_V1; ++index) {
            g_clock_owner_v2.handle[index] = 0;
            atomic_store_explicit(&g_clock_owner_v2.busy[index], 0,
                                  memory_order_relaxed);
        }
        atomic_store_explicit(&g_clock_owner_v2.state, 2,
                              memory_order_release);
        return HAL_SEALED_FACADE_STATUS_OK_V1;
    }
    for (index = 0; index < HAL_FACADE_SLOT_COUNT_V1; ++index) {
        atomic_store_explicit(&g_clock_owner_v2.busy[index], 0,
                              memory_order_relaxed);
        g_clock_owner_v2.handle[index] = hal_sealed_facade_prepare_config_v1(
            launcher, pure_worker, c_worker, rust_worker, deadline_ms);
        if (!g_clock_owner_v2.handle[index] ||
            rt_hal_sealed_seal_v1(g_clock_owner_v2.handle[index]) !=
                HAL_SEALED_FACADE_STATUS_OK_V1)
            break;
    }
    if (index != HAL_FACADE_SLOT_COUNT_V1) {
        size_t rollback;
        for (rollback = 0; rollback <= index; ++rollback) {
            if (g_clock_owner_v2.handle[rollback])
                (void)rt_hal_sealed_maintenance_shutdown_v1(
                    g_clock_owner_v2.handle[rollback]);
            g_clock_owner_v2.handle[rollback] = 0;
        }
        atomic_store_explicit(&g_clock_owner_v2.state, 0,
                              memory_order_release);
        return HAL_SEALED_FACADE_STATUS_IO_V1;
    }
    atomic_store_explicit(&g_clock_owner_v2.state, 2, memory_order_release);
    return HAL_SEALED_FACADE_STATUS_OK_V1;
}

int32_t hal_clock_dispatch_init_config_v2(
        const char *launcher, const char *pure_worker, const char *c_worker,
        const char *rust_worker, int32_t run_mode, int32_t preferred_provider,
        int64_t deadline_ms) {
    return clock_dispatch_init_config_v2(
        launcher, pure_worker, c_worker, rust_worker, run_mode,
        preferred_provider, deadline_ms);
}

int32_t rt_hal_clock_dispatch_init_v2(int32_t run_mode,
                                      int32_t preferred_provider,
                                      int64_t deadline_ms) {
    return clock_dispatch_init_config_v2(
        HAL_LAUNCHER_V1, HAL_PURE_V1, HAL_C_V1, HAL_RUST_V1,
        run_mode, preferred_provider, deadline_ms);
}

int64_t rt_hal_clock_dispatch_compare_v2(void) {
    int64_t captured;
    uint64_t invocation;
    size_t index;
    int32_t status;
    HalClockDispatchOwnerV2 *owner = &g_clock_owner_v2;
    if (atomic_load_explicit(&owner->state, memory_order_acquire) != 2)
        return -1;
    if (owner->run_mode == HAL_SEALED_RUN_NORMAL_V1)
        return rt_time_now_nanos();
    for (index = 0; index < HAL_FACADE_SLOT_COUNT_V1; ++index) {
        int expected = 0;
        if (!atomic_compare_exchange_strong_explicit(
                &owner->busy[index], &expected, 1,
                memory_order_acq_rel, memory_order_relaxed)) continue;
        if (atomic_load_explicit(&owner->state, memory_order_acquire) != 2) {
            atomic_store_explicit(&owner->busy[index], 0,
                                  memory_order_release);
            return -1;
        }
        /* Capture only after admission. A rejected concurrent caller must not
         * consume an untraceable environment instruction. */
        captured = rt_time_now_nanos();
        if (captured < 0) {
            atomic_store_explicit(&owner->busy[index], 0,
                                  memory_order_release);
            return captured;
        }
        invocation = atomic_fetch_add_explicit(
            &owner->invocation, 1, memory_order_relaxed) + 1;
        if (invocation == 0 || invocation > (uint64_t)INT64_MAX) {
            atomic_store_explicit(&owner->busy[index], 0,
                                  memory_order_release);
            return -1;
        }
        status = rt_hal_sealed_invoke_clock_mode_v2(
            owner->handle[index], owner->run_mode, owner->preferred_provider,
            HAL_CLOCK_OPERATION_ID_V2, (int64_t)invocation, 1, captured, 8,
            INT64_C(0x48414c434c4f434b), (int64_t)(index + 1), 1, 1, 1);
        if (status == HAL_SEALED_FACADE_STATUS_OK_V1 &&
            rt_hal_sealed_commit_allowed_v2(owner->handle[index]) == 1)
            captured = rt_hal_sealed_result_field_v2(
                owner->handle[index], owner->preferred_provider, 7);
        else
            captured = -1;
        atomic_store_explicit(&owner->busy[index], 0, memory_order_release);
        return captured;
    }
    return -1;
}

int32_t rt_hal_clock_dispatch_shutdown_v2(void) {
    int expected = 2;
    int32_t status = HAL_SEALED_FACADE_STATUS_OK_V1;
    size_t index;
    if (!atomic_compare_exchange_strong_explicit(
            &g_clock_owner_v2.state, &expected, 3,
            memory_order_acq_rel, memory_order_acquire))
        return HAL_SEALED_FACADE_STATUS_STATE_V1;
    for (index = 0; index < HAL_FACADE_SLOT_COUNT_V1; ++index) {
        if (atomic_load_explicit(&g_clock_owner_v2.busy[index],
                                 memory_order_acquire) != 0) {
            atomic_store_explicit(&g_clock_owner_v2.state, 2,
                                  memory_order_release);
            return HAL_SEALED_FACADE_STATUS_STATE_V1;
        }
    }
    for (index = 0; index < HAL_FACADE_SLOT_COUNT_V1; ++index) {
        if (g_clock_owner_v2.handle[index] != 0 &&
            rt_hal_sealed_maintenance_shutdown_v1(
                g_clock_owner_v2.handle[index]) !=
                    HAL_SEALED_FACADE_STATUS_OK_V1)
            status = HAL_SEALED_FACADE_STATUS_STATE_V1;
        else
            g_clock_owner_v2.handle[index] = 0;
    }
    atomic_store_explicit(&g_clock_owner_v2.state,
        status == HAL_SEALED_FACADE_STATUS_OK_V1 ? 0 : 2,
        memory_order_release);
    return status;
}

int32_t rt_hal_sealed_seal_v1(uint64_t handle) {
    HalSealedFacadeSlotV1 *slot;
    int expected = 1;
    maintenance_lock();
    slot = lookup(handle, NULL);
    if (!slot || !atomic_compare_exchange_strong_explicit(
            &slot->state, &expected, 3, memory_order_acq_rel,
            memory_order_acquire)) {
        maintenance_unlock(); return HAL_SEALED_FACADE_STATUS_STATE_V1;
    }
    if (!hal_sealed_session_seal_v1(&slot->session) ||
        !hal_sealed_session_enter_critical_v1(&slot->session)) {
        slot->last_status = HAL_SEALED_FACADE_STATUS_IO_V1;
        atomic_store_explicit(&slot->state, 1, memory_order_release);
        maintenance_unlock(); return slot->last_status;
    }
    slot->last_status = HAL_SEALED_FACADE_STATUS_OK_V1;
    atomic_store_explicit(&slot->state, 2, memory_order_release);
    maintenance_unlock();
    return HAL_SEALED_FACADE_STATUS_OK_V1;
}

int32_t rt_hal_sealed_invoke_mode_v1(
        uint64_t handle, int32_t run_mode, int32_t preferred_provider,
        int64_t operation_id, int64_t invocation_id, int64_t fixture_id,
        int64_t input_offset, int64_t input_length, int64_t input_capacity,
        int64_t trace_capacity) {
    HalSealedFacadeSlotV1 *slot = lookup(handle, NULL);
    unsigned char request[HAL_SEALED_FRAME_CAP_V1];
    unsigned char result[3][HAL_SEALED_FRAME_CAP_V1];
    size_t result_size[3];
    unsigned lane_mask;
    int expected = 2, request_size, lane;
    if (!slot || run_mode < HAL_SEALED_RUN_ALPHA_V1 ||
        run_mode > HAL_SEALED_RUN_NORMAL_V1 || preferred_provider < 0 ||
        preferred_provider >= HAL_SEALED_FACADE_LANES_V1 ||
        operation_id <= 0 || invocation_id <= 0 || fixture_id <= 0 ||
        input_offset < 0 || input_length < 0 || input_capacity < 0 ||
        input_length > input_capacity ||
        input_offset > input_capacity - input_length || trace_capacity <= 0)
        return HAL_SEALED_FACADE_STATUS_INVALID_V1;
    /* Compare modes dispatch all preinitialized isolated lanes. Normal sends
     * no protocol traffic to non-preferred lanes and retains no stale result.
     * Both paths use only fixed stack/slot storage after seal. */
    lane_mask = run_mode == HAL_SEALED_RUN_NORMAL_V1
        ? (1u << (unsigned)preferred_provider) : 7u;
    if (!atomic_compare_exchange_strong_explicit(
            &slot->state, &expected, 3, memory_order_acq_rel,
            memory_order_acquire)) return HAL_SEALED_FACADE_STATUS_STATE_V1;
    slot->completed_mask = 0;
    slot->result_schema = 0;
    slot->difference_mask_v2 = 0;
    slot->commit_allowed_v2 = 0;
    slot->selected_provider_v2 = -1;
    request_size = snprintf((char *)request, sizeof(request),
        "HALREQ1|1|%lld|%lld|%lld|%lld|%lld|%lld|%lld\n",
        (long long)operation_id, (long long)invocation_id,
        (long long)fixture_id, (long long)input_offset,
        (long long)input_length, (long long)input_capacity,
        (long long)trace_capacity);
    if (request_size <= 0 || (size_t)request_size >= sizeof(request) ||
        !hal_sealed_session_invoke_mask_v1(&slot->session,
            (uint64_t)invocation_id, lane_mask, request, (size_t)request_size,
            result, result_size)) {
        slot->last_status = HAL_SEALED_FACADE_STATUS_IO_V1;
        atomic_store_explicit(&slot->state, 2, memory_order_release);
        return slot->last_status;
    }
    for (lane = 0; lane < 3; ++lane) {
        if ((lane_mask & (1u << lane)) == 0) continue;
        if (!parse_result(result[lane], result_size[lane], lane,
                          invocation_id, slot->result[lane])) {
            slot->last_status = HAL_SEALED_FACADE_STATUS_PROTOCOL_V1;
            atomic_store_explicit(&slot->state, 2, memory_order_release);
            return slot->last_status;
        }
    }
    slot->completed_mask = (int32_t)lane_mask;
    slot->result_schema = 1;
    slot->last_status = HAL_SEALED_FACADE_STATUS_OK_V1;
    atomic_store_explicit(&slot->state, 2, memory_order_release);
    return HAL_SEALED_FACADE_STATUS_OK_V1;
}

int32_t rt_hal_sealed_invoke_clock_mode_v2(
        uint64_t handle, int32_t run_mode, int32_t preferred_provider,
        int64_t operation_id, int64_t invocation_id, int64_t fixture_id,
        int64_t captured_scalar, int64_t result_capacity,
        int64_t trace_identity_hi, int64_t trace_identity_lo,
        int64_t trace_cursor, int64_t trace_length, int64_t trace_capacity) {
    HalSealedFacadeSlotV1 *slot = lookup(handle, NULL);
    unsigned char request[HAL_SEALED_FRAME_CAP_V1];
    unsigned char result[3][HAL_SEALED_FRAME_CAP_V1];
    size_t result_size[3];
    unsigned lane_mask;
    int expected = 2, request_size, lane, difference = 0;
    if (!slot || run_mode < HAL_SEALED_RUN_ALPHA_V1 ||
        run_mode > HAL_SEALED_RUN_NORMAL_V1 || preferred_provider < 0 ||
        preferred_provider >= HAL_SEALED_FACADE_LANES_V1 ||
        operation_id <= 0 || invocation_id <= 0 || fixture_id <= 0 ||
        result_capacity < 8 || result_capacity > 32 ||
        (trace_identity_hi == 0 && trace_identity_lo == 0) ||
        trace_cursor != 1 || trace_length != 1 || trace_capacity < 1)
        return HAL_SEALED_FACADE_STATUS_INVALID_V1;
    /* The strictly increasing invocation is the sealed session's bounded,
     * allocation-free one-consumption cursor. A captured ClockRead receipt can
     * never be replayed, including after a divergent comparison. */
    lane_mask = run_mode == HAL_SEALED_RUN_NORMAL_V1
        ? (1u << (unsigned)preferred_provider) : 7u;
    if (!atomic_compare_exchange_strong_explicit(
            &slot->state, &expected, 3, memory_order_acq_rel,
            memory_order_acquire)) return HAL_SEALED_FACADE_STATUS_STATE_V1;
    if (invocation_id <= slot->last_v2_invocation) {
        atomic_store_explicit(&slot->state, 2, memory_order_release);
        return HAL_SEALED_FACADE_STATUS_INVALID_V1;
    }
    slot->completed_mask = 0;
    slot->result_schema = 0;
    slot->difference_mask_v2 = 0;
    slot->commit_allowed_v2 = 0;
    slot->selected_provider_v2 = -1;
    slot->last_v2_invocation = invocation_id;
    request_size = snprintf((char *)request, sizeof(request),
        "HALREQ2|2|%lld|%lld|%lld|%lld|%lld|%lld|%lld|%lld|%lld|%lld\n",
        (long long)operation_id, (long long)invocation_id,
        (long long)fixture_id, (long long)captured_scalar,
        (long long)result_capacity, (long long)trace_identity_hi,
        (long long)trace_identity_lo, (long long)trace_cursor,
        (long long)trace_length, (long long)trace_capacity);
    if (request_size <= 0 || (size_t)request_size >= sizeof(request) ||
        !hal_sealed_session_invoke_mask_v1(&slot->session,
            (uint64_t)invocation_id, lane_mask, request, (size_t)request_size,
            result, result_size)) {
        slot->last_status = HAL_SEALED_FACADE_STATUS_IO_V1;
        atomic_store_explicit(&slot->state, 2, memory_order_release);
        return slot->last_status;
    }
    for (lane = 0; lane < 3; ++lane) {
        if ((lane_mask & (1u << lane)) == 0) continue;
        if (!parse_result_v2(result[lane], result_size[lane], lane,
                             invocation_id, slot->result_v2[lane]) ||
            slot->result_v2[lane][9] != result_capacity ||
            slot->result_v2[lane][10] != trace_identity_hi ||
            slot->result_v2[lane][11] != trace_identity_lo ||
            slot->result_v2[lane][12] != trace_cursor ||
            slot->result_v2[lane][13] != trace_length ||
            slot->result_v2[lane][14] != trace_capacity) {
            slot->last_status = HAL_SEALED_FACADE_STATUS_PROTOCOL_V1;
            atomic_store_explicit(&slot->state, 2, memory_order_release);
            return slot->last_status;
        }
    }
    if (run_mode != HAL_SEALED_RUN_NORMAL_V1)
        difference = difference_mask_v2(slot->result_v2);
    slot->completed_mask = (int32_t)lane_mask;
    slot->result_schema = 2;
    slot->difference_mask_v2 = difference;
    slot->selected_provider_v2 = preferred_provider;
    slot->commit_allowed_v2 = difference == 0 ||
        run_mode == HAL_SEALED_RUN_BETA_V1 ||
        run_mode == HAL_SEALED_RUN_NORMAL_V1;
    slot->last_status = difference != 0 && run_mode == HAL_SEALED_RUN_ALPHA_V1
        ? HAL_SEALED_FACADE_STATUS_DIVERGED_V2
        : HAL_SEALED_FACADE_STATUS_OK_V1;
    atomic_store_explicit(&slot->state, 2, memory_order_release);
    return slot->last_status;
}

int32_t rt_hal_sealed_invoke_clock_v2(
        uint64_t handle, int64_t operation_id, int64_t invocation_id,
        int64_t fixture_id, int64_t captured_scalar,
        int64_t trace_identity_hi, int64_t trace_identity_lo) {
    /* No configuration is fail-safe: compare all lanes, stop on divergence,
     * and prefer Pure Simple only after exact agreement. */
    return rt_hal_sealed_invoke_clock_mode_v2(
        handle, HAL_SEALED_RUN_ALPHA_V1, 0, operation_id, invocation_id,
        fixture_id, captured_scalar, 8, trace_identity_hi,
        trace_identity_lo, 1, 1, 1);
}

int64_t rt_hal_sealed_result_field_v2(uint64_t handle, int32_t lane,
                                      int32_t field) {
    HalSealedFacadeSlotV1 *slot = lookup(handle, NULL);
    if (!slot || atomic_load_explicit(&slot->state, memory_order_acquire) != 2 ||
        slot->result_schema != 2 || lane < 0 || lane >= 3 ||
        (slot->completed_mask & (1 << lane)) == 0 || field < 0 ||
        field >= HAL_SEALED_FACADE_RESULT_FIELDS_V2) return INT64_MIN;
    return slot->result_v2[lane][field];
}

int32_t rt_hal_sealed_difference_mask_v2(uint64_t handle) {
    HalSealedFacadeSlotV1 *slot = lookup(handle, NULL);
    return slot && atomic_load_explicit(&slot->state, memory_order_acquire) == 2 &&
        slot->result_schema == 2 ? slot->difference_mask_v2 : 0;
}

int32_t rt_hal_sealed_commit_allowed_v2(uint64_t handle) {
    HalSealedFacadeSlotV1 *slot = lookup(handle, NULL);
    return slot && atomic_load_explicit(&slot->state, memory_order_acquire) == 2 &&
        slot->result_schema == 2 ? slot->commit_allowed_v2 : 0;
}

int32_t rt_hal_sealed_selected_provider_v2(uint64_t handle) {
    HalSealedFacadeSlotV1 *slot = lookup(handle, NULL);
    return slot && atomic_load_explicit(&slot->state, memory_order_acquire) == 2 &&
        slot->result_schema == 2 && slot->commit_allowed_v2
        ? slot->selected_provider_v2 : -1;
}

int32_t rt_hal_sealed_invoke_v1(uint64_t handle, int64_t operation_id,
                                int64_t invocation_id, int64_t fixture_id,
                                int64_t input_offset, int64_t input_length,
                                int64_t input_capacity, int64_t trace_capacity) {
    return rt_hal_sealed_invoke_mode_v1(
        handle, HAL_SEALED_RUN_ALPHA_V1, 0, operation_id, invocation_id,
        fixture_id, input_offset, input_length, input_capacity, trace_capacity);
}

int32_t rt_hal_sealed_completed_mask_v1(uint64_t handle) {
    HalSealedFacadeSlotV1 *slot = lookup(handle, NULL);
    if (!slot || atomic_load_explicit(&slot->state, memory_order_acquire) != 2 ||
        (slot->last_status != HAL_SEALED_FACADE_STATUS_OK_V1 &&
         slot->last_status != HAL_SEALED_FACADE_STATUS_DIVERGED_V2)) return 0;
    return slot->completed_mask;
}

int64_t rt_hal_sealed_result_field_v1(uint64_t handle, int32_t lane,
                                      int32_t field) {
    HalSealedFacadeSlotV1 *slot = lookup(handle, NULL);
    if (!slot || atomic_load_explicit(&slot->state, memory_order_acquire) != 2 ||
        slot->last_status != HAL_SEALED_FACADE_STATUS_OK_V1 ||
        slot->result_schema != 1 || lane < 0 ||
        lane >= 3 || (slot->completed_mask & (1 << lane)) == 0 ||
        field < 0 || field >= 16) return INT64_MIN;
    return slot->result[lane][field];
}

int64_t rt_hal_sealed_sandbox_pid_v1(uint64_t handle, int32_t lane) {
    HalSealedFacadeSlotV1 *slot = lookup(handle, NULL);
    if (!slot || atomic_load_explicit(&slot->state, memory_order_acquire) != 2 ||
        lane < 0 || lane >= 3 || !slot->session.lane[lane].isolation_valid)
        return -1;
    return slot->session.lane[lane].sandbox_pid;
}

int32_t rt_hal_sealed_last_status_v1(uint64_t handle) {
    HalSealedFacadeSlotV1 *slot = lookup(handle, NULL);
    return slot ? slot->last_status : HAL_SEALED_FACADE_STATUS_INVALID_V1;
}

uint64_t rt_hal_sealed_hot_spawn_count_v1(uint64_t handle) {
    HalSealedFacadeSlotV1 *slot = lookup(handle, NULL);
    return slot ? slot->session.hot_spawn_count : UINT64_MAX;
}

uint64_t rt_hal_sealed_hot_allocation_count_v1(uint64_t handle) {
    HalSealedFacadeSlotV1 *slot = lookup(handle, NULL);
    return slot ? slot->session.hot_allocation_count : UINT64_MAX;
}

int32_t rt_hal_sealed_maintenance_shutdown_v1(uint64_t handle) {
    HalSealedFacadeSlotV1 *slot;
    int expected;
    int was_critical;
    maintenance_lock();
    slot = lookup(handle, NULL);
    if (!slot) { maintenance_unlock(); return HAL_SEALED_FACADE_STATUS_INVALID_V1; }
    expected = atomic_load_explicit(&slot->state, memory_order_acquire);
    if (expected != 1 && expected != 2) {
        maintenance_unlock(); return HAL_SEALED_FACADE_STATUS_STATE_V1;
    }
    was_critical = expected == 2;
    if (!atomic_compare_exchange_strong_explicit(
            &slot->state, &expected, 3, memory_order_acq_rel,
            memory_order_acquire)) {
        maintenance_unlock(); return HAL_SEALED_FACADE_STATUS_STATE_V1;
    }
    if ((was_critical &&
         !hal_sealed_session_leave_critical_v1(&slot->session)) ||
        !hal_sealed_session_shutdown_v1(&slot->session)) {
        slot->last_status = HAL_SEALED_FACADE_STATUS_IO_V1;
        atomic_store_explicit(&slot->state, 1, memory_order_release);
        maintenance_unlock(); return slot->last_status;
    }
    slot->generation = 0;
    slot->last_status = HAL_SEALED_FACADE_STATUS_OK_V1;
    atomic_store_explicit(&slot->state, 0, memory_order_release);
    maintenance_unlock();
    return HAL_SEALED_FACADE_STATUS_OK_V1;
}
