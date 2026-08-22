#include "runtime_hal_buffer_dispatch.h"

#include <stdatomic.h>
#include <stddef.h>
#include <string.h>

enum { HAL_BUFFER_STATUS_OK_V3 = 0, HAL_BUFFER_STATUS_INVALID_V3 = 1,
       HAL_BUFFER_STATUS_STATE_V3 = 2, HAL_BUFFER_STATUS_IO_V3 = 3 };

enum {
    HAL_BUFFER_OPERATION_ENVIRONMENT_GET_V3 = 102,
    HAL_BUFFER_OPERATION_FILE_READ_V3 = 1001,
    HAL_BUFFER_OPERATION_STREAM_READ_V3 = 1004,
    HAL_BUFFER_OPERATION_STREAM_WRITE_V3 = 1005,
    HAL_BUFFER_OPERATION_PROCESS_WAIT_V3 = 1007,
    HAL_BUFFER_OPERATION_RANDOM_FILL_V3 = 1011,
    HAL_BUFFER_OPERATION_SOCKET_CONNECT_TIMEOUT_V3 = 1012
};

/* Maintenance writes the immutable callback/config before publishing state=2.
 * Compare calls never allocate, spawn, lock, inspect the environment, or
 * retain either caller pointer. */
static _Atomic int g_hal_buffer_state_v3;
static _Atomic uint64_t g_hal_buffer_active_v3;
static RtHalBufferOwnerCompareV3 g_hal_buffer_owner_v3;
static _Atomic int32_t g_hal_buffer_mode_v3;
static _Atomic int32_t g_hal_buffer_provider_v3;

int32_t rt_hal_buffer_dispatch_bind_owner_v3(
        RtHalBufferOwnerCompareV3 owner, int32_t run_mode,
        int32_t preferred_provider) {
    int expected = 0;
    if (!owner || run_mode < 0 || run_mode > 2 ||
        preferred_provider < 0 || preferred_provider > 2 ||
        !atomic_compare_exchange_strong_explicit(
            &g_hal_buffer_state_v3, &expected, 1,
            memory_order_acq_rel, memory_order_acquire))
        return HAL_BUFFER_STATUS_INVALID_V3;
    g_hal_buffer_owner_v3 = owner;
    atomic_store_explicit(&g_hal_buffer_mode_v3, run_mode, memory_order_relaxed);
    atomic_store_explicit(&g_hal_buffer_provider_v3, preferred_provider,
                          memory_order_relaxed);
    atomic_store_explicit(&g_hal_buffer_state_v3, 2, memory_order_release);
    return HAL_BUFFER_STATUS_OK_V3;
}

int32_t rt_hal_buffer_dispatch_unbind_owner_v3(void) {
    int expected = 2;
    if (!atomic_compare_exchange_strong_explicit(
            &g_hal_buffer_state_v3, &expected, 3,
            memory_order_acq_rel, memory_order_acquire))
        return HAL_BUFFER_STATUS_STATE_V3;
    if (atomic_load_explicit(&g_hal_buffer_active_v3,
                             memory_order_acquire) != 0) {
        atomic_store_explicit(&g_hal_buffer_state_v3, 2,
                              memory_order_release);
        return HAL_BUFFER_STATUS_STATE_V3;
    }
    g_hal_buffer_owner_v3 = NULL;
    atomic_store_explicit(&g_hal_buffer_mode_v3, 0, memory_order_relaxed);
    atomic_store_explicit(&g_hal_buffer_provider_v3, 0, memory_order_relaxed);
    atomic_store_explicit(&g_hal_buffer_state_v3, 0, memory_order_release);
    return HAL_BUFFER_STATUS_OK_V3;
}

int32_t rt_hal_buffer_dispatch_compare_v3(
        int64_t operation_id, int64_t fixture_id, int32_t captured_status,
        int32_t error_domain, int64_t error_code, int64_t error_detail,
        const uint8_t *captured, int64_t captured_length,
        uint8_t *output, int64_t output_capacity,
        int64_t trace_identity_hi, int64_t trace_identity_lo,
        int64_t trace_cursor, int64_t trace_length, int64_t trace_capacity) {
    RtHalBufferOwnerCompareV3 owner;
    int32_t result;
    if (atomic_load_explicit(&g_hal_buffer_state_v3,
                             memory_order_acquire) != 2)
        return HAL_BUFFER_STATUS_INVALID_V3;
    atomic_fetch_add_explicit(&g_hal_buffer_active_v3, 1,
                              memory_order_acq_rel);
    if (atomic_load_explicit(&g_hal_buffer_state_v3,
                             memory_order_acquire) != 2) {
        atomic_fetch_sub_explicit(&g_hal_buffer_active_v3, 1,
                                  memory_order_release);
        return HAL_BUFFER_STATUS_STATE_V3;
    }
    owner = g_hal_buffer_owner_v3;
    if (!owner) {
        atomic_fetch_sub_explicit(&g_hal_buffer_active_v3, 1,
                                  memory_order_release);
        return HAL_BUFFER_STATUS_INVALID_V3;
    }
    result = owner(operation_id, fixture_id, captured_status, error_domain,
                   error_code, error_detail, captured, captured_length,
                   output, output_capacity, trace_identity_hi,
                   trace_identity_lo, trace_cursor, trace_length,
                   trace_capacity);
    atomic_fetch_sub_explicit(&g_hal_buffer_active_v3, 1,
                              memory_order_release);
    return result;
}

int32_t rt_hal_buffer_dispatch_direct_v3(
        int64_t operation_id, int64_t fixture_id, int32_t captured_status,
        int32_t error_domain, int64_t error_code, int64_t error_detail,
        const uint8_t *captured, int64_t captured_length,
        uint8_t *output, int64_t output_capacity,
        int64_t trace_identity_hi, int64_t trace_identity_lo,
        int64_t trace_cursor, int64_t trace_length, int64_t trace_capacity) {
    const int operation_known =
        operation_id == HAL_BUFFER_OPERATION_ENVIRONMENT_GET_V3 ||
        operation_id == HAL_BUFFER_OPERATION_FILE_READ_V3 ||
        operation_id == HAL_BUFFER_OPERATION_STREAM_READ_V3 ||
        operation_id == HAL_BUFFER_OPERATION_STREAM_WRITE_V3 ||
        operation_id == HAL_BUFFER_OPERATION_PROCESS_WAIT_V3 ||
        operation_id == HAL_BUFFER_OPERATION_RANDOM_FILL_V3 ||
        operation_id == HAL_BUFFER_OPERATION_SOCKET_CONNECT_TIMEOUT_V3;
    if (!operation_known || fixture_id <= 0 ||
        trace_identity_hi == 0 || trace_identity_lo == 0 ||
        trace_cursor < 0 || trace_length <= trace_cursor ||
        trace_length - trace_cursor != 1 ||
        trace_capacity < trace_length || trace_capacity > 4096 ||
        captured_length < 0 || captured_length > 32 ||
        output_capacity <= 0 || output_capacity > 32 ||
        captured_length > output_capacity || !output ||
        (captured_length > 0 && !captured))
        return HAL_BUFFER_STATUS_INVALID_V3;
    if ((captured_status == 0 &&
         (error_domain != 0 || error_code != 0 || error_detail != 0)) ||
        (captured_status < 0) ||
        (captured_status > 0 && (error_domain <= 0 || error_code == 0)))
        return HAL_BUFFER_STATUS_INVALID_V3;
    if (captured_status > 0)
        return HAL_BUFFER_STATUS_IO_V3;
    if (captured_length > 0)
        memmove(output, captured, (size_t)captured_length);
    return HAL_BUFFER_STATUS_OK_V3;
}

int32_t rt_hal_buffer_dispatch_configured_v3(
        int64_t operation_id, int64_t fixture_id, int32_t captured_status,
        int32_t error_domain, int64_t error_code, int64_t error_detail,
        const uint8_t *captured, int64_t captured_length,
        uint8_t *output, int64_t output_capacity,
        int64_t trace_identity_hi, int64_t trace_identity_lo,
        int64_t trace_cursor, int64_t trace_length, int64_t trace_capacity) {
    if (atomic_load_explicit(&g_hal_buffer_state_v3,
                             memory_order_acquire) != 2)
        return HAL_BUFFER_STATUS_INVALID_V3;
    if (atomic_load_explicit(&g_hal_buffer_mode_v3,
                             memory_order_relaxed) == 2)
        return rt_hal_buffer_dispatch_direct_v3(
            operation_id, fixture_id, captured_status, error_domain,
            error_code, error_detail, captured, captured_length, output,
            output_capacity, trace_identity_hi, trace_identity_lo,
            trace_cursor, trace_length, trace_capacity);
    return rt_hal_buffer_dispatch_compare_v3(
        operation_id, fixture_id, captured_status, error_domain,
        error_code, error_detail, captured, captured_length, output,
        output_capacity, trace_identity_hi, trace_identity_lo,
        trace_cursor, trace_length, trace_capacity);
}

int32_t rt_hal_buffer_dispatch_mode_v3(void) {
    return atomic_load_explicit(&g_hal_buffer_state_v3,
                                memory_order_acquire) == 2
        ? atomic_load_explicit(&g_hal_buffer_mode_v3, memory_order_relaxed) : -1;
}

int32_t rt_hal_buffer_dispatch_provider_v3(void) {
    return atomic_load_explicit(&g_hal_buffer_state_v3,
                                memory_order_acquire) == 2
        ? atomic_load_explicit(&g_hal_buffer_provider_v3,
                               memory_order_relaxed) : -1;
}

uint64_t rt_hal_buffer_dispatch_hot_allocation_count_v3(void) { return 0; }

enum { HAL_EXTERNAL_MAX_SLOTS_V4 = 256, HAL_EXTERNAL_MAX_STEPS_V4 = 4096,
       HAL_EXTERNAL_KIND_PROCESS_V4 = 0, HAL_EXTERNAL_KIND_SOCKET_V4 = 1 };

typedef struct RtHalExternalSlotV4 {
    atomic_flag lock;
    int64_t fixture_id;
    int64_t generation;
    int64_t identity_hi;
    int64_t identity_lo;
    int64_t next_cursor;
    uint64_t nonce;
    int32_t kind;
    int32_t occupied;
    int32_t terminal;
    int32_t poisoned;
    int32_t in_flight;
} RtHalExternalSlotV4;

static _Atomic int g_hal_external_state_v4;
static int64_t g_hal_external_capacity_v4;
static RtHalExternalSlotV4 g_hal_external_slots_v4[HAL_EXTERNAL_MAX_SLOTS_V4];

static void hal_external_lock_v4(RtHalExternalSlotV4 *slot) {
    while (atomic_flag_test_and_set_explicit(&slot->lock,
                                             memory_order_acquire)) {}
}

static void hal_external_unlock_v4(RtHalExternalSlotV4 *slot) {
    atomic_flag_clear_explicit(&slot->lock, memory_order_release);
}

static int hal_external_trace_valid_v4(
        int64_t fixture_id, int64_t identity_hi, int64_t identity_lo,
        int64_t cursor, int64_t length, int64_t capacity) {
    return fixture_id > 0 && fixture_id <= INT64_C(1000000000) &&
           identity_hi != 0 && identity_lo != 0 && cursor >= 0 &&
           cursor < HAL_EXTERNAL_MAX_STEPS_V4 && length == cursor + 1 &&
           capacity >= length && capacity <= HAL_EXTERNAL_MAX_STEPS_V4;
}

int32_t rt_hal_process_socket_lifecycle_init_v4(int64_t capacity) {
    int expected = 0;
    int64_t i;
    if (capacity <= 0 || capacity > HAL_EXTERNAL_MAX_SLOTS_V4 ||
        !atomic_compare_exchange_strong_explicit(
            &g_hal_external_state_v4, &expected, 1,
            memory_order_acq_rel, memory_order_acquire))
        return HAL_BUFFER_STATUS_INVALID_V3;
    g_hal_external_capacity_v4 = capacity;
    for (i = 0; i < capacity; ++i) {
        memset(&g_hal_external_slots_v4[i], 0,
               sizeof(g_hal_external_slots_v4[i]));
        atomic_flag_clear_explicit(&g_hal_external_slots_v4[i].lock,
                                   memory_order_relaxed);
    }
    atomic_store_explicit(&g_hal_external_state_v4, 2,
                          memory_order_release);
    return HAL_BUFFER_STATUS_OK_V3;
}

static int32_t hal_external_register_v4(
        int32_t kind, int64_t fixture_id, int64_t generation,
        int64_t identity_hi, int64_t identity_lo, int64_t cursor,
        int64_t length, int64_t trace_capacity) {
    RtHalExternalSlotV4 *slot;
    int32_t result = HAL_BUFFER_STATUS_INVALID_V3;
    if (atomic_load_explicit(&g_hal_external_state_v4,
                             memory_order_acquire) != 2 || generation <= 0 ||
        generation > INT64_C(1000000000) || cursor != 0 ||
        !hal_external_trace_valid_v4(fixture_id, identity_hi, identity_lo,
                                     cursor, length, trace_capacity))
        return result;
    slot = &g_hal_external_slots_v4[fixture_id % g_hal_external_capacity_v4];
    hal_external_lock_v4(slot);
    if (!slot->in_flight &&
        (!slot->occupied ||
         (slot->fixture_id == fixture_id && generation > slot->generation))) {
        slot->fixture_id = fixture_id;
        slot->generation = generation;
        slot->identity_hi = identity_hi;
        slot->identity_lo = identity_lo;
        slot->next_cursor = kind == HAL_EXTERNAL_KIND_PROCESS_V4 ? 1 : 0;
        slot->kind = kind;
        slot->occupied = 1;
        slot->terminal = 0;
        slot->poisoned = 0;
        slot->in_flight = 0;
        if (++slot->nonce == 0) ++slot->nonce;
        result = HAL_BUFFER_STATUS_OK_V3;
    }
    hal_external_unlock_v4(slot);
    return result;
}

int32_t rt_hal_process_socket_register_spawn_v4(
        int64_t fixture_id, int64_t generation, int64_t identity_hi,
        int64_t identity_lo, int64_t cursor, int64_t length,
        int64_t trace_capacity) {
    return hal_external_register_v4(HAL_EXTERNAL_KIND_PROCESS_V4, fixture_id,
        generation, identity_hi, identity_lo, cursor, length, trace_capacity);
}

int32_t rt_hal_process_socket_register_attempt_v4(
        int64_t fixture_id, int64_t generation, int64_t identity_hi,
        int64_t identity_lo, int64_t cursor, int64_t length,
        int64_t trace_capacity) {
    return hal_external_register_v4(HAL_EXTERNAL_KIND_SOCKET_V4, fixture_id,
        generation, identity_hi, identity_lo, cursor, length, trace_capacity);
}

static uint64_t hal_external_begin_v4(
        int32_t kind, int64_t fixture_id, int64_t identity_hi,
        int64_t identity_lo, int64_t cursor, int64_t length,
        int64_t trace_capacity) {
    RtHalExternalSlotV4 *slot;
    uint64_t nonce = 0;
    if (atomic_load_explicit(&g_hal_external_state_v4,
                             memory_order_acquire) != 2 ||
        !hal_external_trace_valid_v4(fixture_id, identity_hi, identity_lo,
                                     cursor, length, trace_capacity))
        return 0;
    slot = &g_hal_external_slots_v4[fixture_id % g_hal_external_capacity_v4];
    hal_external_lock_v4(slot);
    if (slot->occupied && !slot->terminal && !slot->poisoned &&
        !slot->in_flight && slot->kind == kind &&
        slot->fixture_id == fixture_id && slot->identity_hi == identity_hi &&
        slot->identity_lo == identity_lo && slot->next_cursor == cursor) {
        slot->in_flight = 1;
        if (++slot->nonce == 0) ++slot->nonce;
        nonce = slot->nonce;
    }
    hal_external_unlock_v4(slot);
    return nonce;
}

static int32_t hal_external_finish_v4(
        int32_t kind, int64_t fixture_id, int64_t identity_hi,
        int64_t identity_lo, int64_t cursor, uint64_t nonce,
        int32_t committed) {
    RtHalExternalSlotV4 *slot;
    int32_t result = HAL_BUFFER_STATUS_INVALID_V3;
    if (atomic_load_explicit(&g_hal_external_state_v4,
                             memory_order_acquire) != 2 || nonce == 0)
        return result;
    slot = &g_hal_external_slots_v4[fixture_id % g_hal_external_capacity_v4];
    hal_external_lock_v4(slot);
    if (slot->occupied && slot->in_flight && slot->kind == kind &&
        slot->fixture_id == fixture_id && slot->identity_hi == identity_hi &&
        slot->identity_lo == identity_lo && slot->next_cursor == cursor &&
        slot->nonce == nonce) {
        slot->in_flight = 0;
        if (!committed) {
            slot->poisoned = 1;
            slot->terminal = 1;
        } else if (kind == HAL_EXTERNAL_KIND_PROCESS_V4) {
            slot->next_cursor = cursor + 1;
        } else {
            slot->next_cursor = 1;
            slot->terminal = 1;
        }
        result = committed ? HAL_BUFFER_STATUS_OK_V3
                           : HAL_BUFFER_STATUS_INVALID_V3;
    }
    hal_external_unlock_v4(slot);
    return result;
}

static int32_t hal_external_dispatch_v4(
        int32_t kind, int32_t compare, int64_t operation_id,
        int64_t fixture_id, int32_t captured_status, int32_t error_domain,
        int64_t error_code, int64_t error_detail, const uint8_t *captured,
        int64_t captured_length, uint8_t *output, int64_t output_capacity,
        int64_t identity_hi, int64_t identity_lo, int64_t cursor,
        int64_t length, int64_t trace_capacity) {
    uint8_t scratch[32];
    uint64_t nonce;
    int32_t status;
    int32_t finished;
    if (!output || captured_length < 0 || captured_length > 32 ||
        output_capacity <= 0 || output_capacity > 32 ||
        captured_length > output_capacity ||
        (captured_length > 0 && !captured))
        return HAL_BUFFER_STATUS_INVALID_V3;
    nonce = hal_external_begin_v4(kind, fixture_id, identity_hi,
        identity_lo, cursor, length, trace_capacity);
    if (nonce == 0) return HAL_BUFFER_STATUS_INVALID_V3;
    memset(scratch, 0, sizeof(scratch));
    status = compare
        ? rt_hal_buffer_dispatch_compare_v3(operation_id, fixture_id,
            captured_status, error_domain, error_code, error_detail, captured,
            captured_length, scratch, output_capacity, identity_hi, identity_lo,
            cursor, length, trace_capacity)
        : rt_hal_buffer_dispatch_direct_v3(operation_id, fixture_id,
            captured_status, error_domain, error_code, error_detail, captured,
            captured_length, scratch, output_capacity, identity_hi, identity_lo,
            cursor, length, trace_capacity);
    finished = hal_external_finish_v4(kind, fixture_id, identity_hi,
        identity_lo, cursor, nonce, status == HAL_BUFFER_STATUS_OK_V3);
    if (status == HAL_BUFFER_STATUS_OK_V3 &&
        finished != HAL_BUFFER_STATUS_OK_V3)
        return HAL_BUFFER_STATUS_INVALID_V3;
    if (status == HAL_BUFFER_STATUS_OK_V3 && captured_length > 0)
        memmove(output, scratch, (size_t)captured_length);
    return status;
}

#define HAL_EXTERNAL_DISPATCH_V4(name, kind_value, compare_value, op_value) \
int32_t name(int64_t fixture_id, int32_t captured_status, \
        int32_t error_domain, int64_t error_code, int64_t error_detail, \
        const uint8_t *captured, int64_t captured_length, uint8_t *output, \
        int64_t output_capacity, int64_t identity_hi, int64_t identity_lo, \
        int64_t cursor, int64_t length, int64_t trace_capacity) { \
    return hal_external_dispatch_v4(kind_value, compare_value, op_value, \
        fixture_id, captured_status, error_domain, error_code, error_detail, \
        captured, captured_length, output, output_capacity, identity_hi, \
        identity_lo, cursor, length, trace_capacity); \
}

HAL_EXTERNAL_DISPATCH_V4(rt_hal_process_wait_dispatch_direct_v4,
    HAL_EXTERNAL_KIND_PROCESS_V4, 0, INT64_C(1007))
HAL_EXTERNAL_DISPATCH_V4(rt_hal_process_wait_dispatch_compare_v4,
    HAL_EXTERNAL_KIND_PROCESS_V4, 1, INT64_C(1007))
HAL_EXTERNAL_DISPATCH_V4(rt_hal_socket_connect_dispatch_direct_v4,
    HAL_EXTERNAL_KIND_SOCKET_V4, 0, INT64_C(1012))
HAL_EXTERNAL_DISPATCH_V4(rt_hal_socket_connect_dispatch_compare_v4,
    HAL_EXTERNAL_KIND_SOCKET_V4, 1, INT64_C(1012))

uint64_t rt_hal_process_socket_hot_allocation_count_v4(void) { return 0; }
