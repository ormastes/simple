#include "runtime_hal_buffer_dispatch.h"

#include <stdatomic.h>
#include <stddef.h>
#include <string.h>

enum { HAL_BUFFER_STATUS_OK_V3 = 0, HAL_BUFFER_STATUS_INVALID_V3 = 1,
       HAL_BUFFER_STATUS_STATE_V3 = 2, HAL_BUFFER_STATUS_IO_V3 = 3 };

/* Maintenance writes the immutable callback/config before publishing state=2.
 * Compare calls never allocate, spawn, lock, inspect the environment, or
 * retain either caller pointer. */
static _Atomic int g_hal_buffer_state_v3;
static _Atomic uint64_t g_hal_buffer_active_v3;
static RtHalBufferOwnerCompareV3 g_hal_buffer_owner_v3;
static int32_t g_hal_buffer_mode_v3;
static int32_t g_hal_buffer_provider_v3;

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
    g_hal_buffer_mode_v3 = run_mode;
    g_hal_buffer_provider_v3 = preferred_provider;
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
    g_hal_buffer_mode_v3 = 0;
    g_hal_buffer_provider_v3 = 0;
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
    (void)operation_id; (void)fixture_id; (void)trace_identity_hi;
    (void)trace_identity_lo; (void)trace_cursor; (void)trace_length;
    (void)trace_capacity;
    if (captured_length < 0 || captured_length > 32 ||
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

int32_t rt_hal_buffer_dispatch_mode_v3(void) {
    return atomic_load_explicit(&g_hal_buffer_state_v3,
                                memory_order_acquire) == 2
        ? g_hal_buffer_mode_v3 : -1;
}

int32_t rt_hal_buffer_dispatch_provider_v3(void) {
    return atomic_load_explicit(&g_hal_buffer_state_v3,
                                memory_order_acquire) == 2
        ? g_hal_buffer_provider_v3 : -1;
}

uint64_t rt_hal_buffer_dispatch_hot_allocation_count_v3(void) { return 0; }
