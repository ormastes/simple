#ifndef SIMPLE_RUNTIME_HAL_BUFFER_DISPATCH_H
#define SIMPLE_RUNTIME_HAL_BUFFER_DISPATCH_H

#include <stdint.h>

typedef int32_t (*RtHalBufferOwnerCompareV3)(
    int64_t, int64_t, int32_t, int32_t, int64_t, int64_t,
    const uint8_t *, int64_t, uint8_t *, int64_t,
    int64_t, int64_t, int64_t, int64_t, int64_t);

int32_t rt_hal_buffer_dispatch_bind_owner_v3(
    RtHalBufferOwnerCompareV3 owner, int32_t run_mode,
    int32_t preferred_provider);
int32_t rt_hal_buffer_dispatch_unbind_owner_v3(void);
int32_t rt_hal_buffer_dispatch_direct_v3(
    int64_t operation_id, int64_t fixture_id, int32_t captured_status,
    int32_t error_domain, int64_t error_code, int64_t error_detail,
    const uint8_t *captured, int64_t captured_length,
    uint8_t *output, int64_t output_capacity,
    int64_t trace_identity_hi, int64_t trace_identity_lo,
    int64_t trace_cursor, int64_t trace_length, int64_t trace_capacity);
int32_t rt_hal_buffer_dispatch_configured_v3(
    int64_t operation_id, int64_t fixture_id, int32_t captured_status,
    int32_t error_domain, int64_t error_code, int64_t error_detail,
    const uint8_t *captured, int64_t captured_length,
    uint8_t *output, int64_t output_capacity,
    int64_t trace_identity_hi, int64_t trace_identity_lo,
    int64_t trace_cursor, int64_t trace_length, int64_t trace_capacity);
int32_t rt_hal_buffer_dispatch_compare_v3(
    int64_t operation_id, int64_t fixture_id, int32_t captured_status,
    int32_t error_domain, int64_t error_code, int64_t error_detail,
    const uint8_t *captured, int64_t captured_length,
    uint8_t *output, int64_t output_capacity,
    int64_t trace_identity_hi, int64_t trace_identity_lo,
    int64_t trace_cursor, int64_t trace_length, int64_t trace_capacity);
int32_t rt_hal_buffer_dispatch_mode_v3(void);
int32_t rt_hal_buffer_dispatch_provider_v3(void);
uint64_t rt_hal_buffer_dispatch_hot_allocation_count_v3(void);

/* Init-owned, fixed-capacity process/socket lifecycle authority. Execution
 * entrypoints intentionally retain the frozen 14-argument buffer ABI. */
int32_t rt_hal_process_socket_lifecycle_init_v4(int64_t capacity);
int32_t rt_hal_process_socket_register_spawn_v4(
    int64_t fixture_id, int64_t generation, int64_t identity_hi,
    int64_t identity_lo, int64_t cursor, int64_t length,
    int64_t trace_capacity);
int32_t rt_hal_process_socket_register_attempt_v4(
    int64_t fixture_id, int64_t generation, int64_t identity_hi,
    int64_t identity_lo, int64_t cursor, int64_t length,
    int64_t trace_capacity);
int32_t rt_hal_process_wait_dispatch_direct_v4(
    int64_t fixture_id, int32_t captured_status, int32_t error_domain,
    int64_t error_code, int64_t error_detail,
    const uint8_t *captured, int64_t captured_length,
    uint8_t *output, int64_t output_capacity,
    int64_t trace_identity_hi, int64_t trace_identity_lo,
    int64_t trace_cursor, int64_t trace_length, int64_t trace_capacity);
int32_t rt_hal_process_wait_dispatch_compare_v4(
    int64_t fixture_id, int32_t captured_status, int32_t error_domain,
    int64_t error_code, int64_t error_detail,
    const uint8_t *captured, int64_t captured_length,
    uint8_t *output, int64_t output_capacity,
    int64_t trace_identity_hi, int64_t trace_identity_lo,
    int64_t trace_cursor, int64_t trace_length, int64_t trace_capacity);
int32_t rt_hal_socket_connect_dispatch_direct_v4(
    int64_t fixture_id, int32_t captured_status, int32_t error_domain,
    int64_t error_code, int64_t error_detail,
    const uint8_t *captured, int64_t captured_length,
    uint8_t *output, int64_t output_capacity,
    int64_t trace_identity_hi, int64_t trace_identity_lo,
    int64_t trace_cursor, int64_t trace_length, int64_t trace_capacity);
int32_t rt_hal_socket_connect_dispatch_compare_v4(
    int64_t fixture_id, int32_t captured_status, int32_t error_domain,
    int64_t error_code, int64_t error_detail,
    const uint8_t *captured, int64_t captured_length,
    uint8_t *output, int64_t output_capacity,
    int64_t trace_identity_hi, int64_t trace_identity_lo,
    int64_t trace_cursor, int64_t trace_length, int64_t trace_capacity);
uint64_t rt_hal_process_socket_hot_allocation_count_v4(void);

#endif
