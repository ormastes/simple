#ifndef SIMPLE_HAL_PROVIDER_SEALED_FACADE_V1_H
#define SIMPLE_HAL_PROVIDER_SEALED_FACADE_V1_H

#include <stdint.h>

enum {
    HAL_SEALED_FACADE_LANES_V1 = 3,
    HAL_SEALED_FACADE_RESULT_FIELDS_V1 = 16,
    HAL_SEALED_FACADE_STATUS_OK_V1 = 0,
    HAL_SEALED_FACADE_STATUS_INVALID_V1 = 1,
    HAL_SEALED_FACADE_STATUS_STATE_V1 = 2,
    HAL_SEALED_FACADE_STATUS_IO_V1 = 3,
    HAL_SEALED_FACADE_STATUS_PROTOCOL_V1 = 4
};

enum {
    HAL_SEALED_RUN_ALPHA_V1 = 0,
    HAL_SEALED_RUN_BETA_V1 = 1,
    HAL_SEALED_RUN_NORMAL_V1 = 2
};

enum {
    HAL_SEALED_RESULT_PROVIDER_V1 = 0,
    HAL_SEALED_RESULT_INVOCATION_V1 = 1,
    HAL_SEALED_RESULT_STATUS_V1 = 2,
    HAL_SEALED_RESULT_STATUS_CODE_V1 = 3,
    HAL_SEALED_RESULT_NORMALIZED_HI_V1 = 4,
    HAL_SEALED_RESULT_NORMALIZED_LO_V1 = 5,
    HAL_SEALED_RESULT_TRACE_HI_V1 = 6,
    HAL_SEALED_RESULT_TRACE_LO_V1 = 7,
    HAL_SEALED_RESULT_PAYLOAD_LENGTH_V1 = 8,
    HAL_SEALED_RESULT_PAYLOAD_CAPACITY_V1 = 9,
    HAL_SEALED_RESULT_TRACE_LENGTH_V1 = 10,
    HAL_SEALED_RESULT_TRACE_CAPACITY_V1 = 11,
    HAL_SEALED_RESULT_OVERFLOW_KIND_V1 = 12,
    HAL_SEALED_RESULT_OVERFLOW_FIRST_V1 = 13,
    HAL_SEALED_RESULT_OVERFLOW_COUNT_V1 = 14,
    HAL_SEALED_RESULT_ELAPSED_TICKS_V1 = 15
};

/* Production maintenance boundary. Paths are pinned in this implementation. */
uint64_t rt_hal_sealed_prepare_v1(int64_t deadline_ms);
int32_t rt_hal_sealed_seal_v1(uint64_t handle);
int32_t rt_hal_sealed_invoke_v1(uint64_t handle, int64_t operation_id,
                                int64_t invocation_id, int64_t fixture_id,
                                int64_t input_offset, int64_t input_length,
                                int64_t input_capacity, int64_t trace_capacity);
int32_t rt_hal_sealed_invoke_mode_v1(
    uint64_t handle, int32_t run_mode, int32_t preferred_provider,
    int64_t operation_id, int64_t invocation_id, int64_t fixture_id,
    int64_t input_offset, int64_t input_length, int64_t input_capacity,
    int64_t trace_capacity);
int32_t rt_hal_sealed_completed_mask_v1(uint64_t handle);
int64_t rt_hal_sealed_result_field_v1(uint64_t handle, int32_t lane,
                                      int32_t field);
int64_t rt_hal_sealed_sandbox_pid_v1(uint64_t handle, int32_t lane);
int32_t rt_hal_sealed_last_status_v1(uint64_t handle);
uint64_t rt_hal_sealed_hot_spawn_count_v1(uint64_t handle);
uint64_t rt_hal_sealed_hot_allocation_count_v1(uint64_t handle);
int32_t rt_hal_sealed_maintenance_shutdown_v1(uint64_t handle);

/* Focused tests use an explicit absolute launcher/worker configuration. */
uint64_t hal_sealed_facade_prepare_config_v1(
    const char *launcher, const char *pure_worker, const char *c_worker,
    const char *rust_worker, int64_t deadline_ms);

#endif
