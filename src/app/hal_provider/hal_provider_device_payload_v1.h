#ifndef SIMPLE_HAL_PROVIDER_DEVICE_PAYLOAD_V1_H
#define SIMPLE_HAL_PROVIDER_DEVICE_PAYLOAD_V1_H

#include <stddef.h>
#include <stdint.h>

#define SIMPLE_HAL_DEVICE_PAYLOAD_V1 1u
#define SIMPLE_HAL_DEVICE_PAYLOAD_MAX_BYTES_V1 65536u

typedef enum simple_hal_payload_replay_status_v1 {
    SIMPLE_HAL_PAYLOAD_REPLAYED_V1 = 0,
    SIMPLE_HAL_PAYLOAD_INVALID_V1 = 1,
    SIMPLE_HAL_PAYLOAD_WRONG_SEQUENCE_V1 = 2,
    SIMPLE_HAL_PAYLOAD_ALREADY_CONSUMED_V1 = 3,
    SIMPLE_HAL_PAYLOAD_REGION_OVERFLOW_V1 = 4,
    SIMPLE_HAL_PAYLOAD_DIFFERENCE_V1 = 5
} simple_hal_payload_replay_status_v1;

typedef struct simple_hal_caller_region_v1 {
    uint32_t offset;
    uint32_t length;
    uint32_t capacity;
    uint64_t digest_hi;
    uint64_t digest_lo;
} simple_hal_caller_region_v1;

typedef struct simple_hal_captured_device_payload_v1 {
    uint32_t version;
    uint32_t opcode;
    uint64_t invocation_id;
    uint32_t sequence;
    uint32_t capability_id;
    uint32_t capability_generation;
    uint32_t read_once_token;
    uint64_t grant_digest_hi;
    uint64_t grant_digest_lo;
    int64_t scalar0;
    int64_t scalar1;
    simple_hal_caller_region_v1 region;
    uint32_t observation_status;
    int32_t observation_status_code;
    uint64_t interaction_digest_hi;
    uint64_t interaction_digest_lo;
    uint8_t sealed;
} simple_hal_captured_device_payload_v1;

typedef struct simple_hal_payload_cursor_v1 {
    uint64_t invocation_id;
    uint32_t next_sequence;
    uint32_t capacity;
    uint32_t consumed_count;
    uint64_t read_once_consumed_mask;
    uint8_t sealed;
} simple_hal_payload_cursor_v1;

typedef enum simple_hal_device_compare_mode_v1 {
    SIMPLE_HAL_COMPARE_ALPHA_V1 = 0,
    SIMPLE_HAL_COMPARE_BETA_V1 = 1,
    SIMPLE_HAL_COMPARE_NORMAL_V1 = 2
} simple_hal_device_compare_mode_v1;

typedef struct simple_hal_device_compare_owner_v1 {
    uint64_t invocation_id;
    uint8_t mode;
    uint8_t preferred_provider;
    uint8_t expected_provider_mask;
    uint8_t received_provider_mask;
    uint8_t equivalent_provider_mask;
    uint8_t difference_provider_mask;
    uint8_t duplicate_provider_mask;
    simple_hal_payload_cursor_v1 cursors[3];
    uint8_t sealed;
} simple_hal_device_compare_owner_v1;

typedef struct simple_hal_device_compare_receipt_v1 {
    uint8_t complete;
    uint8_t equivalent;
    uint8_t commit_allowed;
    uint8_t expected_provider_mask;
    uint8_t received_provider_mask;
    uint8_t equivalent_provider_mask;
    uint8_t difference_provider_mask;
    uint8_t duplicate_provider_mask;
    uint8_t physical_effect;
    uint32_t allocation_count;
} simple_hal_device_compare_receipt_v1;

int simple_hal_captured_device_payload_well_formed_v1(
    const simple_hal_captured_device_payload_v1 *value);

simple_hal_payload_replay_status_v1 simple_hal_payload_replay_exact_v1(
    simple_hal_payload_cursor_v1 *cursor,
    const simple_hal_captured_device_payload_v1 *recorded,
    const uint8_t *recorded_bytes, size_t recorded_capacity,
    const simple_hal_captured_device_payload_v1 *candidate,
    const uint8_t *candidate_bytes, size_t candidate_capacity);

int simple_hal_device_compare_owner_init_v1(
    simple_hal_device_compare_owner_v1 *owner, uint64_t invocation_id,
    uint32_t capacity, simple_hal_device_compare_mode_v1 mode,
    uint8_t preferred_provider);

simple_hal_payload_replay_status_v1 simple_hal_device_compare_submit_v1(
    simple_hal_device_compare_owner_v1 *owner, uint8_t provider,
    const simple_hal_captured_device_payload_v1 *recorded,
    const uint8_t *recorded_bytes, size_t recorded_capacity,
    const simple_hal_captured_device_payload_v1 *candidate,
    const uint8_t *candidate_bytes, size_t candidate_capacity);

simple_hal_device_compare_receipt_v1 simple_hal_device_compare_get_receipt_v1(
    const simple_hal_device_compare_owner_v1 *owner);

#endif
