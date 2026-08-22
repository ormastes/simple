#include "hal_provider_device_payload_v1.h"

#include <string.h>

static int digest_present(uint64_t hi, uint64_t lo) {
    return hi != 0u || lo != 0u;
}

static int region_well_formed(const simple_hal_caller_region_v1 *region) {
    return region != NULL &&
        region->length <= region->capacity &&
        region->capacity <= SIMPLE_HAL_DEVICE_PAYLOAD_MAX_BYTES_V1 &&
        ((region->length == 0u && region->digest_hi == 0u &&
          region->digest_lo == 0u) ||
         (region->length != 0u &&
          digest_present(region->digest_hi, region->digest_lo)));
}

static int region_fits(const simple_hal_caller_region_v1 *region,
                       size_t capacity) {
    return region_well_formed(region) &&
        (size_t)region->offset <= capacity &&
        (size_t)region->length <= capacity - (size_t)region->offset;
}

static int opcode_requires_region(uint32_t opcode) {
    return opcode == 11u || opcode == 18u || opcode == 19u ||
        opcode == 21u || opcode == 22u;
}

static int opcode_requires_read_once(uint32_t opcode) {
    return opcode == 11u || opcode == 17u || opcode == 18u || opcode == 22u;
}

int simple_hal_captured_device_payload_well_formed_v1(
    const simple_hal_captured_device_payload_v1 *value) {
    if (value == NULL || value->version != SIMPLE_HAL_DEVICE_PAYLOAD_V1 ||
        value->invocation_id == 0u || value->capability_id == 0u ||
        value->read_once_token > 62u || value->sealed != 1u ||
        !region_well_formed(&value->region) ||
        !digest_present(value->interaction_digest_hi,
                        value->interaction_digest_lo)) {
        return 0;
    }
    /* RandomFill is opcode 11 and has no physical-device grant. All device
       opcodes (16..23) are bound to one captured grant generation/digest. */
    if (value->opcode == 11u) {
        return value->capability_generation == 0u &&
            digest_present(value->grant_digest_hi, value->grant_digest_lo) &&
            value->read_once_token != 0u && value->region.length != 0u;
    }
    if (value->opcode < 16u || value->opcode > 23u ||
        value->capability_generation == 0u ||
        !digest_present(value->grant_digest_hi, value->grant_digest_lo)) {
        return 0;
    }
    return opcode_requires_region(value->opcode) == (value->region.length != 0u) &&
        opcode_requires_read_once(value->opcode) ==
            (value->read_once_token != 0u);
}

simple_hal_payload_replay_status_v1 simple_hal_payload_replay_exact_v1(
    simple_hal_payload_cursor_v1 *cursor,
    const simple_hal_captured_device_payload_v1 *recorded,
    const uint8_t *recorded_bytes, size_t recorded_capacity,
    const simple_hal_captured_device_payload_v1 *candidate,
    const uint8_t *candidate_bytes, size_t candidate_capacity) {
    uint64_t token_mask;
    if (cursor == NULL || cursor->sealed != 1u ||
        !simple_hal_captured_device_payload_well_formed_v1(recorded) ||
        !simple_hal_captured_device_payload_well_formed_v1(candidate)) {
        return SIMPLE_HAL_PAYLOAD_INVALID_V1;
    }
    if (recorded->invocation_id != cursor->invocation_id ||
        candidate->invocation_id != cursor->invocation_id ||
        recorded->sequence != cursor->next_sequence ||
        candidate->sequence != cursor->next_sequence ||
        cursor->consumed_count >= cursor->capacity) {
        return SIMPLE_HAL_PAYLOAD_WRONG_SEQUENCE_V1;
    }
    if (!region_fits(&recorded->region, recorded_capacity) ||
        !region_fits(&candidate->region, candidate_capacity) ||
        (recorded->region.length != 0u &&
         (recorded_bytes == NULL || candidate_bytes == NULL))) {
        return SIMPLE_HAL_PAYLOAD_REGION_OVERFLOW_V1;
    }
    token_mask = recorded->read_once_token == 0u ? 0u :
        UINT64_C(1) << recorded->read_once_token;
    if (token_mask != 0u &&
        (cursor->read_once_consumed_mask & token_mask) != 0u) {
        return SIMPLE_HAL_PAYLOAD_ALREADY_CONSUMED_V1;
    }
    if (recorded->opcode != candidate->opcode ||
        recorded->capability_id != candidate->capability_id ||
        recorded->capability_generation != candidate->capability_generation ||
        recorded->read_once_token != candidate->read_once_token ||
        recorded->grant_digest_hi != candidate->grant_digest_hi ||
        recorded->grant_digest_lo != candidate->grant_digest_lo ||
        recorded->scalar0 != candidate->scalar0 ||
        recorded->scalar1 != candidate->scalar1 ||
        recorded->observation_status != candidate->observation_status ||
        recorded->observation_status_code != candidate->observation_status_code ||
        recorded->interaction_digest_hi != candidate->interaction_digest_hi ||
        recorded->interaction_digest_lo != candidate->interaction_digest_lo ||
        recorded->region.length != candidate->region.length ||
        recorded->region.digest_hi != candidate->region.digest_hi ||
        recorded->region.digest_lo != candidate->region.digest_lo ||
        (recorded->region.length != 0u &&
         memcmp(recorded_bytes + recorded->region.offset,
                candidate_bytes + candidate->region.offset,
                recorded->region.length) != 0)) {
        return SIMPLE_HAL_PAYLOAD_DIFFERENCE_V1;
    }
    cursor->next_sequence += 1u;
    cursor->consumed_count += 1u;
    cursor->read_once_consumed_mask |= token_mask;
    return SIMPLE_HAL_PAYLOAD_REPLAYED_V1;
}
