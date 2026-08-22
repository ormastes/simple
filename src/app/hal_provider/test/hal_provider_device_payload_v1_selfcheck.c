#include "../hal_provider_device_payload_v1.h"

#include <stdint.h>
#include <stdio.h>

static simple_hal_captured_device_payload_v1 random_payload(uint32_t sequence) {
    simple_hal_captured_device_payload_v1 value = {0};
    value.version = SIMPLE_HAL_DEVICE_PAYLOAD_V1;
    value.opcode = 11u;
    value.invocation_id = 77u;
    value.sequence = sequence;
    value.capability_id = 9u;
    value.read_once_token = 1u;
    value.grant_digest_hi = 31u;
    value.grant_digest_lo = 32u;
    value.region.offset = 1u;
    value.region.length = 4u;
    value.region.capacity = 4u;
    value.region.digest_hi = 51u;
    value.region.digest_lo = 52u;
    value.observation_status = 1u;
    value.interaction_digest_hi = 71u;
    value.interaction_digest_lo = 72u;
    value.sealed = 1u;
    return value;
}

int main(void) {
    uint8_t recorded[5] = {0u, 1u, 2u, 3u, 4u};
    uint8_t same[5] = {9u, 1u, 2u, 3u, 4u};
    uint8_t changed[5] = {9u, 1u, 2u, 99u, 4u};
    simple_hal_captured_device_payload_v1 value = random_payload(0u);
    simple_hal_payload_cursor_v1 cursor = {77u, 0u, 4u, 0u, 0u, 1u};
    if (simple_hal_payload_replay_exact_v1(&cursor, &value, recorded,
            sizeof(recorded), &value, same, sizeof(same)) !=
            SIMPLE_HAL_PAYLOAD_REPLAYED_V1 || cursor.consumed_count != 1u) {
        return 1;
    }
    cursor.next_sequence = 0u;
    cursor.consumed_count = 0u;
    cursor.read_once_consumed_mask = 0u;
    if (simple_hal_payload_replay_exact_v1(&cursor, &value, recorded,
            sizeof(recorded), &value, changed, sizeof(changed)) !=
            SIMPLE_HAL_PAYLOAD_DIFFERENCE_V1) {
        return 2;
    }
    if (simple_hal_payload_replay_exact_v1(&cursor, &value, recorded, 3u,
            &value, same, sizeof(same)) !=
            SIMPLE_HAL_PAYLOAD_REGION_OVERFLOW_V1) {
        return 3;
    }
    puts("hal-provider-device-payload-v1-selfcheck: PASS");
    return 0;
}
