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

static simple_hal_captured_device_payload_v1 payload_for_opcode(
    uint32_t opcode, uint32_t token) {
    simple_hal_captured_device_payload_v1 value = random_payload(0u);
    value.opcode = opcode;
    value.read_once_token = token;
    if (opcode != 11u) value.capability_generation = 3u;
    if (opcode == 17u) {
        value.region.length = 0u;
        value.region.capacity = 0u;
        value.region.digest_hi = 0u;
        value.region.digest_lo = 0u;
    }
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
    {
        const uint32_t opcodes[4] = {11u, 17u, 18u, 22u};
        uint32_t index;
        for (index = 0u; index < 4u; ++index) {
            simple_hal_device_compare_owner_v1 owner;
            simple_hal_device_compare_receipt_v1 receipt;
            simple_hal_captured_device_payload_v1 captured =
                payload_for_opcode(opcodes[index], index + 1u);
            uint8_t provider;
            if (!simple_hal_device_compare_owner_init_v1(&owner, 77u, 4u,
                    SIMPLE_HAL_COMPARE_ALPHA_V1, 0u)) return 4;
            for (provider = 0u; provider < 3u; ++provider) {
                if (simple_hal_device_compare_submit_v1(&owner, provider,
                        &captured, recorded, sizeof(recorded), &captured,
                        same, sizeof(same)) !=
                        SIMPLE_HAL_PAYLOAD_REPLAYED_V1) return 5;
            }
            receipt = simple_hal_device_compare_get_receipt_v1(&owner);
            if (!receipt.complete || !receipt.equivalent ||
                !receipt.commit_allowed ||
                receipt.equivalent_provider_mask != 7u ||
                receipt.physical_effect != 0u ||
                receipt.allocation_count != 0u) return 6;
        }
    }
    {
        simple_hal_captured_device_payload_v1 captured =
            payload_for_opcode(18u, 3u);
        simple_hal_device_compare_owner_v1 owner;
        simple_hal_device_compare_receipt_v1 receipt;
        uint8_t provider;
        if (!simple_hal_device_compare_owner_init_v1(&owner, 77u, 4u,
                SIMPLE_HAL_COMPARE_ALPHA_V1, 0u)) return 7;
        for (provider = 0u; provider < 3u; ++provider) {
            const uint8_t *candidate = provider == 1u ? changed : same;
            (void)simple_hal_device_compare_submit_v1(&owner, provider,
                &captured, recorded, sizeof(recorded), &captured,
                candidate, sizeof(same));
        }
        receipt = simple_hal_device_compare_get_receipt_v1(&owner);
        if (receipt.commit_allowed || receipt.difference_provider_mask != 2u)
            return 8;

        if (!simple_hal_device_compare_owner_init_v1(&owner, 77u, 4u,
                SIMPLE_HAL_COMPARE_BETA_V1, 0u)) return 9;
        for (provider = 0u; provider < 3u; ++provider) {
            const uint8_t *candidate = provider == 1u ? changed : same;
            (void)simple_hal_device_compare_submit_v1(&owner, provider,
                &captured, recorded, sizeof(recorded), &captured,
                candidate, sizeof(same));
        }
        if (!simple_hal_device_compare_get_receipt_v1(&owner).commit_allowed)
            return 10;

        if (!simple_hal_device_compare_owner_init_v1(&owner, 77u, 4u,
                SIMPLE_HAL_COMPARE_NORMAL_V1, 2u) ||
            simple_hal_device_compare_submit_v1(&owner, 2u, &captured,
                recorded, sizeof(recorded), &captured, same, sizeof(same)) !=
                SIMPLE_HAL_PAYLOAD_REPLAYED_V1 ||
            !simple_hal_device_compare_get_receipt_v1(&owner).commit_allowed)
            return 11;
    }
    puts("hal-provider-device-payload-v1-selfcheck: PASS parity_mask=7 effects=0 allocations=0");
    return 0;
}
