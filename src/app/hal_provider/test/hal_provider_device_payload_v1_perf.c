#define _POSIX_C_SOURCE 200809L
#include "../hal_provider_device_payload_v1.h"

#include <stdint.h>
#include <stdio.h>
#include <time.h>

static uint64_t now_ns(void) {
    struct timespec value;
    if (clock_gettime(CLOCK_MONOTONIC, &value) != 0) return 0u;
    return (uint64_t)value.tv_sec * UINT64_C(1000000000) +
        (uint64_t)value.tv_nsec;
}

int main(void) {
    enum { iterations = 50000000 };
    uint8_t bytes[33] = {0};
    simple_hal_captured_device_payload_v1 value = {0};
    simple_hal_payload_cursor_v1 cursor = {77u, 0u, 1u, 0u, 0u, 1u};
    volatile uint64_t checksum = 0u;
    value.version = SIMPLE_HAL_DEVICE_PAYLOAD_V1;
    value.opcode = 11u;
    value.invocation_id = 77u;
    value.capability_id = 9u;
    value.read_once_token = 1u;
    value.grant_digest_hi = 31u;
    value.grant_digest_lo = 32u;
    value.region.offset = 1u;
    value.region.length = 32u;
    value.region.capacity = 32u;
    value.region.digest_hi = 51u;
    value.region.digest_lo = 52u;
    value.observation_status = 1u;
    value.interaction_digest_hi = 71u;
    value.interaction_digest_lo = 72u;
    value.sealed = 1u;
    uint64_t start = now_ns();
    for (uint32_t i = 0u; i < iterations; ++i) {
        cursor.next_sequence = 0u;
        cursor.consumed_count = 0u;
        cursor.read_once_consumed_mask = 0u;
        checksum += (uint64_t)simple_hal_payload_replay_exact_v1(
            &cursor, &value, bytes, sizeof(bytes),
            &value, bytes, sizeof(bytes));
    }
    uint64_t elapsed = now_ns() - start;
    if (checksum != 0u || elapsed == 0u) return 1;
    printf("iterations=%u elapsed_ns=%llu ns_per_replay=%.3f allocations=0\n",
        iterations, (unsigned long long)elapsed,
        (double)elapsed / (double)iterations);
    return 0;
}
