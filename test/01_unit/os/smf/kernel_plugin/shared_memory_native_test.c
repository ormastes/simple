#include <stdint.h>
#include <stdio.h>
#include <string.h>

struct descriptor_v1 {
    uint32_t wire_version;
    uint32_t protocol_version;
    int64_t kind;
    int64_t generation;
    int64_t session_epoch;
    int64_t request_slot;
    int64_t request_epoch;
    uint64_t capability_bits;
    int64_t payload_offset;
    int64_t payload_length;
};

static int valid(const struct descriptor_v1 *descriptor, int64_t storage_bytes,
                 int64_t expected_offset, int64_t slot_payload_bytes) {
    if (descriptor->wire_version != 1 || descriptor->protocol_version != 1) return 0;
    if (storage_bytes < 0 || expected_offset < 0 || slot_payload_bytes < 0) return 0;
    if (descriptor->payload_offset != expected_offset) return 0;
    if (descriptor->payload_length < 0 || descriptor->payload_length > slot_payload_bytes) return 0;
    if (descriptor->payload_offset > storage_bytes) return 0;
    return descriptor->payload_length <= storage_bytes - descriptor->payload_offset;
}

int main(void) {
    uint8_t caller_owned_storage[16] = {0};
    struct descriptor_v1 frame = {1, 1, 3, 7, 3, 4, 9, 5, 8, 2};
    caller_owned_storage[8] = 11;
    caller_owned_storage[9] = 22;
    if (!valid(&frame, 16, 8, 8)) return 10;
    if (memcmp(caller_owned_storage + frame.payload_offset, "\x0b\x16", 2)) return 11;
    frame.payload_offset = 7;
    if (valid(&frame, 16, 8, 8)) return 20;
    frame.payload_offset = 8;
    frame.payload_length = 9;
    if (valid(&frame, 16, 8, 8)) return 21;
    frame.payload_length = 2;
    frame.protocol_version = 99;
    if (valid(&frame, 16, 8, 8)) return 22;
    puts("shared-memory worker native acceptance: PASS");
    return 0;
}

