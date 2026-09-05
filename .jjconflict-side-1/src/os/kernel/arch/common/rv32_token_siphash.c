#include "rv32_token_siphash.h"
#include <stddef.h>

static uint64_t rotl64(uint64_t value, unsigned shift) {
    return (value << shift) | (value >> (64U - shift));
}

static uint64_t load64le(const uint8_t *p) {
    uint64_t out = 0;
    unsigned i;
    for (i = 0; i < 8; ++i) out |= ((uint64_t)p[i]) << (8U * i);
    return out;
}

#define SIPROUND() do {                 \
    v0 += v1; v1 = rotl64(v1, 13);      \
    v1 ^= v0; v0 = rotl64(v0, 32);      \
    v2 += v3; v3 = rotl64(v3, 16);      \
    v3 ^= v2;                           \
    v0 += v3; v3 = rotl64(v3, 21);      \
    v3 ^= v0;                           \
    v2 += v1; v1 = rotl64(v1, 17);      \
    v1 ^= v2; v2 = rotl64(v2, 32);      \
} while (0)

uint64_t simpleos_token_siphash24_bytes(const uint8_t key[16],
                                        const uint8_t *message,
                                        uint32_t message_len) {
    uint64_t k0 = load64le(key), k1 = load64le(key + 8);
    uint64_t v0 = UINT64_C(0x736f6d6570736575) ^ k0;
    uint64_t v1 = UINT64_C(0x646f72616e646f6d) ^ k1;
    uint64_t v2 = UINT64_C(0x6c7967656e657261) ^ k0;
    uint64_t v3 = UINT64_C(0x7465646279746573) ^ k1;
    uint32_t offset = 0;
    uint64_t tail = ((uint64_t)message_len) << 56;
    while (offset + 8U <= message_len) {
        uint64_t word = load64le(message + offset);
        v3 ^= word; SIPROUND(); SIPROUND(); v0 ^= word;
        offset += 8U;
    }
    {
        unsigned shift = 0;
        while (offset < message_len) {
            tail |= ((uint64_t)message[offset++]) << shift;
            shift += 8U;
        }
    }
    v3 ^= tail; SIPROUND(); SIPROUND(); v0 ^= tail;
    v2 ^= UINT64_C(0xff);
    SIPROUND(); SIPROUND(); SIPROUND(); SIPROUND();
    return v0 ^ v1 ^ v2 ^ v3;
}

uint64_t rt_rv32_token_siphash24(uint32_t key_address,
                                 uint32_t message_address,
                                 uint32_t message_len) {
    const uint8_t *key = (const uint8_t *)(uintptr_t)key_address;
    const uint8_t *message = (const uint8_t *)(uintptr_t)message_address;
    if (key == NULL || (message == NULL && message_len != 0U)) return 0;
    return simpleos_token_siphash24_bytes(key, message, message_len);
}
