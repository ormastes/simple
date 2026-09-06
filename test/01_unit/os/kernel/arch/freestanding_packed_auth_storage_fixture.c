#include <stdint.h>
#include <string.h>

#include "freestanding_packed_auth_storage.h"

static int expect_zero(const uint8_t *bytes, uint32_t len) {
    uint32_t i;
    for (i = 0U; i < len; ++i) if (bytes[i] != 0U) return 0;
    return 1;
}

int main(void) {
    SimpleOsPackedAuthLease secret;
    SimpleOsPackedAuthLease message;
    SimpleOsPackedAuthLease token;
    SimpleOsPackedAuthLease replacement;
    uint8_t secret_in[16];
    uint8_t secret_out[16];
    uint8_t message_in[80];
    uint8_t token_in[96];
    uint32_t i;

    for (i = 0U; i < 16U; ++i) secret_in[i] = (uint8_t)(i + 1U);
    for (i = 0U; i < 80U; ++i) message_in[i] = (uint8_t)(i ^ 0x5aU);
    for (i = 0U; i < 96U; ++i) token_in[i] = (uint8_t)(255U - i);

    if (simpleos_packed_auth_claim(SIMPLEOS_PACKED_AUTH_SECRET, &secret) != 0) return 1;
    if (simpleos_packed_auth_claim(SIMPLEOS_PACKED_AUTH_MESSAGE, &message) != 0) return 2;
    if (simpleos_packed_auth_claim(SIMPLEOS_PACKED_AUTH_X86_TOKEN, &token) != 0) return 3;
    if (simpleos_packed_auth_write(secret, secret_in, 16U) != 0) return 4;
    if (simpleos_packed_auth_write(message, message_in, 80U) != 0) return 5;
    if (simpleos_packed_auth_write(token, token_in, 96U) != 0) return 6;
    if ((simpleos_packed_auth_address(secret) & 15U) != 0U) return 7;
    if ((simpleos_packed_auth_address(message) & 15U) != 0U) return 8;
    if ((simpleos_packed_auth_address(token) & 15U) != 0U) return 9;
    if (simpleos_packed_auth_read(secret, secret_out, 16U) != 0) return 10;
    if (memcmp(secret_in, secret_out, 16U) != 0) return 11;
    if (simpleos_packed_auth_write(secret, secret_in, 15U) != -22) return 12;

    uintptr_t old_address = simpleos_packed_auth_address(token);
    uint32_t old_generation = token.generation;
    if (simpleos_packed_auth_release(token) != 0) return 13;
    if (simpleos_packed_auth_address(token) != 0U) return 14;
    if (simpleos_packed_auth_release(token) != -13) return 15;
    if (simpleos_packed_auth_claim(SIMPLEOS_PACKED_AUTH_X86_TOKEN, &replacement) != 0) return 16;
    if (replacement.slot != token.slot || replacement.generation == old_generation) return 17;
    if (simpleos_packed_auth_address(replacement) != old_address) return 18;
    if (!expect_zero((const uint8_t *)simpleos_packed_auth_address(replacement), 96U)) return 19;
    if (simpleos_packed_auth_write(token, token_in, 96U) != -13) return 20;

    if (simpleos_packed_auth_release(secret) != 0) return 21;
    if (simpleos_packed_auth_release(message) != 0) return 22;
    if (simpleos_packed_auth_release(replacement) != 0) return 23;

    uint64_t scalar = rt_packed_auth_claim(SIMPLEOS_PACKED_AUTH_MESSAGE);
    if (scalar == 0U) return 24;
    for (i = 0U; i < 80U; ++i) {
        if (rt_packed_auth_write_byte(scalar, i, i) != 0) return 25;
    }
    if (rt_packed_auth_write_byte(scalar, 80U, 0U) != -22) return 26;
    if ((rt_packed_auth_address(scalar) & 15U) != 0U) return 27;
    if (rt_packed_auth_release(scalar) != 0) return 28;
    if (rt_packed_auth_address(scalar) != 0U) return 29;
    return 0;
}
