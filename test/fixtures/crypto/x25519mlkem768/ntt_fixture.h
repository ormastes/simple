#ifndef X25519MLKEM768_NTT_FIXTURE_H
#define X25519MLKEM768_NTT_FIXTURE_H

#include <stdint.h>

#define X25519MLKEM768_NTT_FIXTURE_ID "ntt-v1-p97-i29-c17-q3329"
#define X25519MLKEM768_NTT_MODULUS 3329
#define X25519MLKEM768_NTT_COEFFICIENTS 256
#define X25519MLKEM768_NTT_BATCH 3

static inline int32_t x25519mlkem768_ntt_fixture_coefficient(
        int polynomial_index, int coefficient_index) {
    return (int32_t)((polynomial_index * 97 + coefficient_index * 29 + 17) %
                     X25519MLKEM768_NTT_MODULUS);
}

#endif
