#include <stdint.h>
#include <stdio.h>

#include "ntt_fixture.h"

_Static_assert(X25519MLKEM768_NTT_BATCH == 3, "Metal receipt batch changed");
_Static_assert(X25519MLKEM768_NTT_COEFFICIENTS == 256,
               "Metal receipt polynomial size changed");

int main(int argc, char **argv)
{
    if (argc != 2) {
        fprintf(stderr, "usage: %s FIXTURE.bin\n", argv[0]);
        return 2;
    }
    FILE *output = fopen(argv[1], "wb");
    if (output == NULL) {
        perror(argv[1]);
        return 1;
    }
    for (int polynomial = 0; polynomial < X25519MLKEM768_NTT_BATCH;
            ++polynomial) {
        for (int coefficient = 0;
                coefficient < X25519MLKEM768_NTT_COEFFICIENTS;
                ++coefficient) {
            uint32_t value = (uint32_t)x25519mlkem768_ntt_fixture_coefficient(
                polynomial, coefficient);
            unsigned char encoded[4] = {
                (unsigned char)value,
                (unsigned char)(value >> 8),
                (unsigned char)(value >> 16),
                (unsigned char)(value >> 24)
            };
            if (fwrite(encoded, sizeof(encoded), 1, output) != 1) {
                perror(argv[1]);
                fclose(output);
                return 1;
            }
        }
    }
    if (fclose(output) != 0) {
        perror(argv[1]);
        return 1;
    }
    return 0;
}
