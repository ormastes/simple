#include <math.h>
#include <stdint.h>
#include <stdio.h>

double simpleos_sqrt(double x);

static double from_bits(uint64_t value) {
    union { uint64_t u; double f; } rep = { value };
    return rep.f;
}

static uint64_t bits(double value) {
    union { double f; uint64_t u; } rep = { value };
    return rep.u;
}

int main(void) {
    uint64_t state = UINT64_C(0x9e3779b97f4a7c15);
    for (unsigned i = 0; i < 100000; ++i) {
        state = state * UINT64_C(6364136223846793005) + 1;
        uint64_t input_bits = state & UINT64_C(0x7fffffffffffffff);
        if (input_bits >= UINT64_C(0x7ff0000000000000)) {
            input_bits >>= 1;
        }
        double input = from_bits(input_bits);
        uint64_t got = bits(simpleos_sqrt(input));
        uint64_t want = bits(sqrt(input));
        if (got != want) {
            fprintf(stderr, "sqrt mismatch input=%016llx got=%016llx want=%016llx\n",
                    (unsigned long long)input_bits, (unsigned long long)got,
                    (unsigned long long)want);
            return 1;
        }
    }
    return 0;
}
