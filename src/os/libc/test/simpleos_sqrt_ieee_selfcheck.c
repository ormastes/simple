#include <stdint.h>
#include <stdio.h>

double sqrt(double x);

static uint64_t bits(double value) {
    union { double f; uint64_t u; } rep = { value };
    return rep.u;
}

static double from_bits(uint64_t value) {
    union { double f; uint64_t u; } rep = { .u = value };
    return rep.f;
}

int main(void) {
    double negative = sqrt(-1.0);
    if (negative == negative) {
        fprintf(stderr, "sqrt(-1) must be NaN, got %a\n", negative);
        return 1;
    }
    if (bits(sqrt(-0.0)) != UINT64_C(0x8000000000000000)) return 2;
    if (bits(sqrt(__builtin_inf())) != UINT64_C(0x7ff0000000000000)) return 3;
    if (sqrt(4.0) != 2.0) return 4;
    if (bits(sqrt(from_bits(UINT64_C(0x7ff0000000000001)))) !=
        UINT64_C(0x7ff8000000000001)) return 5;
    if (bits(sqrt(from_bits(UINT64_C(0xfff8000000001234)))) !=
        UINT64_C(0xfff8000000001234)) return 6;
    return 0;
}
