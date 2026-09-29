#include <stdint.h>
#include <stdio.h>

extern double cos(double x);

static double absolute(double value) {
    return value < 0.0 ? -value : value;
}

static uint64_t bits(double value) {
    union { double f; uint64_t u; } raw;
    raw.f = value;
    return raw.u;
}

int main(void) {
    unsigned failures = 0;
    double positive_zero = cos(0.0);
    double negative_zero = cos(-0.0);

    if (bits(positive_zero) != UINT64_C(0x3ff0000000000000)) {
        fprintf(stderr, "cos(+0) bits=%016llx expected=3ff0000000000000\n",
                (unsigned long long)bits(positive_zero));
        failures++;
    }
    if (bits(negative_zero) != UINT64_C(0x3ff0000000000000)) {
        fprintf(stderr, "cos(-0) bits=%016llx expected=3ff0000000000000\n",
                (unsigned long long)bits(negative_zero));
        failures++;
    }
    if (cos(1.0e-12) > 1.0 || cos(-1.0e-12) > 1.0) {
        fprintf(stderr, "cos(tiny) exceeded mathematical upper bound\n");
        failures++;
    }
    if (bits(cos(3.14159265358979323846)) != UINT64_C(0xbff0000000000000)) {
        fprintf(stderr, "cos(pi) is not exactly -1\n");
        failures++;
    }
    if (absolute(cos(1.0) - 0.5403023058681398) > 1.0e-15 ||
        absolute(cos(-2.0) - -0.4161468365471424) > 1.0e-15 ||
        absolute(cos(3.0) - -0.9899924966004454) > 1.0e-15) {
        fprintf(stderr, "cos ordinary/quadrant accuracy regressed\n");
        failures++;
    }
    if (bits(cos(2.0)) != bits(cos(-2.0)) ||
        absolute(cos(3.14159265358979323846 - 1.0e-8) + 1.0) > 1.0e-15) {
        fprintf(stderr, "cos even symmetry or near-pi accuracy regressed\n");
        failures++;
    }

    if (failures == 0) {
        puts("simpleos cos zero selfcheck: PASS (6 checks)");
    }
    return (int)failures;
}
