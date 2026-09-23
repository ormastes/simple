#include <stdint.h>
#include <stdio.h>

double exp(double);

static uint64_t bits(double value) {
    union { double f; uint64_t u; } rep = { value };
    return rep.u;
}

int main(void) {
    volatile double input = 1.0;
    double actual = exp(input);
    double expected = 0x1.5bf0a8b145769p+1;

    if (bits(actual) != bits(expected)) {
        fprintf(stderr, "exp(1) mismatch: expected %a, got %a\n",
                expected, actual);
        return 1;
    }
    if (bits(exp(0.0)) != bits(1.0)) return 2;
    return 0;
}
