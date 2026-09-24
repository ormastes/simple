#include <math.h>
#include <stdint.h>
#include <stdio.h>

static uint64_t bits(double value) {
    union { double f; uint64_t u; } rep = { value };
    return rep.u;
}

int main(void) {
    double x = 0x1.0000000000001p0;
    double y = 0x1.fffffffffffffp-1;
    double cancellation = fma(x, y, -1.0);
    if (bits(cancellation) != bits(0x1.ffffffffffffep-54)) {
        fprintf(stderr, "fma cancellation mismatch: %a\n", cancellation);
        return 1;
    }
    if (bits(fma(0x1p-1022, 0.5, 0x1p-1074)) !=
        bits(0x0.8000000000001p-1022)) return 4;
    if (bits(fma(2.0, 3.0, 4.0)) != bits(10.0)) return 2;
    if (!isnan(fma(INFINITY, 0.0, 1.0))) return 3;
    return 0;
}
