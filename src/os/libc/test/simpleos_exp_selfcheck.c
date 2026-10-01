#include <stdint.h>
#include <stdio.h>

double exp(double);

static uint64_t bits(double value) {
    union { double f; uint64_t u; } rep = { value };
    return rep.u;
}

static double from_bits(uint64_t value) {
    union { double f; uint64_t u; } rep = { .u = value };
    return rep.f;
}

int main(void) {
    static const struct {
        double input;
        double expected;
    } cases[] = {
        {-745.0, 0x0.0000000000001p-1022},
        {-0x1.74910d52d3052p+9, 0.0},
        {-0x1.74910d52d3051p+9, 0x0.0000000000001p-1022},
        {-0x1.74910d52d3050p+9, 0x0.0000000000001p-1022},
        {-744.0, 0x0.0000000000002p-1022},
        {-710.0, 0x0.33802fd28b3c3p-1022},
        {-708.0, 0x1.7c8ab2288c9abp-1022},
        {-100.0, 0x1.a8c1f14e2af5dp-145},
        {-1.0, 0x1.78b56362cef38p-2},
        {-0.5, 0x1.368b2fc6f960ap-1},
        {0.0, 0x1.0000000000000p+0},
        {0.5, 0x1.a61298e1e069cp+0},
        {1.0, 0x1.5bf0a8b145769p+1},
        {100.0, 0x1.3494a9b171bf5p+144},
        {700.0, 0x1.d945df4f8ec8ep+1009},
        {709.0, 0x1.d422d2be5dc9bp+1022},
        {709.5, 0x1.81e9b4b52d0c9p+1023},
        {0x1.62e42fefa39eep+9, 0x1.ffffffffffb2ap+1023},
        {0x1.62e42fefa39efp+9, 0x1.fffffffffff2ap+1023},
        {0x1.62e42fefa39f0p+9, __builtin_inf()},
    };

    for (unsigned i = 0; i < sizeof(cases) / sizeof(cases[0]); ++i) {
        volatile double input = cases[i].input;
        double actual = exp(input);
        uint64_t actual_bits = bits(actual);
        uint64_t expected_bits = bits(cases[i].expected);
        uint64_t ulp = actual_bits > expected_bits
            ? actual_bits - expected_bits : expected_bits - actual_bits;
        if (ulp > 1) {
            fprintf(stderr, "exp(%a) exceeds 1 ULP: expected %a, got %a\n",
                    cases[i].input, cases[i].expected, actual);
            return (int)i + 1;
        }
    }
    /* Preserve the scoped exp(1) repair and prove the three original range
     * failures do not merely move to a nearby wrong class/value. */
    if (bits(exp(1.0)) != bits(0x1.5bf0a8b145769p+1)) return 20;
    if (bits(exp(-745.0)) != bits(0x0.0000000000001p-1022)) return 21;
    if (bits(exp(-710.0)) != bits(0x0.33802fd28b3c3p-1022)) return 22;
    if (bits(exp(709.5)) != bits(0x1.81e9b4b52d0c9p+1023)) return 23;
    if (bits(exp(0.0)) != bits(1.0)) return 24;
    if (bits(exp(from_bits(UINT64_C(0x8000000000000000)))) != bits(1.0)) return 25;
    if (bits(exp(from_bits(UINT64_C(0x7ff0000000000000)))) !=
        UINT64_C(0x7ff0000000000000)) return 26;
    if (bits(exp(from_bits(UINT64_C(0xfff0000000000000)))) != bits(0.0)) return 27;
    if (bits(exp(from_bits(UINT64_C(0x7ff8123456789abc)))) !=
        UINT64_C(0x7ff8123456789abc)) return 28;
    if (bits(exp(from_bits(UINT64_C(0x7ff0123456789abc)))) !=
        UINT64_C(0x7ff8123456789abc)) return 29;
    return 0;
}
