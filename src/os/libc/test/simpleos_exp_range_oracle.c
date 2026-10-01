#include <math.h>
#include <stdint.h>
#include <stdio.h>

double simpleos_exp(double);

static uint64_t bits(double value) {
    union { double f; uint64_t u; } rep = { value };
    return rep.u;
}

int main(void) {
    uint64_t max_ulp = 0;
    double worst = 0.0;
    const unsigned samples = 200001;

    for (unsigned i = 0; i < samples; ++i) {
        double x = -745.0 + (1454.75 * (double)i) / (double)(samples - 1);
        double actual = simpleos_exp(x);
        double expected = exp(x);
        uint64_t a = bits(actual);
        uint64_t e = bits(expected);
        uint64_t ulp = a > e ? a - e : e - a;
        if (ulp > max_ulp) {
            max_ulp = ulp;
            worst = x;
        }
    }

    if (max_ulp > 1) {
        fprintf(stderr, "exp range exceeds 1 ULP at %a: max=%llu\n",
                worst, (unsigned long long)max_ulp);
        return 1;
    }
    printf("exp range: %u samples, max=%llu ULP at %a\n", samples,
           (unsigned long long)max_ulp, worst);
    return 0;
}
