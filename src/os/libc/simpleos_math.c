/*
 * SimpleOS Libc Shim — Basic math functions
 *
 * Provides minimal math routines sufficient for toolchain bootstrapping.
 * No libm dependency — all implemented from scratch.
 */

/* Function prototypes match simpleos_libc.h declarations */

double fabs(double x) {
    return x < 0.0 ? -x : x;
}

float fabsf(float x) {
    return x < 0.0f ? -x : x;
}

double sqrt(double x) {
    if (x != x) {
        union { double f; unsigned long long u; } rep = { x };
        rep.u |= 0x0008000000000000ULL;
        return rep.f;
    }
    if (x < 0.0) return __builtin_nan("");
    /* Preserve signed zero and avoid turning positive infinity into NaN in
     * the Newton step (inf / inf).  Both builtins are freestanding constants. */
    if (x == 0.0 || x == __builtin_inf()) return x;

    /* Newton-Raphson iteration */
    double guess = x * 0.5;
    for (int i = 0; i < 30; i++) {
        double next = (guess + x / guess) * 0.5;
        if (fabs(next - guess) < 1e-15 * fabs(guess))
            break;
        guess = next;
    }
    return guess;
}

float sqrtf(float x) {
    return (float)sqrt((double)x);
}
