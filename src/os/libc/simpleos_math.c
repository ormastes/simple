/*
 * SimpleOS Libc Shim — Basic math functions
 *
 * Provides minimal math routines sufficient for toolchain bootstrapping.
 * No libm dependency — all implemented from scratch.
 */

#include "simpleos_libc.h"

double fabs(double x) {
    return x < 0.0 ? -x : x;
}

float fabsf(float x) {
    return x < 0.0f ? -x : x;
}

double sqrt(double x) {
    if (x < 0.0) return 0.0;   /* NaN not available in freestanding */
    if (x == 0.0) return 0.0;

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
