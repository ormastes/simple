/*
 * Simple Runtime — Math FFI Functions
 *
 * C equivalents of the Rust math FFI in src/compiler_rust/runtime/src/value/ffi/math.rs.
 * Build: cc -c -fPIC -O2 -std=gnu11 runtime_math.c -o runtime_math.o
 */

#include <math.h>
#include <stdint.h>
#include <stdlib.h>

double rt_math_pow(double base, double exp) { return pow(base, exp); }
double rt_math_log(double x)               { return log(x); }
double rt_math_log10(double x)             { return log10(x); }
double rt_math_log2(double x)              { return log2(x); }
double rt_math_exp(double x)               { return exp(x); }
double rt_math_sqrt(double x)              { return sqrt(x); }
double rt_math_cbrt(double x)              { return cbrt(x); }
double rt_math_sin(double x)               { return sin(x); }
double rt_math_cos(double x)               { return cos(x); }
double rt_math_tan(double x)               { return tan(x); }
double rt_math_asin(double x)              { return asin(x); }
double rt_math_acos(double x)              { return acos(x); }
double rt_math_atan(double x)              { return atan(x); }
double rt_math_atan2(double y, double x)   { return atan2(y, x); }
double rt_math_sinh(double x)              { return sinh(x); }
double rt_math_cosh(double x)              { return cosh(x); }
double rt_math_tanh(double x)              { return tanh(x); }
double rt_math_floor(double x)             { return floor(x); }
double rt_math_ceil(double x)              { return ceil(x); }
double rt_math_round(double x)             { return round(x); }
double rt_math_trunc(double x)             { return trunc(x); }
double rt_math_abs(double x)               { return fabs(x); }
double rt_math_hypot(double x, double y)   { return hypot(x, y); }

int64_t rt_math_gcd(int64_t a, int64_t b) {
    a = llabs(a);
    b = llabs(b);
    while (b != 0) {
        int64_t t = b;
        b = a % b;
        a = t;
    }
    return a;
}

double rt_math_min(double a, double b)                        { return fmin(a, b); }
double rt_math_max(double a, double b)                        { return fmax(a, b); }
double rt_math_clamp(double x, double min, double max)        { return x < min ? min : (x > max ? max : x); }
double rt_math_fma(double x, double y, double z)              { return fma(x, y, z); }
