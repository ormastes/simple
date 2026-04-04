/*
 * SimpleOS Libc Shim -- Extended math library
 *
 * Full math functions using polynomial/Taylor approximations.
 * All implemented from scratch -- no libm dependency.
 * Extends simpleos_math.c (which provides fabs, fabsf, sqrt, sqrtf).
 */

#include "include/math.h"
#include <stdint.h>

/* ====================================================================
 * Constants
 * ==================================================================== */

static const double PI        = 3.14159265358979323846;
static const double PI_2      = 1.57079632679489661923;
static const double TWO_PI    = 6.28318530717958647692;
static const double LN2       = 0.693147180559945309417;
static const double LN10      = 2.30258509299404568402;
static const double LOG2E     = 1.44269504088896340736;

/* ====================================================================
 * Bit manipulation helpers for IEEE 754 doubles
 * ==================================================================== */

typedef union {
    double   f;
    uint64_t u;
    int64_t  i;
} double_bits;

typedef union {
    float    f;
    uint32_t u;
    int32_t  i;
} float_bits;

static double _make_double(uint64_t bits) {
    double_bits db;
    db.u = bits;
    return db.f;
}

static uint64_t _double_bits(double x) {
    double_bits db;
    db.f = x;
    return db.u;
}

/* ====================================================================
 * 1. Trigonometric functions
 * ==================================================================== */

/* Reduce angle to [-PI, PI] */
static double _reduce_angle(double x) {
    /* Use repeated subtraction for moderate values, fmod-like for large */
    if (x >= -PI && x <= PI) return x;
    x = x - TWO_PI * (double)(long long)(x / TWO_PI);
    if (x > PI)  x -= TWO_PI;
    if (x < -PI) x += TWO_PI;
    return x;
}

double sin(double x) {
    /* Handle special cases */
    if (x != x) return x; /* NaN */

    x = _reduce_angle(x);

    /* Taylor series: x - x^3/3! + x^5/5! - x^7/7! + ...
     * Use Horner-like evaluation for 13 terms (accurate to ~1e-15) */
    double x2 = x * x;
    double term = x;
    double sum  = x;

    /* 13 terms of Taylor series */
    term *= -x2 / (2.0 * 3.0);    sum += term;  /*  3 */
    term *= -x2 / (4.0 * 5.0);    sum += term;  /*  5 */
    term *= -x2 / (6.0 * 7.0);    sum += term;  /*  7 */
    term *= -x2 / (8.0 * 9.0);    sum += term;  /*  9 */
    term *= -x2 / (10.0 * 11.0);  sum += term;  /* 11 */
    term *= -x2 / (12.0 * 13.0);  sum += term;  /* 13 */
    term *= -x2 / (14.0 * 15.0);  sum += term;  /* 15 */
    term *= -x2 / (16.0 * 17.0);  sum += term;  /* 17 */
    term *= -x2 / (18.0 * 19.0);  sum += term;  /* 19 */
    term *= -x2 / (20.0 * 21.0);  sum += term;  /* 21 */
    term *= -x2 / (22.0 * 23.0);  sum += term;  /* 23 */
    term *= -x2 / (24.0 * 25.0);  sum += term;  /* 25 */

    return sum;
}

double cos(double x) {
    return sin(x + PI_2);
}

double tan(double x) {
    double c = cos(x);
    if (c == 0.0) return _make_double(0x7FF0000000000000ULL); /* +inf */
    return sin(x) / c;
}

/* ====================================================================
 * 2. Inverse trigonometric functions
 * ==================================================================== */

double atan(double x) {
    /* For |x| > 1: atan(x) = pi/2 - atan(1/x)  (x > 0)
     *              atan(x) = -pi/2 - atan(1/x) (x < 0) */
    int negate = 0;
    int invert = 0;

    if (x < 0.0) { x = -x; negate = 1; }
    if (x > 1.0) { x = 1.0 / x; invert = 1; }

    /* For |x| <= 1: Taylor series x - x^3/3 + x^5/5 - x^7/7 + ...
     * Use more terms for better accuracy near |x| = 1 */
    double x2 = x * x;
    double term = x;
    double sum  = x;

    /* 20 terms for good accuracy near |x| = 1 */
    for (int n = 1; n <= 30; n++) {
        term *= -x2;
        double contrib = term / (2.0 * n + 1.0);
        sum += contrib;
        if (fabs(contrib) < 1e-16) break;
    }

    if (invert) sum = PI_2 - sum;
    if (negate) sum = -sum;
    return sum;
}

double atan2(double y, double x) {
    if (x > 0.0)          return atan(y / x);
    if (x < 0.0 && y >= 0.0) return atan(y / x) + PI;
    if (x < 0.0 && y < 0.0)  return atan(y / x) - PI;
    if (x == 0.0 && y > 0.0)  return PI_2;
    if (x == 0.0 && y < 0.0)  return -PI_2;
    return 0.0; /* x == 0, y == 0 */
}

double asin(double x) {
    if (x < -1.0 || x > 1.0) return _make_double(0x7FF8000000000000ULL); /* NaN */
    if (x == 1.0)  return PI_2;
    if (x == -1.0) return -PI_2;
    return atan2(x, sqrt(1.0 - x * x));
}

double acos(double x) {
    if (x < -1.0 || x > 1.0) return _make_double(0x7FF8000000000000ULL); /* NaN */
    return atan2(sqrt(1.0 - x * x), x);
}

/* ====================================================================
 * 3. Hyperbolic functions
 * ==================================================================== */

/* Forward declaration -- exp is defined below */
double exp(double x);

double sinh(double x) {
    if (fabs(x) < 1e-10) return x; /* small x approximation */
    double ex = exp(x);
    return (ex - 1.0 / ex) * 0.5;
}

double cosh(double x) {
    double ex = exp(x);
    return (ex + 1.0 / ex) * 0.5;
}

double tanh(double x) {
    if (x > 20.0)  return 1.0;
    if (x < -20.0) return -1.0;
    double e2x = exp(2.0 * x);
    return (e2x - 1.0) / (e2x + 1.0);
}

/* ====================================================================
 * 4. Exponential and logarithmic functions
 * ==================================================================== */

double exp(double x) {
    /* Handle edge cases */
    if (x != x) return x; /* NaN */
    if (x > 709.0)  return _make_double(0x7FF0000000000000ULL); /* +inf */
    if (x < -745.0) return 0.0;

    /* Argument reduction: x = k * ln(2) + r, where |r| <= ln(2)/2
     * exp(x) = 2^k * exp(r) */
    int k = (int)(x * LOG2E + (x >= 0.0 ? 0.5 : -0.5));
    double r = x - (double)k * LN2;

    /* exp(r) via Taylor series: 1 + r + r^2/2! + r^3/3! + ...
     * 13 terms for |r| <= 0.35, giving ~1e-16 accuracy */
    double term = 1.0;
    double sum  = 1.0;

    term *= r / 1.0;   sum += term;
    term *= r / 2.0;   sum += term;
    term *= r / 3.0;   sum += term;
    term *= r / 4.0;   sum += term;
    term *= r / 5.0;   sum += term;
    term *= r / 6.0;   sum += term;
    term *= r / 7.0;   sum += term;
    term *= r / 8.0;   sum += term;
    term *= r / 9.0;   sum += term;
    term *= r / 10.0;  sum += term;
    term *= r / 11.0;  sum += term;
    term *= r / 12.0;  sum += term;
    term *= r / 13.0;  sum += term;

    /* Multiply by 2^k using bit manipulation */
    double_bits db;
    db.f = sum;
    db.u += (uint64_t)k << 52;
    return db.f;
}

double exp2(double x) {
    return exp(x * LN2);
}

double log(double x) {
    /* Handle edge cases */
    if (x < 0.0)  return _make_double(0x7FF8000000000000ULL); /* NaN */
    if (x == 0.0) return -_make_double(0x7FF0000000000000ULL); /* -inf */
    if (x != x)   return x; /* NaN */

    /* Argument reduction: x = m * 2^e where 1 <= m < 2
     * log(x) = e * ln(2) + log(m) */
    double_bits db;
    db.f = x;
    int e = (int)((db.u >> 52) & 0x7FF) - 1023;
    /* Extract mantissa in [1, 2) */
    db.u = (db.u & 0x000FFFFFFFFFFFFFULL) | 0x3FF0000000000000ULL;
    double m = db.f;

    /* For better convergence, if m > sqrt(2) ~= 1.4142, divide by 2 and adjust */
    if (m > 1.4142135623730950488) {
        m *= 0.5;
        e++;
    }

    /* log(m) using the series for log((1+t)/(1-t)) = 2*(t + t^3/3 + t^5/5 + ...)
     * where t = (m - 1) / (m + 1) */
    double t = (m - 1.0) / (m + 1.0);
    double t2 = t * t;
    double sum = t;
    double power = t;

    /* 20 terms for high accuracy */
    for (int n = 1; n <= 25; n++) {
        power *= t2;
        sum += power / (2.0 * n + 1.0);
        if (fabs(power) < 1e-17) break;
    }
    sum *= 2.0;

    return (double)e * LN2 + sum;
}

double log2(double x) {
    return log(x) / LN2;
}

double log10(double x) {
    return log(x) / LN10;
}

/* ====================================================================
 * 5. Power function
 * ==================================================================== */

double pow(double base, double exponent) {
    if (exponent == 0.0) return 1.0;
    if (base == 0.0) {
        if (exponent > 0.0) return 0.0;
        return _make_double(0x7FF0000000000000ULL); /* +inf for 0^negative */
    }
    if (base == 1.0) return 1.0;

    /* Integer exponent fast path */
    if (exponent == (double)(long long)exponent) {
        long long n = (long long)exponent;
        if (n < 0) {
            base = 1.0 / base;
            n = -n;
        }
        double result = 1.0;
        double b = base;
        while (n > 0) {
            if (n & 1) result *= b;
            b *= b;
            n >>= 1;
        }
        return result;
    }

    /* General case: base^exp = exp(exp * log(base)) */
    if (base < 0.0) {
        /* Negative base with non-integer exponent -> NaN */
        return _make_double(0x7FF8000000000000ULL);
    }
    return exp(exponent * log(base));
}

/* ====================================================================
 * 6. Rounding functions
 * ==================================================================== */

double ceil(double x) {
    long long i = (long long)x;
    if (x > 0.0 && x != (double)i) return (double)(i + 1);
    return (double)i;
}

double floor(double x) {
    long long i = (long long)x;
    if (x < 0.0 && x != (double)i) return (double)(i - 1);
    return (double)i;
}

double round(double x) {
    return (x >= 0.0) ? floor(x + 0.5) : ceil(x - 0.5);
}

double trunc(double x) {
    return (double)(long long)x;
}

/* ====================================================================
 * 7. Remainder / modulo
 * ==================================================================== */

double fmod(double x, double y) {
    if (y == 0.0) return _make_double(0x7FF8000000000000ULL); /* NaN */
    return x - trunc(x / y) * y;
}

double remainder(double x, double y) {
    if (y == 0.0) return _make_double(0x7FF8000000000000ULL);
    double n = round(x / y);
    return x - n * y;
}

/* ====================================================================
 * 8. Decomposition functions
 * ==================================================================== */

double frexp(double x, int *exp) {
    if (x == 0.0) { *exp = 0; return 0.0; }
    double_bits db;
    db.f = x;
    int e = (int)((db.u >> 52) & 0x7FF);
    if (e == 0) {
        /* Subnormal: multiply by 2^64 and try again */
        db.f = x * 18446744073709551616.0; /* 2^64 */
        e = (int)((db.u >> 52) & 0x7FF) - 64;
    }
    *exp = e - 1022;
    /* Set exponent to -1 (biased: 1022) to get mantissa in [0.5, 1.0) */
    db.u = (db.u & 0x800FFFFFFFFFFFFFULL) | 0x3FE0000000000000ULL;
    return db.f;
}

double ldexp(double x, int exp) {
    if (x == 0.0) return 0.0;
    double_bits db;
    db.f = x;
    int e = (int)((db.u >> 52) & 0x7FF);
    e += exp;
    if (e <= 0) return 0.0; /* underflow */
    if (e >= 2047) return (x > 0.0) ?
        _make_double(0x7FF0000000000000ULL) :
        _make_double(0xFFF0000000000000ULL); /* overflow */
    db.u = (db.u & 0x800FFFFFFFFFFFFFULL) | ((uint64_t)e << 52);
    return db.f;
}

double modf(double x, double *iptr) {
    double i = trunc(x);
    *iptr = i;
    return x - i;
}

double copysign(double x, double y) {
    double_bits bx, by;
    bx.f = x;
    by.f = y;
    bx.u = (bx.u & 0x7FFFFFFFFFFFFFFFULL) | (by.u & 0x8000000000000000ULL);
    return bx.f;
}

/* ====================================================================
 * 9. Min / max / misc
 * ==================================================================== */

double fmin(double x, double y) {
    if (x != x) return y; /* x is NaN */
    if (y != y) return x; /* y is NaN */
    return x < y ? x : y;
}

double fmax(double x, double y) {
    if (x != x) return y;
    if (y != y) return x;
    return x > y ? x : y;
}

double hypot(double x, double y) {
    return sqrt(x * x + y * y);
}

double cbrt(double x) {
    if (x == 0.0) return 0.0;
    int neg = (x < 0.0);
    if (neg) x = -x;

    /* Initial guess using pow(x, 1/3) via bit hack */
    double_bits db;
    db.f = x;
    db.u = db.u / 3 + 0x2A9F7893E4FE0000ULL;
    double guess = db.f;

    /* Halley's method (converges cubically) */
    for (int i = 0; i < 6; i++) {
        double g3 = guess * guess * guess;
        guess = guess * (g3 + 2.0 * x) / (2.0 * g3 + x);
    }
    return neg ? -guess : guess;
}

/* ====================================================================
 * 10. Classification functions
 * ==================================================================== */

int __fpclassify(double x) {
    double_bits db;
    db.f = x;
    uint64_t exp_bits = (db.u >> 52) & 0x7FF;
    uint64_t frac_bits = db.u & 0x000FFFFFFFFFFFFFULL;

    if (exp_bits == 0) {
        return (frac_bits == 0) ? FP_ZERO : FP_SUBNORMAL;
    }
    if (exp_bits == 0x7FF) {
        return (frac_bits == 0) ? FP_INFINITE : FP_NAN;
    }
    return FP_NORMAL;
}

int __isnan(double x) {
    double_bits db;
    db.f = x;
    uint64_t exp_bits = (db.u >> 52) & 0x7FF;
    uint64_t frac_bits = db.u & 0x000FFFFFFFFFFFFFULL;
    return (exp_bits == 0x7FF && frac_bits != 0);
}

int __isinf(double x) {
    double_bits db;
    db.f = x;
    uint64_t exp_bits = (db.u >> 52) & 0x7FF;
    uint64_t frac_bits = db.u & 0x000FFFFFFFFFFFFFULL;
    return (exp_bits == 0x7FF && frac_bits == 0);
}

/* ====================================================================
 * 11. Float (32-bit) variants -- delegate to double versions
 * ==================================================================== */

float sinf(float x)                  { return (float)sin((double)x); }
float cosf(float x)                  { return (float)cos((double)x); }
float tanf(float x)                  { return (float)tan((double)x); }
float asinf(float x)                 { return (float)asin((double)x); }
float acosf(float x)                 { return (float)acos((double)x); }
float atanf(float x)                 { return (float)atan((double)x); }
float atan2f(float y, float x)       { return (float)atan2((double)y, (double)x); }
float sinhf(float x)                 { return (float)sinh((double)x); }
float coshf(float x)                 { return (float)cosh((double)x); }
float tanhf(float x)                 { return (float)tanh((double)x); }
float logf(float x)                  { return (float)log((double)x); }
float log2f(float x)                 { return (float)log2((double)x); }
float log10f(float x)                { return (float)log10((double)x); }
float expf(float x)                  { return (float)exp((double)x); }
float exp2f(float x)                 { return (float)exp2((double)x); }
float powf(float x, float y)         { return (float)pow((double)x, (double)y); }
float ceilf(float x)                 { return (float)ceil((double)x); }
float floorf(float x)                { return (float)floor((double)x); }
float roundf(float x)                { return (float)round((double)x); }
float truncf(float x)                { return (float)trunc((double)x); }
float fmodf(float x, float y)        { return (float)fmod((double)x, (double)y); }
float remainderf(float x, float y)   { return (float)remainder((double)x, (double)y); }

float frexpf(float x, int *exp) {
    double d = frexp((double)x, exp);
    return (float)d;
}

float ldexpf(float x, int exp) {
    return (float)ldexp((double)x, exp);
}

float modff(float x, float *iptr) {
    double di;
    double result = modf((double)x, &di);
    *iptr = (float)di;
    return (float)result;
}

float copysignf(float x, float y) {
    float_bits bx, by;
    bx.f = x;
    by.f = y;
    bx.u = (bx.u & 0x7FFFFFFFU) | (by.u & 0x80000000U);
    return bx.f;
}

float fminf(float x, float y) { return (float)fmin((double)x, (double)y); }
float fmaxf(float x, float y) { return (float)fmax((double)x, (double)y); }
float hypotf(float x, float y) { return (float)hypot((double)x, (double)y); }
float cbrtf(float x)           { return (float)cbrt((double)x); }
