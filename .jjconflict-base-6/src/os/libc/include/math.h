/*
 * SimpleOS <math.h> — mathematical functions
 */

#ifndef _SIMPLEOS_MATH_H
#define _SIMPLEOS_MATH_H

#ifdef __cplusplus
extern "C" {
#endif

/* Mathematical constants */
#define M_PI      3.14159265358979323846
#define M_PI_2    1.57079632679489661923
#define M_PI_4    0.78539816339744830962
#define M_E       2.71828182845904523536
#define M_LN2     0.69314718055994530942
#define M_LN10    2.30258509299404568402
#define M_LOG2E   1.44269504088896340736
#define M_LOG10E  0.43429448190325182765
#define M_SQRT2   1.41421356237309504880
#define M_1_PI    0.31830988618379067154
#define M_2_PI    0.63661977236758134308

/* Special values */
#define HUGE_VAL  __builtin_huge_val()
#define HUGE_VALF __builtin_huge_valf()
#define INFINITY  __builtin_inff()
#define NAN       __builtin_nanf("")

/* Classification */
#define FP_NAN       0
#define FP_INFINITE  1
#define FP_ZERO      2
#define FP_SUBNORMAL 3
#define FP_NORMAL    4

#define fpclassify(x) __builtin_fpclassify(FP_NAN, FP_INFINITE, FP_NORMAL, FP_SUBNORMAL, FP_ZERO, (x))
#define isnan(x)      __builtin_isnan(x)
#define isinf(x)      __builtin_isinf(x)
#define isfinite(x)   __builtin_isfinite(x)
#define isnormal(x)   __builtin_isnormal(x)
#define signbit(x)    __builtin_signbit(x)

/* double functions */
double fabs(double x);
double sqrt(double x);
double cbrt(double x);
double sin(double x);
double cos(double x);
double tan(double x);
double asin(double x);
double acos(double x);
double atan(double x);
double atan2(double y, double x);
double sinh(double x);
double cosh(double x);
double tanh(double x);
double log(double x);
double log2(double x);
double log10(double x);
double exp(double x);
double exp2(double x);
double pow(double x, double y);
double ceil(double x);
double floor(double x);
double round(double x);
double trunc(double x);
double fmod(double x, double y);
double remainder(double x, double y);
double frexp(double x, int *exp);
double ldexp(double x, int exp);
double modf(double x, double *iptr);
double copysign(double x, double y);
double fmin(double x, double y);
double fmax(double x, double y);
double hypot(double x, double y);

/* Near-zero accurate variants */
double log1p(double x);
double expm1(double x);

/* Scale by power of 2 */
double scalbn(double x, int n);

/* float functions */
float fabsf(float x);
float sqrtf(float x);
float cbrtf(float x);
float sinf(float x);
float cosf(float x);
float tanf(float x);
float asinf(float x);
float acosf(float x);
float atanf(float x);
float atan2f(float y, float x);
float sinhf(float x);
float coshf(float x);
float tanhf(float x);
float logf(float x);
float log2f(float x);
float log10f(float x);
float expf(float x);
float exp2f(float x);
float powf(float x, float y);
float ceilf(float x);
float floorf(float x);
float roundf(float x);
float truncf(float x);
float fmodf(float x, float y);
float remainderf(float x, float y);
float frexpf(float x, int *exp);
float ldexpf(float x, int exp);
float modff(float x, float *iptr);
float copysignf(float x, float y);
float fminf(float x, float y);
float fmaxf(float x, float y);
float hypotf(float x, float y);

/* float near-zero variants */
float log1pf(float x);
float expm1f(float x);

/* float scale by power of 2 */
float scalbnf(float x, int n);

#ifdef __cplusplus
}
#endif

#endif /* _SIMPLEOS_MATH_H */
