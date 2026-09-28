/*
 * Soft-float compiler-rt builtins for the SimpleOS freestanding targets.
 *
 * Why this file exists: on aarch64-unknown-simpleos and riscv64-unknown-simpleos
 * `long double` is IEEE-754 binary128, so an ordinary `(long double)some_double`
 * cast -- e.g. `strtold()` in simpleos_libc_ext.c, which is defined as
 * `(long double)strtod(...)` -- makes the compiler emit a call to the
 * compiler-rt builtin `__extenddftf2`. Neither arch has hardware quad-precision,
 * and these are freestanding targets with no compiler-rt / libgcc available:
 * `find_compiler_rt_builtins()` shells out to `cc -print-libgcc-file-name` for
 * `aarch64-none-elf` / `riscv64-unknown-elf` and gets nothing back. The symbol
 * was therefore the last undefined name on the SimpleOS link after the
 * simple-core archive and the C runtime were put on the link line -- see
 * doc/08_tracking/bug/simpleos_target_build_link_omits_simple_core_archive_2026-08-24.md
 *
 * binary64 -> binary128 is always EXACT: binary128 has both a wider exponent
 * range (15-bit, bias 16383) and a wider significand (112 stored bits vs 52), so
 * every finite double -- including every binary64 subnormal, which becomes a
 * normal binary128 -- maps with no rounding and no overflow. That makes this a
 * pure bit-manipulation routine with no rounding mode to honour.
 */

#include <stdint.h>

/*
 * Guarded on the actual `long double` format rather than on the architecture:
 * where long double is not binary128 (x86_64's 80-bit extended, or targets
 * where long double == double) the compiler does not emit __extenddftf2 at all,
 * and defining it would be both unnecessary and wrong.
 */
#if defined(__LDBL_MANT_DIG__) && __LDBL_MANT_DIG__ == 113

#define SPL_F64_MANT_BITS 52
#define SPL_F64_EXP_MASK 0x7FFu
#define SPL_F64_EXP_BIAS 1023
#define SPL_F128_MANT_BITS 112
#define SPL_F128_EXP_BIAS 16383
#define SPL_F128_EXP_MAX 0x7FFFu

typedef unsigned __int128 spl_u128;

long double __extenddftf2(double a);

long double __extenddftf2(double a) {
    uint64_t bits;
    __builtin_memcpy(&bits, &a, sizeof(bits));

    const uint64_t sign = bits >> 63;
    uint32_t exponent = (uint32_t)((bits >> SPL_F64_MANT_BITS) & SPL_F64_EXP_MASK);
    uint64_t mantissa = bits & (((uint64_t)1 << SPL_F64_MANT_BITS) - 1);

    /* Widening the significand is a constant left shift: 112 - 52 == 60. */
    spl_u128 out_mantissa = (spl_u128)mantissa << (SPL_F128_MANT_BITS - SPL_F64_MANT_BITS);
    uint32_t out_exponent;

    if (exponent == SPL_F64_EXP_MASK) {
        /* Inf or NaN. Shifting the payload left by 60 keeps the is-quiet bit
         * (the significand MSB) as the MSB, so quiet and signalling NaNs stay
         * distinct and the payload is preserved. */
        out_exponent = SPL_F128_EXP_MAX;
    } else if (exponent == 0 && mantissa == 0) {
        /* Signed zero. */
        out_exponent = 0;
        out_mantissa = 0;
    } else if (exponent == 0) {
        /* binary64 subnormal -- representable as a NORMAL binary128, because
         * binary128's exponent range is far wider. Normalize by shifting the
         * significand left until the implicit leading 1 is in place, debiting
         * the exponent for each shift. */
        int shift = 0;
        while ((mantissa & ((uint64_t)1 << SPL_F64_MANT_BITS)) == 0) {
            mantissa <<= 1;
            shift++;
        }
        /* Drop the now-explicit leading bit; it is implicit in binary128 too. */
        mantissa &= ((uint64_t)1 << SPL_F64_MANT_BITS) - 1;
        out_mantissa = (spl_u128)mantissa << (SPL_F128_MANT_BITS - SPL_F64_MANT_BITS);
        /* A binary64 subnormal has unbiased exponent 1 - 1023, less one per
         * normalization shift. */
        out_exponent = (uint32_t)(SPL_F128_EXP_BIAS - SPL_F64_EXP_BIAS + 1 - shift);
    } else {
        /* Normal: rebias only. */
        out_exponent = exponent - SPL_F64_EXP_BIAS + SPL_F128_EXP_BIAS;
    }

    spl_u128 out = ((spl_u128)sign << 127) | ((spl_u128)out_exponent << SPL_F128_MANT_BITS) | out_mantissa;

    long double result;
    __builtin_memcpy(&result, &out, sizeof(result));
    return result;
}

#else

/* Keep this a valid, non-empty translation unit on targets that do not need the
 * builtin (ISO C forbids an empty translation unit). */
typedef int spl_softfloat_builtins_not_needed;

#endif /* __LDBL_MANT_DIG__ == 113 */
