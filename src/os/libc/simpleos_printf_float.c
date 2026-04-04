/*
 * SimpleOS Libc Shim -- Float formatting for printf
 *
 * Provides _fmt_float() which is called from simpleos_libc.c's vsnprintf
 * for %f, %e, %g, %E, %G format specifiers.
 *
 * This is a separate file to keep the main libc lean when float formatting
 * is not needed.
 */

#include "include/math.h"
#include "include/string.h"
#include <stddef.h>

/* ====================================================================
 * Internal: format a double into a buffer
 *
 * Returns number of characters written (excluding NUL).
 * Respects max (will not write beyond buf[max-1]).
 * ==================================================================== */

/* Helper: write a character if there's room */
static int _fput(char *buf, size_t max, size_t pos, char c) {
    if (pos < max) buf[pos] = c;
    return 1;
}

/* Helper: write a string */
static size_t _fputs(char *buf, size_t max, size_t pos, const char *s) {
    size_t n = 0;
    while (*s) {
        if (pos + n < max) buf[pos + n] = *s;
        s++;
        n++;
    }
    return n;
}

/* Helper: write an unsigned integer (for the integer part) */
static size_t _fput_uint(char *buf, size_t max, size_t pos, unsigned long long val) {
    char tmp[24];
    int len = 0;
    if (val == 0) {
        tmp[len++] = '0';
    } else {
        while (val > 0) {
            tmp[len++] = '0' + (char)(val % 10);
            val /= 10;
        }
    }
    /* Reverse and write */
    size_t n = 0;
    for (int i = len - 1; i >= 0; i--) {
        if (pos + n < max) buf[pos + n] = tmp[i];
        n++;
    }
    return n;
}

/* Helper: round half-up and format digits for the fractional part */
static size_t _fput_frac(char *buf, size_t max, size_t pos, double frac, int prec) {
    size_t n = 0;
    for (int i = 0; i < prec; i++) {
        frac *= 10.0;
        int digit = (int)frac;
        if (digit > 9) digit = 9;
        if (pos + n < max) buf[pos + n] = '0' + (char)digit;
        n++;
        frac -= (double)digit;
    }
    return n;
}

/* Round `val` to `prec` decimal places and decompose into integer + fractional */
static void _decompose(double val, int prec, unsigned long long *int_part,
                        double *frac_part) {
    /* Compute rounding factor: 0.5 * 10^(-prec) */
    double round_add = 0.5;
    for (int i = 0; i < prec; i++) round_add *= 0.1;
    val += round_add;

    *int_part = (unsigned long long)val;
    *frac_part = val - (double)(*int_part);
}

/* Count digits in integer */
static int _count_digits(unsigned long long val) {
    if (val == 0) return 1;
    int n = 0;
    while (val > 0) { n++; val /= 10; }
    return n;
}

/* ====================================================================
 * _fmt_float -- main entry point
 *
 * spec: 'f', 'e', 'E', 'g', 'G'
 * width: minimum field width (0 = no minimum)
 * prec: precision (number of digits after decimal, -1 = default 6)
 *
 * Returns: number of characters that would be written (like snprintf)
 * ==================================================================== */

int _fmt_float(char *buf, size_t max, double val, char spec, int width, int prec) {
    size_t pos = 0;
    int is_upper = (spec == 'E' || spec == 'G');

    if (prec < 0) prec = 6;

    /* Handle special values: NaN, Inf, -Inf */
    /* NaN check: val != val */
    if (val != val) {
        pos += _fputs(buf, max, pos, is_upper ? "NAN" : "nan");
        goto pad_and_done;
    }

    /* Infinity check via comparison */
    if (val > 1e308) {
        pos += _fputs(buf, max, pos, is_upper ? "INF" : "inf");
        goto pad_and_done;
    }
    if (val < -1e308) {
        pos += _fput(buf, max, pos, '-');
        pos += _fputs(buf, max, pos, is_upper ? "INF" : "inf");
        goto pad_and_done;
    }

    /* Handle sign */
    int negative = 0;
    if (val < 0.0) {
        negative = 1;
        val = -val;
    }

    /* %g / %G: choose between %f and %e */
    if (spec == 'g' || spec == 'G') {
        int g_prec = (prec == 0) ? 1 : prec;
        /* Determine exponent */
        int exp_val = 0;
        if (val != 0.0) {
            double tmp = val;
            while (tmp >= 10.0) { tmp /= 10.0; exp_val++; }
            while (tmp < 1.0 && tmp > 0.0) { tmp *= 10.0; exp_val--; }
        }
        if (exp_val < -4 || exp_val >= g_prec) {
            spec = is_upper ? 'E' : 'e';
            prec = g_prec - 1;
        } else {
            spec = 'f';
            prec = g_prec - 1 - exp_val;
            if (prec < 0) prec = 0;
        }
    }

    if (spec == 'f') {
        /* Fixed-point format */
        if (negative) pos += _fput(buf, max, pos, '-');

        unsigned long long int_part;
        double frac_part;
        _decompose(val, prec, &int_part, &frac_part);

        pos += _fput_uint(buf, max, pos, int_part);
        if (prec > 0) {
            pos += _fput(buf, max, pos, '.');
            pos += _fput_frac(buf, max, pos, frac_part, prec);
        }
    } else {
        /* Scientific notation: %e / %E */
        if (negative) pos += _fput(buf, max, pos, '-');

        int exp_val = 0;
        if (val == 0.0) {
            exp_val = 0;
        } else {
            while (val >= 10.0) { val /= 10.0; exp_val++; }
            while (val < 1.0 && val > 0.0) { val *= 10.0; exp_val--; }
        }

        /* val is now in [1.0, 10.0) or 0.0 */
        unsigned long long int_part;
        double frac_part;
        _decompose(val, prec, &int_part, &frac_part);

        /* If rounding pushed int_part to 10, adjust */
        if (int_part >= 10) {
            int_part = 1;
            frac_part = 0.0;
            exp_val++;
        }

        pos += _fput_uint(buf, max, pos, int_part);
        if (prec > 0) {
            pos += _fput(buf, max, pos, '.');
            pos += _fput_frac(buf, max, pos, frac_part, prec);
        }

        /* Exponent */
        pos += _fput(buf, max, pos, is_upper ? 'E' : 'e');
        pos += _fput(buf, max, pos, (exp_val >= 0) ? '+' : '-');
        if (exp_val < 0) exp_val = -exp_val;
        if (exp_val < 10) pos += _fput(buf, max, pos, '0');
        pos += _fput_uint(buf, max, pos, (unsigned long long)exp_val);
    }

pad_and_done:
    /* Right-pad with spaces if width > pos (left-aligned not handled here;
     * the caller in vsnprintf handles width/alignment) */
    (void)width; /* width padding is handled by the vsnprintf caller */

    /* Null-terminate */
    if (pos < max)
        buf[pos] = '\0';
    else if (max > 0)
        buf[max - 1] = '\0';

    return (int)pos;
}
