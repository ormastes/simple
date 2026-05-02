/*
 * SimpleOS Libc Shim — Extended stdlib: number parsing, sorting, search
 *
 * strtol/strtoul/strtoll/strtoull — full base-0/8/10/16 support
 * strtod/strtof — integer.fraction and scientific notation
 * qsort — quicksort with insertion-sort fallback for small partitions
 * bsearch, abs/labs/llabs, div/ldiv/lldiv, rand/srand
 */

#include "include/stdlib.h"
#include "include/errno.h"
#include "include/limits.h"
#include "include/string.h"

extern int errno;

/* ====================================================================
 * 1. Integer parsing — strtol family
 * ==================================================================== */

/* Helper: is whitespace */
static int _is_space(char c) {
    return c == ' ' || c == '\t' || c == '\n' ||
           c == '\r' || c == '\f' || c == '\v';
}

/* Helper: digit value for a given base, -1 if invalid */
static int _digit_val(char c, int base) {
    int v;
    if (c >= '0' && c <= '9')      v = c - '0';
    else if (c >= 'a' && c <= 'z') v = c - 'a' + 10;
    else if (c >= 'A' && c <= 'Z') v = c - 'A' + 10;
    else return -1;
    return (v < base) ? v : -1;
}

long strtol(const char *nptr, char **endptr, int base) {
    const char *s = nptr;
    int neg = 0;
    long result = 0;
    int any = 0;

    /* Skip whitespace */
    while (_is_space(*s)) s++;

    /* Sign */
    if (*s == '-') { neg = 1; s++; }
    else if (*s == '+') { s++; }

    /* Base detection */
    if (base == 0) {
        if (*s == '0') {
            s++;
            if (*s == 'x' || *s == 'X') { base = 16; s++; }
            else { base = 8; }
        } else {
            base = 10;
        }
    } else if (base == 16) {
        if (*s == '0' && (s[1] == 'x' || s[1] == 'X')) s += 2;
    }

    /* Accumulate digits */
    long cutoff = neg ? -(LONG_MIN / base) : LONG_MAX / base;
    int cutlim = (int)(neg ? -(LONG_MIN % base) : LONG_MAX % base);
    int overflow = 0;

    while (1) {
        int d = _digit_val(*s, base);
        if (d < 0) break;
        any = 1;
        if (overflow || result > cutoff || (result == cutoff && d > cutlim)) {
            overflow = 1;
        } else {
            result = result * base + d;
        }
        s++;
    }

    if (endptr) *endptr = (char *)(any ? s : nptr);

    if (overflow) {
        errno = ERANGE;
        return neg ? LONG_MIN : LONG_MAX;
    }

    return neg ? -result : result;
}

unsigned long strtoul(const char *nptr, char **endptr, int base) {
    const char *s = nptr;
    unsigned long result = 0;
    int any = 0;

    while (_is_space(*s)) s++;

    /* Optional sign (unsigned, but strtoul accepts leading +/-) */
    int neg = 0;
    if (*s == '-') { neg = 1; s++; }
    else if (*s == '+') { s++; }

    /* Base detection */
    if (base == 0) {
        if (*s == '0') {
            s++;
            if (*s == 'x' || *s == 'X') { base = 16; s++; }
            else { base = 8; }
        } else {
            base = 10;
        }
    } else if (base == 16) {
        if (*s == '0' && (s[1] == 'x' || s[1] == 'X')) s += 2;
    }

    unsigned long cutoff = ULONG_MAX / (unsigned long)base;
    int cutlim = (int)(ULONG_MAX % (unsigned long)base);
    int overflow = 0;

    while (1) {
        int d = _digit_val(*s, base);
        if (d < 0) break;
        any = 1;
        if (overflow || result > cutoff || (result == cutoff && d > cutlim)) {
            overflow = 1;
        } else {
            result = result * base + d;
        }
        s++;
    }

    if (endptr) *endptr = (char *)(any ? s : nptr);

    if (overflow) {
        errno = ERANGE;
        return ULONG_MAX;
    }

    return neg ? (unsigned long)(-(long)result) : result;
}

long long strtoll(const char *nptr, char **endptr, int base) {
    const char *s = nptr;
    int neg = 0;
    long long result = 0;
    int any = 0;

    while (_is_space(*s)) s++;

    if (*s == '-') { neg = 1; s++; }
    else if (*s == '+') { s++; }

    if (base == 0) {
        if (*s == '0') {
            s++;
            if (*s == 'x' || *s == 'X') { base = 16; s++; }
            else { base = 8; }
        } else {
            base = 10;
        }
    } else if (base == 16) {
        if (*s == '0' && (s[1] == 'x' || s[1] == 'X')) s += 2;
    }

    long long cutoff = neg ? -(LLONG_MIN / base) : LLONG_MAX / base;
    int cutlim = (int)(neg ? -(LLONG_MIN % base) : LLONG_MAX % base);
    int overflow = 0;

    while (1) {
        int d = _digit_val(*s, base);
        if (d < 0) break;
        any = 1;
        if (overflow || result > cutoff || (result == cutoff && d > cutlim)) {
            overflow = 1;
        } else {
            result = result * base + d;
        }
        s++;
    }

    if (endptr) *endptr = (char *)(any ? s : nptr);

    if (overflow) {
        errno = ERANGE;
        return neg ? LLONG_MIN : LLONG_MAX;
    }

    return neg ? -result : result;
}

unsigned long long strtoull(const char *nptr, char **endptr, int base) {
    const char *s = nptr;
    unsigned long long result = 0;
    int any = 0;

    while (_is_space(*s)) s++;

    int neg = 0;
    if (*s == '-') { neg = 1; s++; }
    else if (*s == '+') { s++; }

    if (base == 0) {
        if (*s == '0') {
            s++;
            if (*s == 'x' || *s == 'X') { base = 16; s++; }
            else { base = 8; }
        } else {
            base = 10;
        }
    } else if (base == 16) {
        if (*s == '0' && (s[1] == 'x' || s[1] == 'X')) s += 2;
    }

    unsigned long long cutoff = ULLONG_MAX / (unsigned long long)base;
    int cutlim = (int)(ULLONG_MAX % (unsigned long long)base);
    int overflow = 0;

    while (1) {
        int d = _digit_val(*s, base);
        if (d < 0) break;
        any = 1;
        if (overflow || result > cutoff || (result == cutoff && d > cutlim)) {
            overflow = 1;
        } else {
            result = result * base + d;
        }
        s++;
    }

    if (endptr) *endptr = (char *)(any ? s : nptr);

    if (overflow) {
        errno = ERANGE;
        return ULLONG_MAX;
    }

    return neg ? (unsigned long long)(-(long long)result) : result;
}

/* ====================================================================
 * 2. Floating-point parsing — strtod / strtof
 * ==================================================================== */

double strtod(const char *nptr, char **endptr) {
    const char *s = nptr;

    /* Skip whitespace */
    while (_is_space(*s)) s++;

    /* Sign */
    int neg = 0;
    if (*s == '-') { neg = 1; s++; }
    else if (*s == '+') { s++; }

    /* Integer part */
    double result = 0.0;
    int any = 0;
    while (*s >= '0' && *s <= '9') {
        result = result * 10.0 + (*s - '0');
        any = 1;
        s++;
    }

    /* Fractional part */
    if (*s == '.') {
        s++;
        double frac = 0.1;
        while (*s >= '0' && *s <= '9') {
            result += (*s - '0') * frac;
            frac *= 0.1;
            any = 1;
            s++;
        }
    }

    if (!any) {
        if (endptr) *endptr = (char *)nptr;
        return 0.0;
    }

    /* Exponent: e/E [+/-] digits */
    if (*s == 'e' || *s == 'E') {
        const char *e_start = s;
        s++;
        int eneg = 0;
        if (*s == '-') { eneg = 1; s++; }
        else if (*s == '+') { s++; }

        int exp = 0;
        int eany = 0;
        while (*s >= '0' && *s <= '9') {
            exp = exp * 10 + (*s - '0');
            eany = 1;
            s++;
        }

        if (!eany) {
            /* No digits after 'e' — rewind */
            s = e_start;
        } else {
            /* Apply exponent via repeated multiply/divide */
            double scale = 1.0;
            while (exp >= 8)  { scale *= 1e8;  exp -= 8; }
            while (exp >= 1)  { scale *= 10.0; exp -= 1; }
            if (eneg) result /= scale;
            else      result *= scale;
        }
    }

    if (endptr) *endptr = (char *)s;
    return neg ? -result : result;
}

float strtof(const char *nptr, char **endptr) {
    return (float)strtod(nptr, endptr);
}

/* ====================================================================
 * 3. Convenience wrappers
 * ==================================================================== */

int       atoi(const char *nptr)  { return (int)strtol(nptr, NULL, 10); }
long      atol(const char *nptr)  { return strtol(nptr, NULL, 10); }
long long atoll(const char *nptr) { return strtoll(nptr, NULL, 10); }

/* ====================================================================
 * 4. Sorting — qsort (quicksort + insertion sort for small partitions)
 * ==================================================================== */

/* Swap size bytes between a and b using a stack buffer */
static void _swap(char *a, char *b, size_t size) {
    char tmp[256];
    if (size <= sizeof(tmp)) {
        memcpy(tmp, a, size);
        memcpy(a, b, size);
        memcpy(b, tmp, size);
    } else {
        /* Large elements: byte-by-byte */
        for (size_t i = 0; i < size; i++) {
            char t = a[i];
            a[i] = b[i];
            b[i] = t;
        }
    }
}

/* Insertion sort for small partitions */
static void _insertion_sort(char *base, size_t nmemb, size_t size,
                            int (*compar)(const void *, const void *)) {
    for (size_t i = 1; i < nmemb; i++) {
        size_t j = i;
        while (j > 0 && compar(base + j * size, base + (j - 1) * size) < 0) {
            _swap(base + j * size, base + (j - 1) * size, size);
            j--;
        }
    }
}

/* Median-of-three: return index of median among lo, mid, hi */
static size_t _median3(char *base, size_t lo, size_t mid, size_t hi,
                       size_t size,
                       int (*compar)(const void *, const void *)) {
    char *a = base + lo * size;
    char *b = base + mid * size;
    char *c = base + hi * size;
    if (compar(a, b) < 0) {
        if (compar(b, c) < 0) return mid;
        else if (compar(a, c) < 0) return hi;
        else return lo;
    } else {
        if (compar(a, c) < 0) return lo;
        else if (compar(b, c) < 0) return hi;
        else return mid;
    }
}

static void _qsort_impl(char *base, size_t lo, size_t hi, size_t size,
                         int (*compar)(const void *, const void *)) {
    while (lo < hi) {
        size_t n = hi - lo + 1;

        /* Insertion sort for small partitions */
        if (n <= 16) {
            _insertion_sort(base + lo * size, n, size, compar);
            return;
        }

        /* Median-of-three pivot selection */
        size_t mid = lo + n / 2;
        size_t pivot_idx = _median3(base, lo, mid, hi, size, compar);
        _swap(base + pivot_idx * size, base + hi * size, size);
        char *pivot = base + hi * size;

        /* Partition (Lomuto scheme) */
        size_t i = lo;
        for (size_t j = lo; j < hi; j++) {
            if (compar(base + j * size, pivot) <= 0) {
                _swap(base + i * size, base + j * size, size);
                i++;
            }
        }
        _swap(base + i * size, base + hi * size, size);

        /* Recurse on the smaller partition, loop on the larger (tail-call opt) */
        size_t left_size = (i > lo) ? i - 1 - lo : 0;
        size_t right_size = (hi > i) ? hi - i - 1 : 0;

        if (left_size < right_size) {
            if (i > lo + 1)
                _qsort_impl(base, lo, i - 1, size, compar);
            lo = i + 1;
        } else {
            if (i + 1 < hi)
                _qsort_impl(base, i + 1, hi, size, compar);
            if (i == 0) return;
            hi = i - 1;
        }
    }
}

void qsort(void *base, size_t nmemb, size_t size,
           int (*compar)(const void *, const void *)) {
    if (nmemb < 2 || size == 0) return;
    _qsort_impl((char *)base, 0, nmemb - 1, size, compar);
}

/* ====================================================================
 * 5. Binary search
 * ==================================================================== */

void *bsearch(const void *key, const void *base, size_t nmemb, size_t size,
              int (*compar)(const void *, const void *)) {
    const char *b = (const char *)base;
    size_t lo = 0, hi = nmemb;
    while (lo < hi) {
        size_t mid = lo + (hi - lo) / 2;
        int cmp = compar(key, b + mid * size);
        if (cmp == 0) return (void *)(b + mid * size);
        if (cmp < 0) hi = mid;
        else lo = mid + 1;
    }
    return NULL;
}

/* ====================================================================
 * 6. Integer arithmetic
 * ==================================================================== */

int       abs(int j)       { return j < 0 ? -j : j; }
long      labs(long j)     { return j < 0 ? -j : j; }
long long llabs(long long j) { return j < 0 ? -j : j; }

div_t div(int numer, int denom) {
    div_t r;
    r.quot = numer / denom;
    r.rem  = numer % denom;
    return r;
}

ldiv_t ldiv(long numer, long denom) {
    ldiv_t r;
    r.quot = numer / denom;
    r.rem  = numer % denom;
    return r;
}

lldiv_t lldiv(long long numer, long long denom) {
    lldiv_t r;
    r.quot = numer / denom;
    r.rem  = numer % denom;
    return r;
}

/* ====================================================================
 * 7. Pseudo-random number generator (LCG)
 * ==================================================================== */

static unsigned int _rand_state = 1;

int rand(void) {
    _rand_state = _rand_state * 1103515245 + 12345;
    return (int)((_rand_state >> 16) & 0x7fff);
}

void srand(unsigned int seed) {
    _rand_state = seed;
}
