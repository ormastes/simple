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

static unsigned int sqrt_mul32(unsigned int a, unsigned int b) {
    return (unsigned int)(((unsigned long long)a * b) >> 32);
}

static unsigned long long sqrt_mul64(unsigned long long a,
                                     unsigned long long b) {
    unsigned long long ahi = a >> 32, alo = a & 0xffffffffULL;
    unsigned long long bhi = b >> 32, blo = b & 0xffffffffULL;
    return ahi * bhi + ((ahi * blo) >> 32) + ((alo * bhi) >> 32);
}

static const unsigned short sqrt_rsqrt_tab[128] = {
    0xb451,0xb2f0,0xb196,0xb044,0xaef9,0xadb6,0xac79,0xab43,
    0xaa14,0xa8eb,0xa7c8,0xa6aa,0xa592,0xa480,0xa373,0xa26b,
    0xa168,0xa06a,0x9f70,0x9e7b,0x9d8a,0x9c9d,0x9bb5,0x9ad1,
    0x99f0,0x9913,0x983a,0x9765,0x9693,0x95c4,0x94f8,0x9430,
    0x936b,0x92a9,0x91ea,0x912e,0x9075,0x8fbe,0x8f0a,0x8e59,
    0x8daa,0x8cfe,0x8c54,0x8bac,0x8b07,0x8a64,0x89c4,0x8925,
    0x8889,0x87ee,0x8756,0x86c0,0x862b,0x8599,0x8508,0x8479,
    0x83ec,0x8361,0x82d8,0x8250,0x81c9,0x8145,0x80c2,0x8040,
    0xff02,0xfd0e,0xfb25,0xf947,0xf773,0xf5aa,0xf3ea,0xf234,
    0xf087,0xeee3,0xed47,0xebb3,0xea27,0xe8a3,0xe727,0xe5b2,
    0xe443,0xe2dc,0xe17a,0xe020,0xdecb,0xdd7d,0xdc34,0xdaf1,
    0xd9b3,0xd87b,0xd748,0xd61a,0xd4f1,0xd3cd,0xd2ad,0xd192,
    0xd07b,0xcf69,0xce5b,0xcd51,0xcc4a,0xcb48,0xca4a,0xc94f,
    0xc858,0xc764,0xc674,0xc587,0xc49d,0xc3b7,0xc2d4,0xc1f4,
    0xc116,0xc03c,0xbf65,0xbe90,0xbdbe,0xbcef,0xbc23,0xbb59,
    0xba91,0xb9cc,0xb90a,0xb84a,0xb78c,0xb6d0,0xb617,0xb560
};

double sqrt(double x) {
    union { double f; unsigned long long u; } rep = { x };
    unsigned long long ix = rep.u;
    if (x != x) {
        rep.u |= 0x0008000000000000ULL;
        return rep.f;
    }
    if (x < 0.0) return __builtin_nan("");
    /* Preserve signed zero and avoid turning positive infinity into NaN in
     * the Newton step (inf / inf).  Both builtins are freestanding constants. */
    if (x == 0.0 || x == __builtin_inf()) return x;

    /* Correctly rounded round-to-nearest binary64 core adapted from musl.
     * Normalize subnormals before fixed-point Goldschmidt iterations. */
    unsigned long long top = ix >> 52;
    if (top == 0) {
        rep.f = x * 0x1p52;
        ix = rep.u;
        top = (ix >> 52) - 52;
    }
    int even = (int)(top & 1);
    unsigned long long m = (ix << 11) | 0x8000000000000000ULL;
    if (even) m >>= 1;
    top = (top + 0x3ff) >> 1;

    const unsigned long long three = 0xc0000000ULL;
    unsigned long long i = (ix >> 46) % 128;
    unsigned long long r = (unsigned int)sqrt_rsqrt_tab[i] << 16;
    unsigned long long s = sqrt_mul32((unsigned int)(m >> 32), (unsigned int)r);
    unsigned long long d = sqrt_mul32((unsigned int)s, (unsigned int)r);
    unsigned long long u = three - d;
    r = (unsigned long long)sqrt_mul32((unsigned int)r, (unsigned int)u) << 1;
    s = (unsigned long long)sqrt_mul32((unsigned int)s, (unsigned int)u) << 1;
    d = sqrt_mul32((unsigned int)s, (unsigned int)r);
    u = three - d;
    r = (unsigned long long)sqrt_mul32((unsigned int)r, (unsigned int)u) << 1;
    r <<= 32;
    s = sqrt_mul64(m, r);
    d = sqrt_mul64(s, r);
    u = (three << 32) - d;
    s = sqrt_mul64(s, u);
    s = (s - 2) >> 9;

    unsigned long long d0 = (m << 42) - s * s;
    unsigned long long d1 = s - d0;
    s += d1 >> 63;
    s &= 0x000fffffffffffffULL;
    s |= top << 52;
    rep.u = s;
    return rep.f;
}

float sqrtf(float x) {
    return (float)sqrt((double)x);
}

/* Bit-preserving inverse of spl_f64_to_bits for the pure-Simple runtime.
 * A union avoids a libc memcpy dependency in the freestanding archive. */
double spl_bits_to_f64(long long bits) {
    union { long long bits; double value; } cast;
    cast.bits = bits;
    return cast.value;
}
