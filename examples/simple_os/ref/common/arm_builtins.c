/*
 * SimpleOS — L4 Microkernel Reference Implementation
 * common/arm_builtins.c — ARM EABI compiler runtime builtins
 *
 * Provides division, modulo, and memory routines that clang emits calls to
 * on ARM32 targets.  These are normally supplied by libgcc / compiler-rt,
 * but we are freestanding (-nostdlib -nostdinc).
 *
 * Guarded with __ARM_EABI__ so this file is harmless on non-ARM builds.
 */

#include "common/types.h"

#ifdef __ARM_EABI__

/* ── ARM EABI division routines ─────────────────────────────────────── */

typedef struct { uint32_t quot; uint32_t rem; } uidiv_result_t;
typedef struct { uint64_t quot; uint64_t rem; } uldiv_result_t;

uint32_t __aeabi_uidiv(uint32_t num, uint32_t den) {
    if (den == 0) return 0;
    uint32_t quot = 0;
    uint32_t bit = 1;
    while (den <= num && !(den & (1u << 31))) { den <<= 1; bit <<= 1; }
    while (bit) {
        if (num >= den) { num -= den; quot |= bit; }
        den >>= 1; bit >>= 1;
    }
    return quot;
}

uidiv_result_t __aeabi_uidivmod(uint32_t num, uint32_t den) {
    uidiv_result_t r;
    r.quot = __aeabi_uidiv(num, den);
    r.rem = num - r.quot * den;
    return r;
}

int32_t __aeabi_idiv(int32_t num, int32_t den) {
    int negative = 0;
    if (num < 0) { num = -num; negative = !negative; }
    if (den < 0) { den = -den; negative = !negative; }
    int32_t result = (int32_t)__aeabi_uidiv((uint32_t)num, (uint32_t)den);
    return negative ? -result : result;
}

uldiv_result_t __aeabi_uldivmod(uint64_t num, uint64_t den) {
    uldiv_result_t r;
    if (den == 0) { r.quot = 0; r.rem = 0; return r; }
    r.quot = 0;
    uint64_t bit = 1;
    while (den <= num && !(den & ((uint64_t)1 << 63))) { den <<= 1; bit <<= 1; }
    while (bit) {
        if (num >= den) { num -= den; r.quot |= bit; }
        den >>= 1; bit >>= 1;
    }
    r.rem = num;
    return r;
}

/* ── ARM EABI memory routines ──────────────────────────────────────── */

void __aeabi_memcpy4(void *dst, const void *src, uint32_t n) {
    uint32_t *d = (uint32_t *)dst;
    const uint32_t *s = (const uint32_t *)src;
    uint32_t words = n >> 2;
    uint32_t rem = n & 3;
    while (words--) { *d++ = *s++; }
    if (rem) {
        uint8_t *db = (uint8_t *)d;
        const uint8_t *sb = (const uint8_t *)s;
        while (rem--) { *db++ = *sb++; }
    }
}

void __aeabi_memcpy8(void *dst, const void *src, uint32_t n) {
    __aeabi_memcpy4(dst, src, n);
}

void __aeabi_memcpy(void *dst, const void *src, uint32_t n) {
    uint8_t *d = (uint8_t *)dst;
    const uint8_t *s = (const uint8_t *)src;
    while (n--) { *d++ = *s++; }
}

void __aeabi_memset(void *dst, uint32_t n, int c) {
    uint8_t *d = (uint8_t *)dst;
    while (n--) { *d++ = (uint8_t)c; }
}

void __aeabi_memclr(void *dst, uint32_t n) {
    __aeabi_memset(dst, n, 0);
}

void __aeabi_memclr4(void *dst, uint32_t n) {
    __aeabi_memset(dst, n, 0);
}

void __aeabi_memclr8(void *dst, uint32_t n) {
    __aeabi_memset(dst, n, 0);
}

#endif /* __ARM_EABI__ */
