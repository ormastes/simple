/*
 * SIMD UTF-8 Operations — codepoint counting, validation, invalid-byte search
 *
 * Wave 1: scalar stubs with reserved-field caching.
 * Wave 2: AVX2/NEON fast paths via __attribute__((target)).
 *
 * Build: cc -c -fPIC -O2 -std=gnu11 -I. runtime_simd_utf8.c
 */

#include "runtime_simd_dispatch.h"
#include <stdlib.h>

/* ================================================================
 * Reserved-Field Cache Helpers
 * ================================================================ */

static inline void cache_cp_count(RtCoreStringSimd* s, int64_t count) {
    if (!s) return;
    if (count < 0 || (uint64_t)count > SIMD_CACHE_CPCOUNT_MASK) return;
    uint32_t r = s->reserved;
    r |= SIMD_CACHE_FLAG_CPCOUNT_VALID;
    r = (r & ~SIMD_CACHE_CPCOUNT_MASK) | ((uint32_t)count & SIMD_CACHE_CPCOUNT_MASK);
    s->reserved = r;
}

static inline int64_t cached_cp_count(const RtCoreStringSimd* s) {
    if (!s) return -1;
    if (!(s->reserved & SIMD_CACHE_FLAG_CPCOUNT_VALID)) return -1;
    return (int64_t)(s->reserved & SIMD_CACHE_CPCOUNT_MASK);
}

/* ================================================================
 * AVX2 Placeholders (call scalar for now)
 * ================================================================ */

#if SIMD_CAN_AVX2

__attribute__((target("avx2")))
static int64_t avx2_utf8_count_codepoints(const uint8_t* data, uint64_t len) {
    /* Wave 2: real AVX2 implementation */
    return g_simd_text.utf8_count_codepoints(data, len);
}

__attribute__((target("avx2")))
static int avx2_utf8_validate(const uint8_t* data, uint64_t len) {
    /* Wave 2: real AVX2 implementation */
    return g_simd_text.utf8_validate(data, len);
}

__attribute__((target("avx2")))
static int64_t avx2_utf8_find_invalid(const uint8_t* data, uint64_t len) {
    /* Wave 2: real AVX2 implementation */
    return g_simd_text.utf8_find_invalid(data, len);
}

#endif /* SIMD_CAN_AVX2 */

/* ================================================================
 * rt_* Public API
 * ================================================================ */

/*
 * rt_text_count_codepoints_cached(tagged_string) -> int64_t
 *
 * Checks the reserved-field cache first; falls back to dispatch table.
 * Caches the result in reserved for subsequent calls.
 */
int64_t rt_text_count_codepoints_cached(int64_t value) {
    RtCoreStringSimd* s = simd_as_string(value);
    if (!s) return 0;

    /* Check cache */
    int64_t cached = cached_cp_count(s);
    if (cached >= 0) return cached;

    /* Dispatch to best available implementation */
    int64_t count = g_simd_text.utf8_count_codepoints(
        (const uint8_t*)s->data, s->len);

    /* Cache the result */
    cache_cp_count(s, count);
    return count;
}

/*
 * rt_text_validate_utf8(tagged_string) -> int64_t (1=valid, 0=invalid)
 */
int64_t rt_text_validate_utf8(int64_t value) {
    RtCoreStringSimd* s = simd_as_string(value);
    if (!s) return 1; /* nil/non-string: vacuously valid */
    return (int64_t)g_simd_text.utf8_validate(
        (const uint8_t*)s->data, s->len);
}

/*
 * rt_text_find_invalid_utf8(tagged_string) -> int64_t
 *   Returns byte offset of first invalid byte, or -1 if valid.
 */
int64_t rt_text_find_invalid_utf8(int64_t value) {
    RtCoreStringSimd* s = simd_as_string(value);
    if (!s) return -1;
    return g_simd_text.utf8_find_invalid(
        (const uint8_t*)s->data, s->len);
}
