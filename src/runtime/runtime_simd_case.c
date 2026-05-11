/*
 * SIMD ASCII Case Operations — is_ascii, to_upper, to_lower
 *
 * Wave 1: scalar stubs with reserved-field caching for is_ascii.
 * Wave 2: SIMD fast paths.
 *
 * Build: cc -c -fPIC -O2 -std=gnu11 -I. runtime_simd_case.c
 */

#include "runtime_simd_dispatch.h"
#include <stdlib.h>

/* ================================================================
 * Reserved-Field ASCII Cache Helpers
 * ================================================================ */

static inline void cache_ascii_flag(RtCoreStringSimd* s, int is_ascii) {
    if (!s) return;
    uint32_t r = s->reserved;
    r |= SIMD_CACHE_FLAG_ASCII_VALID;
    if (is_ascii)
        r |= SIMD_CACHE_FLAG_ASCII_VALUE;
    else
        r &= ~SIMD_CACHE_FLAG_ASCII_VALUE;
    s->reserved = r;
}

static inline int cached_ascii_flag(const RtCoreStringSimd* s) {
    if (!s) return -1;
    if (!(s->reserved & SIMD_CACHE_FLAG_ASCII_VALID)) return -1;
    return (s->reserved & SIMD_CACHE_FLAG_ASCII_VALUE) ? 1 : 0;
}

/* ================================================================
 * rt_* Public API
 * ================================================================ */

/*
 * rt_text_is_ascii(tagged_string) -> int64_t (1=all ASCII, 0=has non-ASCII)
 *   Caches the result in the reserved field.
 */
int64_t rt_text_is_ascii(int64_t value) {
    RtCoreStringSimd* s = simd_as_string(value);
    if (!s) return 1; /* nil/non-string: vacuously ASCII */

    /* Check cache */
    int cached = cached_ascii_flag(s);
    if (cached >= 0) return (int64_t)cached;

    /* Compute via dispatch table */
    int result = g_simd_text.is_ascii(
        (const uint8_t*)s->data, s->len);

    /* Cache the result */
    cache_ascii_flag(s, result);
    return (int64_t)result;
}

/*
 * rt_text_to_upper_ascii(tagged_string) -> int64_t (new tagged string)
 *   Allocates a new string with ASCII chars uppercased.
 *   Non-ASCII bytes are copied unchanged.
 */
int64_t rt_text_to_upper_ascii(int64_t value) {
    RtCoreStringSimd* s = simd_as_string(value);
    if (!s || s->len == 0) return value;

    /* Allocate new RtCoreStringSimd */
    size_t total = sizeof(RtCoreStringSimd) + (size_t)s->len + 1;
    RtCoreStringSimd* out = (RtCoreStringSimd*)malloc(total);
    if (!out) return value;

    out->kind = RT_VALUE_HEAP_STRING_SIMD;
    out->reserved = 0;
    out->len = s->len;

    g_simd_text.to_upper_ascii(
        (const uint8_t*)s->data, (uint8_t*)out->data, s->len);
    out->data[s->len] = '\0';

    /* Return tagged pointer */
    return (int64_t)(((uintptr_t)out) | RT_VALUE_TAG_HEAP_SIMD);
}

/*
 * rt_text_to_lower_ascii(tagged_string) -> int64_t (new tagged string)
 *   Allocates a new string with ASCII chars lowercased.
 *   Non-ASCII bytes are copied unchanged.
 */
int64_t rt_text_to_lower_ascii(int64_t value) {
    RtCoreStringSimd* s = simd_as_string(value);
    if (!s || s->len == 0) return value;

    /* Allocate new RtCoreStringSimd */
    size_t total = sizeof(RtCoreStringSimd) + (size_t)s->len + 1;
    RtCoreStringSimd* out = (RtCoreStringSimd*)malloc(total);
    if (!out) return value;

    out->kind = RT_VALUE_HEAP_STRING_SIMD;
    out->reserved = 0;
    out->len = s->len;

    g_simd_text.to_lower_ascii(
        (const uint8_t*)s->data, (uint8_t*)out->data, s->len);
    out->data[s->len] = '\0';

    /* Return tagged pointer */
    return (int64_t)(((uintptr_t)out) | RT_VALUE_TAG_HEAP_SIMD);
}
