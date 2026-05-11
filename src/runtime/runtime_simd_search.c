/*
 * SIMD String Search & Equality
 *
 * Wave 1: wraps dispatch table (scalar memmem/memcmp).
 * Wave 2: SIMD-accelerated search (e.g. SSE4.2 PCMPESTRI).
 *
 * Build: cc -c -fPIC -O2 -std=gnu11 -I. runtime_simd_search.c
 */

#include "runtime_simd_dispatch.h"

/* ================================================================
 * rt_* Public API
 * ================================================================ */

/*
 * rt_simd_str_search(haystack, needle) -> int64_t
 *   Returns byte offset of first occurrence, or -1 if not found.
 *   Both arguments are tagged RuntimeValues (strings).
 */
int64_t rt_simd_str_search(int64_t haystack_val, int64_t needle_val) {
    RtCoreStringSimd* h = simd_as_string(haystack_val);
    RtCoreStringSimd* n = simd_as_string(needle_val);

    if (!h) return -1;
    if (!n || n->len == 0) return 0;

    return g_simd_text.str_search(
        (const uint8_t*)h->data, h->len,
        (const uint8_t*)n->data, n->len);
}

/*
 * rt_simd_str_equal(a, b) -> int64_t (1=equal, 0=not equal)
 *   Both arguments are tagged RuntimeValues (strings).
 */
int64_t rt_simd_str_equal(int64_t a_val, int64_t b_val) {
    /* Fast path: same tagged value */
    if (a_val == b_val) return 1;

    RtCoreStringSimd* a = simd_as_string(a_val);
    RtCoreStringSimd* b = simd_as_string(b_val);

    if (!a && !b) return 1;
    if (!a || !b) return 0;

    return (int64_t)g_simd_text.str_equal(
        (const uint8_t*)a->data, a->len,
        (const uint8_t*)b->data, b->len);
}
