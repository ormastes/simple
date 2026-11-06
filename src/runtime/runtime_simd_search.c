/*
 * String Search & Equality
 *
 * Portable scalar baseline only (libc memchr/memmem/memcmp). The SSE2/AVX2/
 * NEON Mula-style search kernels moved to the levelled vector provider
 * (providers/vector/text_level_kernels.c, SIMPLE_VECTOR_TEXT_FIND[_LAST]);
 * when runtime_simd_utf8.c admitted it, haystacks of at least
 * SIMD_TEXT_PROVIDER_MIN_BYTES route there, otherwise scalar.
 *
 * Build: cc -c -fPIC -O2 -std=gnu11 -I. runtime_simd_search.c
 */

/* glibc declares memmem only with GNU extensions enabled. Feature-test
 * macros must precede every system header, including the dispatch header. */
#if defined(__linux__) && !defined(_GNU_SOURCE)
#  define _GNU_SOURCE 1
#endif

#include "runtime_simd_dispatch.h"
#include "simple_vector_kernel_abi_v1.h"

/* ================================================================
 * T2.6: Scalar String Equality (libc memcmp is already vectorized)
 * ================================================================ */

static int scalar_str_equal_local(const uint8_t* a, uint64_t alen,
                                  const uint8_t* b, uint64_t blen) {
    if (alen != blen) return 0;
    return memcmp(a, b, alen) == 0 ? 1 : 0;
}

/* ================================================================
 * T2.5: Scalar Substring Search (memmem wrapper)
 * ================================================================ */

static int64_t scalar_str_search_local(const uint8_t* haystack, uint64_t hlen,
                                       const uint8_t* needle, uint64_t nlen) {
    if (nlen == 0) return 0;
    if (nlen > hlen) return -1;
    if (nlen == 1) {
        const uint8_t* p = (const uint8_t*)memchr(haystack, needle[0], hlen);
        return p ? (int64_t)(p - haystack) : -1;
    }
#ifdef _WIN32
    /* memmem is a GNU/BSD extension absent from the Windows CRTs. memchr for
     * the first byte keeps the CRT's vectorized scan on the hot path. */
    for (uint64_t i = 0; i + nlen <= hlen;) {
        const uint8_t* p = (const uint8_t*)memchr(haystack + i, needle[0], (size_t)(hlen - nlen + 1 - i));
        if (!p) return -1;
        i = (uint64_t)(p - haystack);
        if (memcmp(p, needle, (size_t)nlen) == 0) return (int64_t)i;
        i++;
    }
    return -1;
#else
    const void* result = memmem(haystack, hlen, needle, nlen);
    if (!result) return -1;
    return (int64_t)((const uint8_t*)result - haystack);
#endif
}

/* Scalar reverse search */
static int64_t scalar_str_search_last(const uint8_t* haystack, uint64_t hlen,
                                      const uint8_t* needle, uint64_t nlen) {
    if (nlen == 0) return (int64_t)hlen;
    if (nlen > hlen) return -1;
    /* Scan backwards */
    for (int64_t i = (int64_t)(hlen - nlen); i >= 0; i--) {
        if (haystack[i] == needle[0] && memcmp(haystack + i, needle, nlen) == 0) return i;
    }
    return -1;
}

/* ================================================================
 * Routed search: provider for long haystacks, scalar otherwise
 * ================================================================ */

static int64_t local_str_search(const uint8_t* haystack, uint64_t hlen,
                                const uint8_t* needle, uint64_t nlen) {
    int64_t r;
    simd_text_init();
    if (hlen >= SIMD_TEXT_PROVIDER_MIN_BYTES && nlen > 0 && nlen <= hlen &&
        simd_text_provider_call(SIMPLE_VECTOR_TEXT_FIND, haystack, hlen, needle, nlen, NULL, &r))
        return r;
    return scalar_str_search_local(haystack, hlen, needle, nlen);
}

static int64_t local_str_search_last(const uint8_t* haystack, uint64_t hlen,
                                     const uint8_t* needle, uint64_t nlen) {
    int64_t r;
    simd_text_init();
    if (hlen >= SIMD_TEXT_PROVIDER_MIN_BYTES && nlen > 0 && nlen <= hlen &&
        simd_text_provider_call(SIMPLE_VECTOR_TEXT_FIND_LAST, haystack, hlen, needle, nlen, NULL, &r))
        return r;
    return scalar_str_search_last(haystack, hlen, needle, nlen);
}

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

    return local_str_search(
        (const uint8_t*)h->data, h->len,
        (const uint8_t*)n->data, n->len);
}

/*
 * rt_simd_str_last_index_of(haystack, needle) -> int64_t
 *   Returns byte offset of last occurrence, or -1 if not found.
 *   Both arguments are tagged RuntimeValues (strings).
 */
int64_t rt_simd_str_last_index_of(int64_t haystack_val, int64_t needle_val) {
    RtCoreStringSimd* h = simd_as_string(haystack_val);
    RtCoreStringSimd* n = simd_as_string(needle_val);

    if (!h) return -1;
    if (!n || n->len == 0) return (int64_t)h->len;

    return local_str_search_last(
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

    return (int64_t)scalar_str_equal_local(
        (const uint8_t*)a->data, a->len,
        (const uint8_t*)b->data, b->len);
}
