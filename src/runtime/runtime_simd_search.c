/*
 * SIMD String Search & Equality
 *
 * Wave 1: wraps dispatch table (scalar memmem/memcmp).
 * Wave 2: SIMD-accelerated search (Muła-style Generic SIMD strstr).
 *
 * Build: cc -c -fPIC -O2 -std=gnu11 -I. runtime_simd_search.c
 */

#include "runtime_simd_dispatch.h"

#if SIMD_HAS_X86
#  include <immintrin.h>
#endif

#if SIMD_HAS_NEON
#  include <arm_neon.h>
#endif

/* ================================================================
 * T2.6: Scalar String Equality
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
    const void* result = memmem(haystack, hlen, needle, nlen);
    if (!result) return -1;
    return (int64_t)((const uint8_t*)result - haystack);
}

/* Scalar reverse search */
static int64_t scalar_str_search_last(const uint8_t* haystack, uint64_t hlen,
                                      const uint8_t* needle, uint64_t nlen) {
    if (nlen == 0) return (int64_t)hlen;
    if (nlen > hlen) return -1;
    /* Scan backwards */
    for (int64_t i = (int64_t)(hlen - nlen); i >= 0; i--) {
        if (memcmp(haystack + i, needle, nlen) == 0) return i;
    }
    return -1;
}

/* ================================================================
 * T2.5: SSE2 Substring Search (Muła-style Generic SIMD strstr)
 * ================================================================ */

#if SIMD_HAS_SSE2

__attribute__((target("sse2")))
static int64_t sse2_str_search(const uint8_t* haystack, uint64_t hlen,
                               const uint8_t* needle, uint64_t nlen) {
    if (nlen == 0) return 0;
    if (nlen > hlen) return -1;

    const __m128i first = _mm_set1_epi8((char)needle[0]);

    /* Single-byte needle: scan for first byte only */
    if (nlen == 1) {
        uint64_t i = 0;
        for (; i + 16 <= hlen; i += 16) {
            __m128i block = _mm_loadu_si128((const __m128i*)(haystack + i));
            int mask = _mm_movemask_epi8(_mm_cmpeq_epi8(block, first));
            if (mask) {
                return (int64_t)(i + (unsigned)__builtin_ctz((unsigned)mask));
            }
        }
        /* Tail */
        for (; i < hlen; i++) {
            if (haystack[i] == needle[0]) return (int64_t)i;
        }
        return -1;
    }

    /* Multi-byte needle: first + last byte filter */
    const __m128i last = _mm_set1_epi8((char)needle[nlen - 1]);

    uint64_t i = 0;
    for (; i + nlen - 1 + 16 <= hlen; i += 16) {
        __m128i block_first = _mm_loadu_si128((const __m128i*)(haystack + i));
        __m128i block_last  = _mm_loadu_si128((const __m128i*)(haystack + i + nlen - 1));

        int mask_first = _mm_movemask_epi8(_mm_cmpeq_epi8(block_first, first));
        int mask_last  = _mm_movemask_epi8(_mm_cmpeq_epi8(block_last, last));
        int mask = mask_first & mask_last;

        while (mask) {
            int bit = __builtin_ctz((unsigned)mask);
            uint64_t pos = i + (unsigned)bit;
            if (memcmp(haystack + pos + 1, needle + 1, nlen - 2) == 0) {
                return (int64_t)pos;
            }
            mask &= mask - 1; /* clear lowest set bit */
        }
    }

    /* Scalar tail */
    for (; i + nlen <= hlen; i++) {
        if (haystack[i] == needle[0] &&
            haystack[i + nlen - 1] == needle[nlen - 1] &&
            memcmp(haystack + i + 1, needle + 1, nlen - 2) == 0) {
            return (int64_t)i;
        }
    }
    return -1;
}

__attribute__((target("sse2")))
static int64_t sse2_str_search_last(const uint8_t* haystack, uint64_t hlen,
                                    const uint8_t* needle, uint64_t nlen) {
    if (nlen == 0) return (int64_t)hlen;
    if (nlen > hlen) return -1;

    const __m128i first = _mm_set1_epi8((char)needle[0]);
    int64_t result = -1;

    /* Single-byte needle */
    if (nlen == 1) {
        uint64_t i = 0;
        for (; i + 16 <= hlen; i += 16) {
            __m128i block = _mm_loadu_si128((const __m128i*)(haystack + i));
            int mask = _mm_movemask_epi8(_mm_cmpeq_epi8(block, first));
            if (mask) {
                /* Find highest set bit */
                int top = 31 - __builtin_clz((unsigned)mask);
                result = (int64_t)(i + (unsigned)top);
            }
        }
        /* Tail */
        for (; i < hlen; i++) {
            if (haystack[i] == needle[0]) result = (int64_t)i;
        }
        return result;
    }

    /* Multi-byte needle: scan forward, keep last match */
    const __m128i last = _mm_set1_epi8((char)needle[nlen - 1]);

    uint64_t i = 0;
    for (; i + nlen - 1 + 16 <= hlen; i += 16) {
        __m128i block_first = _mm_loadu_si128((const __m128i*)(haystack + i));
        __m128i block_last  = _mm_loadu_si128((const __m128i*)(haystack + i + nlen - 1));

        int mask_first = _mm_movemask_epi8(_mm_cmpeq_epi8(block_first, first));
        int mask_last  = _mm_movemask_epi8(_mm_cmpeq_epi8(block_last, last));
        int mask = mask_first & mask_last;

        while (mask) {
            /* Extract highest set bit for reverse scan */
            int bit = 31 - __builtin_clz((unsigned)mask);
            uint64_t pos = i + (unsigned)bit;
            if (memcmp(haystack + pos + 1, needle + 1, nlen - 2) == 0) {
                result = (int64_t)pos;
            }
            /* Clear this bit and continue to find a later match in this chunk */
            mask &= ~(1 << bit);
        }
    }

    /* Scalar tail */
    for (; i + nlen <= hlen; i++) {
        if (haystack[i] == needle[0] &&
            haystack[i + nlen - 1] == needle[nlen - 1] &&
            memcmp(haystack + i + 1, needle + 1, nlen - 2) == 0) {
            result = (int64_t)i;
        }
    }
    return result;
}

__attribute__((target("sse2")))
static int sse2_str_equal(const uint8_t* a, uint64_t alen,
                          const uint8_t* b, uint64_t blen) {
    if (alen != blen) return 0;
    /* libc memcmp is already SIMD-optimized; just call it */
    return memcmp(a, b, alen) == 0 ? 1 : 0;
}

#endif /* SIMD_HAS_SSE2 */

/* ================================================================
 * T2.5: AVX2 Substring Search (Muła-style Generic SIMD strstr)
 * ================================================================ */

#if SIMD_CAN_AVX2

__attribute__((target("avx2")))
static int64_t avx2_str_search(const uint8_t* haystack, uint64_t hlen,
                               const uint8_t* needle, uint64_t nlen) {
    if (nlen == 0) return 0;
    if (nlen > hlen) return -1;

    const __m256i first = _mm256_set1_epi8((char)needle[0]);

    /* Single-byte needle */
    if (nlen == 1) {
        uint64_t i = 0;
        for (; i + 32 <= hlen; i += 32) {
            __m256i block = _mm256_loadu_si256((const __m256i*)(haystack + i));
            unsigned mask = (unsigned)_mm256_movemask_epi8(_mm256_cmpeq_epi8(block, first));
            if (mask) {
                return (int64_t)(i + (unsigned)__builtin_ctz(mask));
            }
        }
        /* Tail — use scalar */
        for (; i < hlen; i++) {
            if (haystack[i] == needle[0]) return (int64_t)i;
        }
        return -1;
    }

    /* Multi-byte needle */
    const __m256i last = _mm256_set1_epi8((char)needle[nlen - 1]);

    uint64_t i = 0;
    for (; i + nlen - 1 + 32 <= hlen; i += 32) {
        __m256i block_first = _mm256_loadu_si256((const __m256i*)(haystack + i));
        __m256i block_last  = _mm256_loadu_si256((const __m256i*)(haystack + i + nlen - 1));

        unsigned mask_first = (unsigned)_mm256_movemask_epi8(_mm256_cmpeq_epi8(block_first, first));
        unsigned mask_last  = (unsigned)_mm256_movemask_epi8(_mm256_cmpeq_epi8(block_last, last));
        unsigned mask = mask_first & mask_last;

        while (mask) {
            int bit = __builtin_ctz(mask);
            uint64_t pos = i + (unsigned)bit;
            if (memcmp(haystack + pos + 1, needle + 1, nlen - 2) == 0) {
                return (int64_t)pos;
            }
            mask &= mask - 1;
        }
    }

    /* Scalar tail */
    for (; i + nlen <= hlen; i++) {
        if (haystack[i] == needle[0] &&
            haystack[i + nlen - 1] == needle[nlen - 1] &&
            memcmp(haystack + i + 1, needle + 1, nlen - 2) == 0) {
            return (int64_t)i;
        }
    }
    return -1;
}

__attribute__((target("avx2")))
static int64_t avx2_str_search_last(const uint8_t* haystack, uint64_t hlen,
                                    const uint8_t* needle, uint64_t nlen) {
    if (nlen == 0) return (int64_t)hlen;
    if (nlen > hlen) return -1;

    const __m256i first = _mm256_set1_epi8((char)needle[0]);
    int64_t result = -1;

    /* Single-byte needle */
    if (nlen == 1) {
        uint64_t i = 0;
        for (; i + 32 <= hlen; i += 32) {
            __m256i block = _mm256_loadu_si256((const __m256i*)(haystack + i));
            unsigned mask = (unsigned)_mm256_movemask_epi8(_mm256_cmpeq_epi8(block, first));
            if (mask) {
                int top = 31 - __builtin_clz(mask);
                result = (int64_t)(i + (unsigned)top);
            }
        }
        for (; i < hlen; i++) {
            if (haystack[i] == needle[0]) result = (int64_t)i;
        }
        return result;
    }

    /* Multi-byte needle */
    const __m256i last = _mm256_set1_epi8((char)needle[nlen - 1]);

    uint64_t i = 0;
    for (; i + nlen - 1 + 32 <= hlen; i += 32) {
        __m256i block_first = _mm256_loadu_si256((const __m256i*)(haystack + i));
        __m256i block_last  = _mm256_loadu_si256((const __m256i*)(haystack + i + nlen - 1));

        unsigned mask_first = (unsigned)_mm256_movemask_epi8(_mm256_cmpeq_epi8(block_first, first));
        unsigned mask_last  = (unsigned)_mm256_movemask_epi8(_mm256_cmpeq_epi8(block_last, last));
        unsigned mask = mask_first & mask_last;

        while (mask) {
            int bit = 31 - __builtin_clz(mask);
            uint64_t pos = i + (unsigned)bit;
            if (memcmp(haystack + pos + 1, needle + 1, nlen - 2) == 0) {
                result = (int64_t)pos;
            }
            mask &= ~(1U << bit);
        }
    }

    /* Scalar tail */
    for (; i + nlen <= hlen; i++) {
        if (haystack[i] == needle[0] &&
            haystack[i + nlen - 1] == needle[nlen - 1] &&
            memcmp(haystack + i + 1, needle + 1, nlen - 2) == 0) {
            result = (int64_t)i;
        }
    }
    return result;
}

__attribute__((target("avx2")))
static int avx2_str_equal(const uint8_t* a, uint64_t alen,
                          const uint8_t* b, uint64_t blen) {
    if (alen != blen) return 0;
    return memcmp(a, b, alen) == 0 ? 1 : 0;
}

#endif /* SIMD_CAN_AVX2 */

/* ================================================================
 * T2.5: NEON Substring Search (Muła-style Generic SIMD strstr)
 * ================================================================ */

#if SIMD_HAS_NEON

/* Helper: extract a 16-bit mask from a NEON vceqq_u8 result.
 * Each bit corresponds to one byte lane (1 = match). */
static inline uint16_t neon_movemask(uint8x16_t v) {
    /* Shift each byte so bit 7 contains the comparison result,
     * then pack via narrow shift into a 64-bit value we can extract bits from.
     * Standard approach: use vshrn to produce a nibble-per-byte mask. */
    static const uint8_t shift_vals[16] = {
        1, 2, 4, 8, 16, 32, 64, 128,
        1, 2, 4, 8, 16, 32, 64, 128
    };
    uint8x16_t shift_mask = vld1q_u8(shift_vals);
    uint8x16_t masked = vandq_u8(v, shift_mask);

    /* Sum pairs of 8 bytes into 2 bytes */
    uint8x8_t lo = vget_low_u8(masked);
    uint8x8_t hi = vget_high_u8(masked);

    /* Horizontal add within each 8-byte half to produce one byte per half */
    uint8x8_t pair_lo = vpadd_u8(lo, lo);
    pair_lo = vpadd_u8(pair_lo, pair_lo);
    pair_lo = vpadd_u8(pair_lo, pair_lo);

    uint8x8_t pair_hi = vpadd_u8(hi, hi);
    pair_hi = vpadd_u8(pair_hi, pair_hi);
    pair_hi = vpadd_u8(pair_hi, pair_hi);

    uint16_t mask_lo = (uint16_t)vget_lane_u8(pair_lo, 0);
    uint16_t mask_hi = (uint16_t)vget_lane_u8(pair_hi, 0);

    return mask_lo | (mask_hi << 8);
}

static int64_t neon_str_search(const uint8_t* haystack, uint64_t hlen,
                               const uint8_t* needle, uint64_t nlen) {
    if (nlen == 0) return 0;
    if (nlen > hlen) return -1;

    const uint8x16_t first = vdupq_n_u8(needle[0]);

    /* Single-byte needle */
    if (nlen == 1) {
        uint64_t i = 0;
        for (; i + 16 <= hlen; i += 16) {
            uint8x16_t block = vld1q_u8(haystack + i);
            uint8x16_t cmp = vceqq_u8(block, first);
            uint16_t mask = neon_movemask(cmp);
            if (mask) {
                return (int64_t)(i + (unsigned)__builtin_ctz((unsigned)mask));
            }
        }
        for (; i < hlen; i++) {
            if (haystack[i] == needle[0]) return (int64_t)i;
        }
        return -1;
    }

    /* Multi-byte needle */
    const uint8x16_t last = vdupq_n_u8(needle[nlen - 1]);

    uint64_t i = 0;
    for (; i + nlen - 1 + 16 <= hlen; i += 16) {
        uint8x16_t block_first = vld1q_u8(haystack + i);
        uint8x16_t block_last  = vld1q_u8(haystack + i + nlen - 1);

        uint8x16_t cmp_first = vceqq_u8(block_first, first);
        uint8x16_t cmp_last  = vceqq_u8(block_last, last);
        uint16_t mask_first = neon_movemask(cmp_first);
        uint16_t mask_last  = neon_movemask(cmp_last);
        unsigned mask = (unsigned)(mask_first & mask_last);

        while (mask) {
            int bit = __builtin_ctz(mask);
            uint64_t pos = i + (unsigned)bit;
            if (memcmp(haystack + pos + 1, needle + 1, nlen - 2) == 0) {
                return (int64_t)pos;
            }
            mask &= mask - 1;
        }
    }

    /* Scalar tail */
    for (; i + nlen <= hlen; i++) {
        if (haystack[i] == needle[0] &&
            haystack[i + nlen - 1] == needle[nlen - 1] &&
            memcmp(haystack + i + 1, needle + 1, nlen - 2) == 0) {
            return (int64_t)i;
        }
    }
    return -1;
}

static int64_t neon_str_search_last(const uint8_t* haystack, uint64_t hlen,
                                    const uint8_t* needle, uint64_t nlen) {
    if (nlen == 0) return (int64_t)hlen;
    if (nlen > hlen) return -1;

    const uint8x16_t first = vdupq_n_u8(needle[0]);
    int64_t result = -1;

    /* Single-byte needle */
    if (nlen == 1) {
        uint64_t i = 0;
        for (; i + 16 <= hlen; i += 16) {
            uint8x16_t block = vld1q_u8(haystack + i);
            uint8x16_t cmp = vceqq_u8(block, first);
            uint16_t mask = neon_movemask(cmp);
            if (mask) {
                int top = 31 - __builtin_clz((unsigned)mask);
                result = (int64_t)(i + (unsigned)top);
            }
        }
        for (; i < hlen; i++) {
            if (haystack[i] == needle[0]) result = (int64_t)i;
        }
        return result;
    }

    /* Multi-byte needle */
    const uint8x16_t last = vdupq_n_u8(needle[nlen - 1]);

    uint64_t i = 0;
    for (; i + nlen - 1 + 16 <= hlen; i += 16) {
        uint8x16_t block_first = vld1q_u8(haystack + i);
        uint8x16_t block_last  = vld1q_u8(haystack + i + nlen - 1);

        uint8x16_t cmp_first = vceqq_u8(block_first, first);
        uint8x16_t cmp_last  = vceqq_u8(block_last, last);
        uint16_t mask_first = neon_movemask(cmp_first);
        uint16_t mask_last  = neon_movemask(cmp_last);
        unsigned mask = (unsigned)(mask_first & mask_last);

        while (mask) {
            int bit = 31 - __builtin_clz(mask);
            uint64_t pos = i + (unsigned)bit;
            if (memcmp(haystack + pos + 1, needle + 1, nlen - 2) == 0) {
                result = (int64_t)pos;
            }
            mask &= ~(1U << bit);
        }
    }

    /* Scalar tail */
    for (; i + nlen <= hlen; i++) {
        if (haystack[i] == needle[0] &&
            haystack[i + nlen - 1] == needle[nlen - 1] &&
            memcmp(haystack + i + 1, needle + 1, nlen - 2) == 0) {
            result = (int64_t)i;
        }
    }
    return result;
}

static int neon_str_equal(const uint8_t* a, uint64_t alen,
                          const uint8_t* b, uint64_t blen) {
    if (alen != blen) return 0;
    return memcmp(a, b, alen) == 0 ? 1 : 0;
}

#endif /* SIMD_HAS_NEON */

/* ================================================================
 * Local Dispatch for str_search / str_search_last / str_equal
 *
 * Selects best SIMD tier at first call, caches in static fn pointers.
 * ================================================================ */

typedef int64_t (*search_fn)(const uint8_t*, uint64_t, const uint8_t*, uint64_t);
typedef int     (*equal_fn)(const uint8_t*, uint64_t, const uint8_t*, uint64_t);

static search_fn local_str_search      = NULL;
static search_fn local_str_search_last = NULL;
static equal_fn  local_str_equal       = NULL;

static void local_dispatch_init(void) {
    static int inited = 0;
    if (inited) return;
    inited = 1;

    /* Default to scalar */
    local_str_search      = scalar_str_search_local;
    local_str_search_last = scalar_str_search_last;
    local_str_equal       = scalar_str_equal_local;

#if SIMD_HAS_NEON
    if (simd_detect_neon()) {
        local_str_search      = neon_str_search;
        local_str_search_last = neon_str_search_last;
        local_str_equal       = neon_str_equal;
    }
#endif

#if SIMD_HAS_SSE2
    /* SSE2 is baseline on x86_64, always available */
    local_str_search      = sse2_str_search;
    local_str_search_last = sse2_str_search_last;
    local_str_equal       = sse2_str_equal;
#endif

#if SIMD_CAN_AVX2
    if (simd_detect_avx2()) {
        local_str_search      = avx2_str_search;
        local_str_search_last = avx2_str_search_last;
        local_str_equal       = avx2_str_equal;
    }
#endif
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

    local_dispatch_init();
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

    local_dispatch_init();
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

    local_dispatch_init();
    return (int64_t)local_str_equal(
        (const uint8_t*)a->data, a->len,
        (const uint8_t*)b->data, b->len);
}
