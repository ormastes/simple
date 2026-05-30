/*
 * SIMD UTF-8 Operations — codepoint counting, validation, invalid-byte search
 *
 * Wave 1: scalar stubs with reserved-field caching.
 * Wave 2: AVX2/SSE2/NEON fast paths via __attribute__((target)).
 *
 * Build: cc -c -fPIC -O2 -std=gnu11 -I. runtime_simd_utf8.c
 */

#include "runtime_simd_dispatch.h"
#include <stdlib.h>
#include <ctype.h>

#if SIMD_HAS_X86
#  include <immintrin.h>
#endif

#if SIMD_HAS_NEON
#  include <arm_neon.h>
#endif

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

/* Check the reserved-field ASCII cache.
 * Returns 1 if the string is known all-ASCII, 0 otherwise (unknown or not ASCII).
 * Bit 31 (SIMD_CACHE_FLAG_IS_ASCII) is set when the string is confirmed all-ASCII. */
static inline int rt_str_is_ascii_cached(const RtCoreStringSimd* s) {
    if (!s) return 0;
    return (s->reserved & SIMD_CACHE_FLAG_IS_ASCII) ? 1 : 0;
}

/* ================================================================
 * Scalar UTF-8 Codepoint Counting (fallback for non-SIMD platforms)
 * ================================================================ */

static int64_t scalar_utf8_count_codepoints(const uint8_t* data, uint64_t len) {
    int64_t count = 0;
    for (uint64_t i = 0; i < len; i++) {
        /* Count bytes where (byte & 0xC0) != 0x80 — these are lead bytes */
        if ((data[i] & 0xC0) != 0x80) {
            count++;
        }
    }
    return count;
}

/* ================================================================
 * T2.1: SSE2 UTF-8 Codepoint Counting (Keiser-Lemire)
 * ================================================================ */

#if SIMD_HAS_SSE2

__attribute__((target("sse2")))
static int64_t sse2_utf8_count_codepoints(const uint8_t* data, uint64_t len) {
    int64_t count = 0;
    uint64_t i = 0;

    /* Process 16-byte chunks */
    for (; i + 16 <= len; i += 16) {
        __m128i chunk = _mm_loadu_si128((const __m128i*)(data + i));
        /* Isolate top 2 bits of each byte */
        __m128i high_bits = _mm_and_si128(chunk, _mm_set1_epi8((int8_t)0xC0));
        /* Continuation bytes have top 2 bits == 10xxxxxx == 0x80 */
        __m128i is_cont = _mm_cmpeq_epi8(high_bits, _mm_set1_epi8((int8_t)0x80));
        /* is_cont = 0xFF for continuation bytes, 0x00 for lead/ASCII */
        int mask = _mm_movemask_epi8(is_cont);
        /* Lead bytes = 16 - number of continuation bytes */
        count += 16 - __builtin_popcount(mask);
    }

    /* Scalar tail */
    for (; i < len; i++) {
        if ((data[i] & 0xC0) != 0x80) {
            count++;
        }
    }

    return count;
}

#endif /* SIMD_HAS_SSE2 */

/* ================================================================
 * T2.1: AVX2 UTF-8 Codepoint Counting (Keiser-Lemire)
 * ================================================================ */

#if SIMD_CAN_AVX2

__attribute__((target("avx2")))
static int64_t avx2_utf8_count_codepoints(const uint8_t* data, uint64_t len) {
    int64_t count = 0;
    uint64_t i = 0;

    /* Process 32-byte chunks */
    for (; i + 32 <= len; i += 32) {
        __m256i chunk = _mm256_loadu_si256((const __m256i*)(data + i));
        /* Isolate top 2 bits of each byte */
        __m256i high_bits = _mm256_and_si256(chunk, _mm256_set1_epi8((int8_t)0xC0));
        /* Continuation bytes have top 2 bits == 0x80 */
        __m256i is_cont = _mm256_cmpeq_epi8(high_bits, _mm256_set1_epi8((int8_t)0x80));
        int mask = _mm256_movemask_epi8(is_cont);
        /* Lead bytes = 32 - number of continuation bytes */
        count += 32 - __builtin_popcount(mask);
    }

    /* SSE2 middle: process remaining 16-byte chunk if present */
    for (; i + 16 <= len; i += 16) {
        __m128i chunk = _mm_loadu_si128((const __m128i*)(data + i));
        __m128i high_bits = _mm_and_si128(chunk, _mm_set1_epi8((int8_t)0xC0));
        __m128i is_cont = _mm_cmpeq_epi8(high_bits, _mm_set1_epi8((int8_t)0x80));
        int mask = _mm_movemask_epi8(is_cont);
        count += 16 - __builtin_popcount(mask);
    }

    /* Scalar tail */
    for (; i < len; i++) {
        if ((data[i] & 0xC0) != 0x80) {
            count++;
        }
    }

    return count;
}

#endif /* SIMD_CAN_AVX2 */

/* ================================================================
 * T2.1: NEON UTF-8 Codepoint Counting (Keiser-Lemire)
 * ================================================================ */

#if SIMD_HAS_NEON && defined(__aarch64__)

static int64_t neon_utf8_count_codepoints(const uint8_t* data, uint64_t len) {
    int64_t count = 0;
    uint64_t i = 0;

    /* Process 16-byte chunks */
    for (; i + 16 <= len; i += 16) {
        uint8x16_t chunk = vld1q_u8(data + i);
        /* Isolate top 2 bits */
        uint8x16_t high_bits = vandq_u8(chunk, vdupq_n_u8(0xC0));
        /* Check for continuation bytes (top 2 bits == 0x80) */
        uint8x16_t is_cont = vceqq_u8(high_bits, vdupq_n_u8(0x80));
        /* Invert: 0xFF for lead bytes, 0x00 for continuation */
        uint8x16_t is_lead = vmvnq_u8(is_cont);
        /* Convert 0xFF to 1, then horizontal sum */
        uint8x16_t ones = vandq_u8(is_lead, vdupq_n_u8(1));
        count += vaddvq_u8(ones);
    }

    /* Scalar tail */
    for (; i < len; i++) {
        if ((data[i] & 0xC0) != 0x80) {
            count++;
        }
    }

    return count;
}

#endif /* SIMD_HAS_NEON && __aarch64__ */

/* ================================================================
 * T2.2: Scalar UTF-8 Validation
 * ================================================================ */

static int scalar_utf8_validate(const uint8_t* data, uint64_t len) {
    uint64_t i = 0;
    while (i < len) {
        uint8_t b = data[i];
        uint64_t need;
        uint32_t cp;

        if (b < 0x80) {
            /* ASCII — always valid */
            i++;
            continue;
        } else if ((b & 0xE0) == 0xC0) {
            need = 2; cp = b & 0x1F;
            /* Reject overlong: 0xC0, 0xC1 (cp < 2) */
            if (cp < 2) return 0;
        } else if ((b & 0xF0) == 0xE0) {
            need = 3; cp = b & 0x0F;
        } else if ((b & 0xF8) == 0xF0) {
            need = 4; cp = b & 0x07;
        } else {
            /* 0x80-0xBF as lead byte, or 0xF5+ */
            return 0;
        }

        if (i + need > len) return 0; /* Truncated sequence */

        for (uint64_t j = 1; j < need; j++) {
            if ((data[i + j] & 0xC0) != 0x80) return 0;
            cp = (cp << 6) | (data[i + j] & 0x3F);
        }

        /* Overlong check */
        if (need == 3 && cp < 0x800) return 0;
        if (need == 4 && cp < 0x10000) return 0;
        /* Surrogate check */
        if (cp >= 0xD800 && cp <= 0xDFFF) return 0;
        /* Range check */
        if (cp > 0x10FFFF) return 0;

        i += need;
    }
    return 1;
}

/* ================================================================
 * T2.2: Scalar UTF-8 Find-Invalid
 * ================================================================ */

static int64_t scalar_utf8_find_invalid(const uint8_t* data, uint64_t len) {
    uint64_t i = 0;
    while (i < len) {
        uint8_t b = data[i];
        uint64_t need;
        uint32_t cp;

        if (b < 0x80) { i++; continue; }
        else if ((b & 0xE0) == 0xC0) { need = 2; cp = b & 0x1F; if (cp < 2) return (int64_t)i; }
        else if ((b & 0xF0) == 0xE0) { need = 3; cp = b & 0x0F; }
        else if ((b & 0xF8) == 0xF0) { need = 4; cp = b & 0x07; }
        else return (int64_t)i;

        if (i + need > len) return (int64_t)i;
        for (uint64_t j = 1; j < need; j++) {
            if ((data[i + j] & 0xC0) != 0x80) return (int64_t)i;
            cp = (cp << 6) | (data[i + j] & 0x3F);
        }
        if (need == 3 && cp < 0x800) return (int64_t)i;
        if (need == 4 && cp < 0x10000) return (int64_t)i;
        if (cp >= 0xD800 && cp <= 0xDFFF) return (int64_t)i;
        if (cp > 0x10FFFF) return (int64_t)i;
        i += need;
    }
    return -1;
}

/* ================================================================
 * T2.2: AVX2 UTF-8 Validation
 *
 * Strategy: SIMD-scan in 32-byte chunks. If a chunk is all-ASCII
 * (no bytes >= 0x80), skip it entirely. Otherwise, fall back to
 * scalar validation of the non-ASCII region. This gives real
 * speedup on predominantly-ASCII text without the complexity
 * of full simdjson lookup tables.
 * ================================================================ */

#if SIMD_CAN_AVX2

/* Scalar validate a sub-range, handling multibyte sequences that
 * might start before 'start' by backing up to the nearest lead byte. */
static int avx2_validate_chunk_scalar(const uint8_t* data, uint64_t full_len,
                                      uint64_t start, uint64_t end) {
    /* Back up to the nearest lead byte before 'start' to avoid
     * splitting a multibyte sequence at the chunk boundary. */
    uint64_t pos = start;
    while (pos > 0 && (data[pos] & 0xC0) == 0x80) {
        pos--;
    }
    /* Validate from pos to end */
    while (pos < end && pos < full_len) {
        uint8_t b = data[pos];
        uint64_t need;
        uint32_t cp;

        if (b < 0x80) { pos++; continue; }
        else if ((b & 0xE0) == 0xC0) { need = 2; cp = b & 0x1F; if (cp < 2) return 0; }
        else if ((b & 0xF0) == 0xE0) { need = 3; cp = b & 0x0F; }
        else if ((b & 0xF8) == 0xF0) { need = 4; cp = b & 0x07; }
        else return 0;

        if (pos + need > full_len) return 0;
        for (uint64_t j = 1; j < need; j++) {
            if ((data[pos + j] & 0xC0) != 0x80) return 0;
            cp = (cp << 6) | (data[pos + j] & 0x3F);
        }
        if (need == 3 && cp < 0x800) return 0;
        if (need == 4 && cp < 0x10000) return 0;
        if (cp >= 0xD800 && cp <= 0xDFFF) return 0;
        if (cp > 0x10FFFF) return 0;
        pos += need;
    }
    return 1;
}

__attribute__((target("avx2")))
static int avx2_utf8_validate(const uint8_t* data, uint64_t len) {
    uint64_t i = 0;

    /* Process 32-byte chunks — fast-skip all-ASCII chunks */
    for (; i + 32 <= len; i += 32) {
        __m256i chunk = _mm256_loadu_si256((const __m256i*)(data + i));
        /* Check if any byte has the high bit set (non-ASCII) */
        int mask = _mm256_movemask_epi8(chunk);
        if (mask != 0) {
            /* Non-ASCII chunk — validate with scalar.
             * Extend to cover any multibyte sequence that spans
             * into the next chunk (up to 3 extra bytes). */
            uint64_t end = i + 32;
            if (end + 3 <= len) end += 3;
            else end = len;
            if (!avx2_validate_chunk_scalar(data, len, i, end)) return 0;
            /* Advance past the validated region. We need to find
             * where the scalar validator left off. Re-scan from
             * end of the validated region, but we can skip to the
             * next 32-byte boundary minus 3 (to handle overlap). */
        }
    }

    /* Scalar tail: validate everything from the last aligned position */
    /* We re-validate from the last chunk boundary to handle any
     * multibyte sequences that might span chunk boundaries. */
    uint64_t tail_start = (i > 3) ? i - 3 : 0;
    return scalar_utf8_validate(data + tail_start, len - tail_start);
}

__attribute__((target("avx2")))
static int64_t avx2_utf8_find_invalid(const uint8_t* data, uint64_t len) {
    uint64_t i = 0;

    /* Fast-skip all-ASCII 32-byte chunks */
    for (; i + 32 <= len; i += 32) {
        __m256i chunk = _mm256_loadu_si256((const __m256i*)(data + i));
        int mask = _mm256_movemask_epi8(chunk);
        if (mask != 0) {
            /* Non-ASCII chunk — fall back to scalar for this region */
            uint64_t back = i;
            while (back > 0 && (data[back] & 0xC0) == 0x80) back--;
            return scalar_utf8_find_invalid(data + back, len - back);
        }
    }

    /* Scalar tail */
    uint64_t tail_start = (i > 3) ? i - 3 : 0;
    int64_t result = scalar_utf8_find_invalid(data + tail_start, len - tail_start);
    if (result >= 0) return result + (int64_t)tail_start;
    return -1;
}

#endif /* SIMD_CAN_AVX2 */

/* ================================================================
 * T2.2: SSE2 UTF-8 Validation
 *
 * SSE2 lacks pshufb (SSSE3+), so we use the same ASCII-fast-skip
 * strategy as AVX2 but with 16-byte chunks.
 * ================================================================ */

#if SIMD_HAS_SSE2

__attribute__((target("sse2")))
static int sse2_utf8_validate(const uint8_t* data, uint64_t len) {
    uint64_t i = 0;

    /* Process 16-byte chunks — fast-skip all-ASCII chunks */
    for (; i + 16 <= len; i += 16) {
        __m128i chunk = _mm_loadu_si128((const __m128i*)(data + i));
        /* Check if any byte has the high bit set (non-ASCII) */
        int mask = _mm_movemask_epi8(chunk);
        if (mask != 0) {
            /* Non-ASCII — fall back to scalar for remainder */
            uint64_t back = i;
            while (back > 0 && (data[back] & 0xC0) == 0x80) back--;
            return scalar_utf8_validate(data + back, len - back);
        }
    }

    /* Scalar tail */
    uint64_t tail_start = (i > 3) ? i - 3 : 0;
    return scalar_utf8_validate(data + tail_start, len - tail_start);
}

__attribute__((target("sse2")))
static int64_t sse2_utf8_find_invalid(const uint8_t* data, uint64_t len) {
    uint64_t i = 0;

    /* Fast-skip all-ASCII 16-byte chunks */
    for (; i + 16 <= len; i += 16) {
        __m128i chunk = _mm_loadu_si128((const __m128i*)(data + i));
        int mask = _mm_movemask_epi8(chunk);
        if (mask != 0) {
            /* Non-ASCII — fall back to scalar */
            uint64_t back = i;
            while (back > 0 && (data[back] & 0xC0) == 0x80) back--;
            int64_t result = scalar_utf8_find_invalid(data + back, len - back);
            if (result >= 0) return result + (int64_t)back;
            return -1;
        }
    }

    /* Scalar tail */
    uint64_t tail_start = (i > 3) ? i - 3 : 0;
    int64_t result = scalar_utf8_find_invalid(data + tail_start, len - tail_start);
    if (result >= 0) return result + (int64_t)tail_start;
    return -1;
}

#endif /* SIMD_HAS_SSE2 */

/* ================================================================
 * T2.2: NEON UTF-8 Validation (aarch64)
 *
 * Same ASCII-fast-skip strategy with 16-byte chunks.
 * ================================================================ */

#if SIMD_HAS_NEON && defined(__aarch64__)

static int neon_utf8_validate(const uint8_t* data, uint64_t len) {
    uint64_t i = 0;

    /* Process 16-byte chunks — fast-skip all-ASCII chunks */
    for (; i + 16 <= len; i += 16) {
        uint8x16_t chunk = vld1q_u8(data + i);
        /* Check if any byte >= 0x80 using unsigned max reduction */
        uint8_t max_val = vmaxvq_u8(chunk);
        if (max_val >= 0x80) {
            /* Non-ASCII — fall back to scalar for remainder */
            uint64_t back = i;
            while (back > 0 && (data[back] & 0xC0) == 0x80) back--;
            return scalar_utf8_validate(data + back, len - back);
        }
    }

    /* Scalar tail */
    uint64_t tail_start = (i > 3) ? i - 3 : 0;
    return scalar_utf8_validate(data + tail_start, len - tail_start);
}

static int64_t neon_utf8_find_invalid(const uint8_t* data, uint64_t len) {
    uint64_t i = 0;

    /* Fast-skip all-ASCII 16-byte chunks */
    for (; i + 16 <= len; i += 16) {
        uint8x16_t chunk = vld1q_u8(data + i);
        uint8_t max_val = vmaxvq_u8(chunk);
        if (max_val >= 0x80) {
            uint64_t back = i;
            while (back > 0 && (data[back] & 0xC0) == 0x80) back--;
            int64_t result = scalar_utf8_find_invalid(data + back, len - back);
            if (result >= 0) return result + (int64_t)back;
            return -1;
        }
    }

    /* Scalar tail */
    uint64_t tail_start = (i > 3) ? i - 3 : 0;
    int64_t result = scalar_utf8_find_invalid(data + tail_start, len - tail_start);
    if (result >= 0) return result + (int64_t)tail_start;
    return -1;
}

#endif /* SIMD_HAS_NEON && __aarch64__ */

/* ================================================================
 * Global Dispatch Table + Scalar Fallbacks for non-UTF8 operations
 *
 * These live here so runtime_simd_dispatch.h stays header-only.
 * Each SIMD TU (search, case) upgrades its own slots lazily.
 * ================================================================ */

SimdTextDispatch g_simd_text = {0};

/* Scalar fallbacks for search/case (used as initial defaults) */
static int64_t scalar_str_search_default(const uint8_t* haystack, uint64_t hlen,
                                         const uint8_t* needle, uint64_t nlen) {
    if (nlen == 0) return 0;
    if (nlen > hlen) return -1;
    const void* result = memmem(haystack, hlen, needle, nlen);
    if (!result) return -1;
    return (int64_t)((const uint8_t*)result - haystack);
}

static int scalar_is_ascii_default(const uint8_t* data, uint64_t len) {
    for (uint64_t i = 0; i < len; i++) {
        if (data[i] >= 0x80) return 0;
    }
    return 1;
}

static void scalar_to_upper_default(const uint8_t* src, uint8_t* dst, uint64_t len) {
    for (uint64_t i = 0; i < len; i++) {
        dst[i] = (uint8_t)toupper(src[i]);
    }
}

static void scalar_to_lower_default(const uint8_t* src, uint8_t* dst, uint64_t len) {
    for (uint64_t i = 0; i < len; i++) {
        dst[i] = (uint8_t)tolower(src[i]);
    }
}

static int scalar_str_equal_default(const uint8_t* a, uint64_t alen,
                                    const uint8_t* b, uint64_t blen) {
    if (alen != blen) return 0;
    return memcmp(a, b, alen) == 0 ? 1 : 0;
}

/* Forward declaration */
static void simd_utf8_init_slots(void);

void simd_text_init(void) {
    static int initialized = 0;
    if (initialized) return;
    initialized = 1;

    /* Start with scalar defaults for all slots */
    g_simd_text.utf8_count_codepoints = scalar_utf8_count_codepoints;
    g_simd_text.utf8_validate         = scalar_utf8_validate;
    g_simd_text.utf8_find_invalid     = scalar_utf8_find_invalid;
    g_simd_text.str_search            = scalar_str_search_default;
    g_simd_text.is_ascii              = scalar_is_ascii_default;
    g_simd_text.to_upper_ascii        = scalar_to_upper_default;
    g_simd_text.to_lower_ascii        = scalar_to_lower_default;
    g_simd_text.str_equal             = scalar_str_equal_default;

    /* Upgrade UTF-8 slots to best available SIMD */
    simd_utf8_init_slots();

    /* Note: search and case TUs upgrade their own slots lazily */
}

static inline void simd_text_ensure_init(void) {
    if (!g_simd_text.utf8_count_codepoints) {
        simd_text_init();
    }
}

/* ================================================================
 * UTF-8 SIMD slot upgrading (called from simd_text_init)
 * ================================================================ */

static void simd_utf8_init_slots(void) {
    /* --- Codepoint counting --- */
#if SIMD_CAN_AVX2
    if (simd_detect_avx2()) {
        g_simd_text.utf8_count_codepoints = avx2_utf8_count_codepoints;
        g_simd_text.utf8_validate         = avx2_utf8_validate;
        g_simd_text.utf8_find_invalid     = avx2_utf8_find_invalid;
    }
#if SIMD_HAS_SSE2
    else {
        /* SSE2 is guaranteed on x86_64, use it when AVX2 is absent */
        g_simd_text.utf8_count_codepoints = sse2_utf8_count_codepoints;
        g_simd_text.utf8_validate         = sse2_utf8_validate;
        g_simd_text.utf8_find_invalid     = sse2_utf8_find_invalid;
    }
#endif
#elif SIMD_HAS_NEON && defined(__aarch64__)
    g_simd_text.utf8_count_codepoints = neon_utf8_count_codepoints;
    g_simd_text.utf8_validate         = neon_utf8_validate;
    g_simd_text.utf8_find_invalid     = neon_utf8_find_invalid;
#endif
    /* If none matched, scalar defaults from simd_text_init() remain */
}

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
    simd_text_ensure_init();
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

int64_t rt_text_count_codepoints(int64_t value) {
    return rt_text_count_codepoints_cached(value);
}

/*
 * rt_text_validate_utf8(tagged_string) -> int64_t (1=valid, 0=invalid)
 *
 * Fast path: if ASCII cache says all-ASCII, return valid immediately.
 */
int64_t rt_text_validate_utf8(int64_t value) {
    simd_text_ensure_init();
    RtCoreStringSimd* s = simd_as_string(value);
    if (!s) return 1; /* nil/non-string: vacuously valid */

    /* Fast path: all-ASCII is always valid UTF-8 */
    if (rt_str_is_ascii_cached(s)) return 1;

    return (int64_t)g_simd_text.utf8_validate(
        (const uint8_t*)s->data, s->len);
}

/*
 * rt_text_find_invalid_utf8(tagged_string) -> int64_t
 *   Returns byte offset of first invalid byte, or -1 if valid.
 */
int64_t rt_text_find_invalid_utf8(int64_t value) {
    simd_text_ensure_init();
    RtCoreStringSimd* s = simd_as_string(value);
    if (!s) return -1;

    /* Fast path: all-ASCII is always valid UTF-8 */
    if (rt_str_is_ascii_cached(s)) return -1;

    return g_simd_text.utf8_find_invalid(
        (const uint8_t*)s->data, s->len);
}
