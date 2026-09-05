/*
 * SIMD ASCII Case Operations — is_ascii, to_upper, to_lower
 *
 * Wave 1: scalar stubs with reserved-field caching for is_ascii.
 * Wave 2: SSE2 / AVX2 / NEON fast paths.
 *
 * Build: cc -c -fPIC -O2 -std=gnu11 -I. runtime_simd_case.c
 */

#include "runtime_simd_dispatch.h"
#include <stdlib.h>

/* x86 intrinsics — guarded by platform macro */
#if SIMD_HAS_X86
#  include <immintrin.h>
#endif

/* ARM NEON intrinsics — aarch64 only (vmaxvq_u8 is not available on armv7) */
#if defined(__aarch64__) || defined(_M_ARM64)
#  include <arm_neon.h>
#endif

/* ================================================================
 * Reserved-Field ASCII Cache Helpers
 * ================================================================ */

static inline void cache_ascii_flag(RtCoreStringSimd* s, int is_ascii) {
    if (!s) return;
    if (is_ascii)
        s->reserved |= SIMD_CACHE_FLAG_IS_ASCII;
    /* Non-ASCII: don't cache (positive-only flag per spec) */
}

static inline int cached_ascii_flag(const RtCoreStringSimd* s) {
    if (!s) return -1;
    if (s->reserved & SIMD_CACHE_FLAG_IS_ASCII) return 1;
    return -1; /* unknown (could be ASCII or not) */
}

/* ================================================================
 * Scalar Kernels
 * ================================================================ */

static int scalar_is_ascii(const uint8_t* data, uint64_t len) {
    for (uint64_t i = 0; i < len; i++) {
        if (data[i] >= 0x80) return 0;
    }
    return 1;
}

static void scalar_to_lower_ascii(const uint8_t* src, uint8_t* dst, uint64_t len) {
    for (uint64_t i = 0; i < len; i++) {
        uint8_t c = src[i];
        if (c >= 'A' && c <= 'Z')
            dst[i] = c | 0x20;
        else
            dst[i] = c;
    }
}

static void scalar_to_upper_ascii(const uint8_t* src, uint8_t* dst, uint64_t len) {
    for (uint64_t i = 0; i < len; i++) {
        uint8_t c = src[i];
        if (c >= 'a' && c <= 'z')
            dst[i] = c & 0xDF;
        else
            dst[i] = c;
    }
}

/* ================================================================
 * SSE2 Kernels (x86_64 — SSE2 is baseline)
 * ================================================================ */

#if SIMD_HAS_SSE2

__attribute__((target("sse2")))
static int sse2_is_ascii(const uint8_t* data, uint64_t len) {
    uint64_t i = 0;
    /* Process 16 bytes at a time */
    for (; i + 16 <= len; i += 16) {
        __m128i chunk = _mm_loadu_si128((const __m128i*)(data + i));
        int mask = _mm_movemask_epi8(chunk);
        if (mask != 0) return 0;
    }
    /* Scalar tail */
    for (; i < len; i++) {
        if (data[i] >= 0x80) return 0;
    }
    return 1;
}

__attribute__((target("sse2")))
static void sse2_to_lower_ascii(const uint8_t* src, uint8_t* dst, uint64_t len) {
    uint64_t i = 0;
    const __m128i lower_bound = _mm_set1_epi8('A' - 1);   /* 64 */
    const __m128i upper_bound = _mm_set1_epi8('Z' + 1);   /* 91 */
    const __m128i delta = _mm_set1_epi8(0x20);

    for (; i + 16 <= len; i += 16) {
        __m128i chunk = _mm_loadu_si128((const __m128i*)(src + i));
        __m128i ge_A = _mm_cmpgt_epi8(chunk, lower_bound);
        __m128i le_Z = _mm_cmplt_epi8(chunk, upper_bound);
        __m128i in_range = _mm_and_si128(ge_A, le_Z);
        __m128i add = _mm_and_si128(in_range, delta);
        __m128i result = _mm_or_si128(chunk, add);
        _mm_storeu_si128((__m128i*)(dst + i), result);
    }
    /* Scalar tail */
    for (; i < len; i++) {
        uint8_t c = src[i];
        if (c >= 'A' && c <= 'Z')
            dst[i] = c | 0x20;
        else
            dst[i] = c;
    }
}

__attribute__((target("sse2")))
static void sse2_to_upper_ascii(const uint8_t* src, uint8_t* dst, uint64_t len) {
    uint64_t i = 0;
    const __m128i lower_bound = _mm_set1_epi8('a' - 1);   /* 96 */
    const __m128i upper_bound = _mm_set1_epi8('z' + 1);   /* 123 */

    for (; i + 16 <= len; i += 16) {
        __m128i chunk = _mm_loadu_si128((const __m128i*)(src + i));
        __m128i ge_a = _mm_cmpgt_epi8(chunk, lower_bound);
        __m128i le_z = _mm_cmplt_epi8(chunk, upper_bound);
        __m128i in_range = _mm_and_si128(ge_a, le_z);
        /* For bytes in range: AND with 0xDF to clear bit 5
         * For bytes out of range: keep original
         * result = (chunk & mask_clear) where in_range, else chunk
         * = chunk & (in_range ? 0xDF : 0xFF)
         * = chunk & (0xFF ^ (in_range & 0x20))
         * = chunk & ~(in_range & 0x20)
         */
        __m128i bit5 = _mm_and_si128(in_range, _mm_set1_epi8(0x20));
        __m128i result = _mm_andnot_si128(bit5, chunk);
        _mm_storeu_si128((__m128i*)(dst + i), result);
    }
    /* Scalar tail */
    for (; i < len; i++) {
        uint8_t c = src[i];
        if (c >= 'a' && c <= 'z')
            dst[i] = c & 0xDF;
        else
            dst[i] = c;
    }
}

#endif /* SIMD_HAS_SSE2 */

/* ================================================================
 * AVX2 Kernels (runtime-detected on x86_64)
 * ================================================================ */

#if SIMD_CAN_AVX2

__attribute__((target("avx2")))
static int avx2_is_ascii(const uint8_t* data, uint64_t len) {
    uint64_t i = 0;
    /* Process 32 bytes at a time */
    for (; i + 32 <= len; i += 32) {
        __m256i chunk = _mm256_loadu_si256((const __m256i*)(data + i));
        int mask = _mm256_movemask_epi8(chunk);
        if (mask != 0) return 0;
    }
    /* SSE2 cleanup for 16-byte remainder */
    for (; i + 16 <= len; i += 16) {
        __m128i chunk = _mm_loadu_si128((const __m128i*)(data + i));
        int mask = _mm_movemask_epi8(chunk);
        if (mask != 0) return 0;
    }
    /* Scalar tail */
    for (; i < len; i++) {
        if (data[i] >= 0x80) return 0;
    }
    return 1;
}

__attribute__((target("avx2")))
static void avx2_to_lower_ascii(const uint8_t* src, uint8_t* dst, uint64_t len) {
    uint64_t i = 0;
    const __m256i lower_bound = _mm256_set1_epi8('A' - 1);
    const __m256i upper_bound = _mm256_set1_epi8('Z' + 1);
    const __m256i delta = _mm256_set1_epi8(0x20);

    for (; i + 32 <= len; i += 32) {
        __m256i chunk = _mm256_loadu_si256((const __m256i*)(src + i));
        __m256i ge_A = _mm256_cmpgt_epi8(chunk, lower_bound);
        __m256i le_Z = _mm256_cmpgt_epi8(upper_bound, chunk);
        __m256i in_range = _mm256_and_si256(ge_A, le_Z);
        __m256i add = _mm256_and_si256(in_range, delta);
        __m256i result = _mm256_or_si256(chunk, add);
        _mm256_storeu_si256((__m256i*)(dst + i), result);
    }
    /* Scalar tail */
    for (; i < len; i++) {
        uint8_t c = src[i];
        if (c >= 'A' && c <= 'Z')
            dst[i] = c | 0x20;
        else
            dst[i] = c;
    }
}

__attribute__((target("avx2")))
static void avx2_to_upper_ascii(const uint8_t* src, uint8_t* dst, uint64_t len) {
    uint64_t i = 0;
    const __m256i lower_bound = _mm256_set1_epi8('a' - 1);
    const __m256i upper_bound = _mm256_set1_epi8('z' + 1);
    const __m256i bit5 = _mm256_set1_epi8(0x20);

    for (; i + 32 <= len; i += 32) {
        __m256i chunk = _mm256_loadu_si256((const __m256i*)(src + i));
        __m256i ge_a = _mm256_cmpgt_epi8(chunk, lower_bound);
        __m256i le_z = _mm256_cmpgt_epi8(upper_bound, chunk);
        __m256i in_range = _mm256_and_si256(ge_a, le_z);
        __m256i clear = _mm256_and_si256(in_range, bit5);
        __m256i result = _mm256_andnot_si256(clear, chunk);
        _mm256_storeu_si256((__m256i*)(dst + i), result);
    }
    /* Scalar tail */
    for (; i < len; i++) {
        uint8_t c = src[i];
        if (c >= 'a' && c <= 'z')
            dst[i] = c & 0xDF;
        else
            dst[i] = c;
    }
}

#endif /* SIMD_CAN_AVX2 */

/* ================================================================
 * NEON Kernels (aarch64 — NEON is baseline)
 * ================================================================ */

#if defined(__aarch64__) || defined(_M_ARM64)

static int neon_is_ascii(const uint8_t* data, uint64_t len) {
    uint64_t i = 0;
    /* Process 16 bytes at a time */
    for (; i + 16 <= len; i += 16) {
        uint8x16_t chunk = vld1q_u8(data + i);
        uint8_t max_val = vmaxvq_u8(chunk);
        if (max_val >= 0x80) return 0;
    }
    /* Scalar tail */
    for (; i < len; i++) {
        if (data[i] >= 0x80) return 0;
    }
    return 1;
}

static void neon_to_lower_ascii(const uint8_t* src, uint8_t* dst, uint64_t len) {
    uint64_t i = 0;
    const uint8x16_t vA = vdupq_n_u8('A');
    const uint8x16_t vZ = vdupq_n_u8('Z');
    const uint8x16_t v20 = vdupq_n_u8(0x20);

    for (; i + 16 <= len; i += 16) {
        uint8x16_t chunk = vld1q_u8(src + i);
        uint8x16_t ge_A = vcgeq_u8(chunk, vA);
        uint8x16_t le_Z = vcleq_u8(chunk, vZ);
        uint8x16_t in_range = vandq_u8(ge_A, le_Z);
        uint8x16_t delta = vandq_u8(in_range, v20);
        uint8x16_t result = vorrq_u8(chunk, delta);
        vst1q_u8(dst + i, result);
    }
    /* Scalar tail */
    for (; i < len; i++) {
        uint8_t c = src[i];
        if (c >= 'A' && c <= 'Z')
            dst[i] = c | 0x20;
        else
            dst[i] = c;
    }
}

static void neon_to_upper_ascii(const uint8_t* src, uint8_t* dst, uint64_t len) {
    uint64_t i = 0;
    const uint8x16_t va = vdupq_n_u8('a');
    const uint8x16_t vz = vdupq_n_u8('z');
    const uint8x16_t v20 = vdupq_n_u8(0x20);

    for (; i + 16 <= len; i += 16) {
        uint8x16_t chunk = vld1q_u8(src + i);
        uint8x16_t ge_a = vcgeq_u8(chunk, va);
        uint8x16_t le_z = vcleq_u8(chunk, vz);
        uint8x16_t in_range = vandq_u8(ge_a, le_z);
        uint8x16_t bit5 = vandq_u8(in_range, v20);
        uint8x16_t result = vbicq_u8(chunk, bit5);
        vst1q_u8(dst + i, result);
    }
    /* Scalar tail */
    for (; i < len; i++) {
        uint8_t c = src[i];
        if (c >= 'a' && c <= 'z')
            dst[i] = c & 0xDF;
        else
            dst[i] = c;
    }
}

#endif /* __aarch64__ */

/* ================================================================
 * Dispatch Slot Upgrade — called via constructor to wire best kernels
 * ================================================================ */

__attribute__((constructor(200)))
static void simd_case_init(void) {
    /* Ensure base dispatch table is initialized first */
    simd_text_init();

    /* Always install our scalar kernels (they avoid locale-dependent
     * toupper/tolower from <ctype.h> used in the dispatch.c fallbacks) */
    g_simd_text.is_ascii       = scalar_is_ascii;
    g_simd_text.to_lower_ascii = scalar_to_lower_ascii;
    g_simd_text.to_upper_ascii = scalar_to_upper_ascii;

#if SIMD_HAS_SSE2
    /* SSE2 is baseline on all x86_64 — always upgrade */
    g_simd_text.is_ascii       = sse2_is_ascii;
    g_simd_text.to_lower_ascii = sse2_to_lower_ascii;
    g_simd_text.to_upper_ascii = sse2_to_upper_ascii;
#endif

#if SIMD_CAN_AVX2
    /* AVX2 requires runtime detection */
    if (simd_detect_avx2()) {
        g_simd_text.is_ascii       = avx2_is_ascii;
        g_simd_text.to_lower_ascii = avx2_to_lower_ascii;
        g_simd_text.to_upper_ascii = avx2_to_upper_ascii;
    }
#endif

#if defined(__aarch64__) || defined(_M_ARM64)
    /* NEON is mandatory on aarch64 */
    g_simd_text.is_ascii       = neon_is_ascii;
    g_simd_text.to_lower_ascii = neon_to_lower_ascii;
    g_simd_text.to_upper_ascii = neon_to_upper_ascii;
#endif
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
