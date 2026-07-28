#include <stdint.h>
#include <immintrin.h>

static void simpleos_cpuid(uint32_t leaf, uint32_t subleaf, uint32_t *a, uint32_t *b, uint32_t *c, uint32_t *d) {
    __asm__ volatile("cpuid" : "=a"(*a), "=b"(*b), "=c"(*c), "=d"(*d) : "a"(leaf), "c"(subleaf));
}
static uint64_t simpleos_xgetbv0(void) {
    uint32_t a, d;
    __asm__ volatile("xgetbv" : "=a"(a), "=d"(d) : "c"(0));
    return ((uint64_t)d << 32) | a;
}
static int simpleos_has_avx2(void) {
    uint32_t a, b, c, d;
    simpleos_cpuid(1, 0, &a, &b, &c, &d);
    if ((c & (1u << 27)) == 0 || (c & (1u << 28)) == 0 || (simpleos_xgetbv0() & 6u) != 6u) return 0;
    simpleos_cpuid(7, 0, &a, &b, &c, &d);
    return (b & (1u << 5)) != 0;
}
static int simpleos_has_sse42(void) {
    uint32_t a, b, c, d;
    simpleos_cpuid(1, 0, &a, &b, &c, &d);
    return (c & (1u << 20)) != 0;
}
static uint64_t simpleos_arch_feature(void) { return simpleos_has_avx2() ? 2u : (simpleos_has_sse42() ? 1u : 0u); }
static uint64_t simpleos_arch_vector_width(void) { return simpleos_has_avx2() ? 256u : (simpleos_has_sse42() ? 128u : 0u); }
static uint64_t simpleos_vector_lanes(void) { return simpleos_has_avx2() ? 8u : 4u; }

__attribute__((target("avx2")))
static uint64_t simpleos_avx2_fill(uint32_t *dst, uint64_t count, uint32_t color) {
    uint64_t chunks = count / 8u, i = 0;
    __m256i value = _mm256_set1_epi32((int)color);
    for (; i < chunks * 8u; i += 8u) _mm256_storeu_si256((__m256i *)(void *)(dst + i), value);
    for (; i < count; i++) dst[i] = color;
    return chunks;
}
static uint64_t simpleos_sse_fill(uint32_t *dst, uint64_t count, uint32_t color) {
    uint64_t chunks = count / 4u, i = 0;
    __m128i value = _mm_set1_epi32((int)color);
    for (; i < chunks * 4u; i += 4u) _mm_storeu_si128((__m128i *)(void *)(dst + i), value);
    for (; i < count; i++) dst[i] = color;
    return chunks;
}
static uint64_t simpleos_vector_fill(uint32_t *dst, uint64_t count, uint32_t color) {
    return simpleos_has_avx2() ? simpleos_avx2_fill(dst, count, color) : simpleos_sse_fill(dst, count, color);
}

__attribute__((target("avx2")))
static uint64_t simpleos_avx2_copy(uint32_t *dst, const uint32_t *src, uint64_t count) {
    uint64_t chunks = count / 8u, i = 0;
    for (; i < chunks * 8u; i += 8u) {
        __m256i value = _mm256_loadu_si256((const __m256i *)(const void *)(src + i));
        _mm256_storeu_si256((__m256i *)(void *)(dst + i), value);
    }
    for (; i < count; i++) dst[i] = src[i];
    return chunks;
}
static uint64_t simpleos_sse_copy(uint32_t *dst, const uint32_t *src, uint64_t count) {
    uint64_t chunks = count / 4u, i = 0;
    for (; i < chunks * 4u; i += 4u) {
        __m128i value = _mm_loadu_si128((const __m128i *)(const void *)(src + i));
        _mm_storeu_si128((__m128i *)(void *)(dst + i), value);
    }
    for (; i < count; i++) dst[i] = src[i];
    return chunks;
}
static uint64_t simpleos_vector_copy(uint32_t *dst, const uint32_t *src, uint64_t count) {
    return simpleos_has_avx2() ? simpleos_avx2_copy(dst, src, count) : simpleos_sse_copy(dst, src, count);
}

static uint32_t simpleos_scalar_blend(uint32_t src, uint32_t dst);
__attribute__((target("avx2")))
static __m256i simpleos_avx2_div255(__m256i value) {
    return _mm256_srli_epi32(_mm256_add_epi32(_mm256_add_epi32(value, _mm256_set1_epi32(1)), _mm256_srli_epi32(value, 8)), 8);
}
__attribute__((target("avx2")))
static __m256i simpleos_avx2_blend_pixels(__m256i src, __m256i dst) {
    __m256i mask = _mm256_set1_epi32(255), full = mask;
    __m256i sa = _mm256_srli_epi32(src, 24);
    __m256i inv = _mm256_sub_epi32(full, sa);
    __m256i sr = _mm256_and_si256(_mm256_srli_epi32(src, 16), mask);
    __m256i sg = _mm256_and_si256(_mm256_srli_epi32(src, 8), mask);
    __m256i sb = _mm256_and_si256(src, mask);
    __m256i dr = _mm256_and_si256(_mm256_srli_epi32(dst, 16), mask);
    __m256i dg = _mm256_and_si256(_mm256_srli_epi32(dst, 8), mask);
    __m256i db = _mm256_and_si256(dst, mask);
    __m256i r = simpleos_avx2_div255(_mm256_add_epi32(_mm256_mullo_epi32(sr, sa), _mm256_mullo_epi32(dr, inv)));
    __m256i g = simpleos_avx2_div255(_mm256_add_epi32(_mm256_mullo_epi32(sg, sa), _mm256_mullo_epi32(dg, inv)));
    __m256i b = simpleos_avx2_div255(_mm256_add_epi32(_mm256_mullo_epi32(sb, sa), _mm256_mullo_epi32(db, inv)));
    return _mm256_or_si256(_mm256_set1_epi32((int)0xff000000u), _mm256_or_si256(_mm256_slli_epi32(r, 16), _mm256_or_si256(_mm256_slli_epi32(g, 8), b)));
}
__attribute__((target("avx2")))
static uint64_t simpleos_avx2_blend(uint32_t *dst, const uint32_t *src, uint64_t count) {
    uint64_t chunks = count / 8u, i = 0;
    for (; i < chunks * 8u; i += 8u) {
        __m256i s = _mm256_loadu_si256((const __m256i *)(const void *)(src + i));
        __m256i d = _mm256_loadu_si256((const __m256i *)(const void *)(dst + i));
        _mm256_storeu_si256((__m256i *)(void *)(dst + i), simpleos_avx2_blend_pixels(s, d));
    }
    for (; i < count; i++) dst[i] = simpleos_scalar_blend(src[i], dst[i]);
    return chunks;
}
static __m128i simpleos_sse_div255(__m128i value) {
    return _mm_srli_epi32(_mm_add_epi32(_mm_add_epi32(value, _mm_set1_epi32(1)), _mm_srli_epi32(value, 8)), 8);
}
static __m128i simpleos_sse_blend_pixels(__m128i src, __m128i dst) {
    __m128i mask = _mm_set1_epi32(255), sa = _mm_srli_epi32(src, 24);
    __m128i inv = _mm_sub_epi32(mask, sa);
    __m128i sr = _mm_and_si128(_mm_srli_epi32(src, 16), mask);
    __m128i sg = _mm_and_si128(_mm_srli_epi32(src, 8), mask);
    __m128i sb = _mm_and_si128(src, mask);
    __m128i dr = _mm_and_si128(_mm_srli_epi32(dst, 16), mask);
    __m128i dg = _mm_and_si128(_mm_srli_epi32(dst, 8), mask);
    __m128i db = _mm_and_si128(dst, mask);
    __m128i r = simpleos_sse_div255(_mm_add_epi32(_mm_mullo_epi32(sr, sa), _mm_mullo_epi32(dr, inv)));
    __m128i g = simpleos_sse_div255(_mm_add_epi32(_mm_mullo_epi32(sg, sa), _mm_mullo_epi32(dg, inv)));
    __m128i b = simpleos_sse_div255(_mm_add_epi32(_mm_mullo_epi32(sb, sa), _mm_mullo_epi32(db, inv)));
    return _mm_or_si128(_mm_set1_epi32((int)0xff000000u), _mm_or_si128(_mm_slli_epi32(r, 16), _mm_or_si128(_mm_slli_epi32(g, 8), b)));
}
static uint64_t simpleos_sse_blend(uint32_t *dst, const uint32_t *src, uint64_t count) {
    uint64_t chunks = count / 4u, i = 0;
    for (; i < chunks * 4u; i += 4u) {
        __m128i s = _mm_loadu_si128((const __m128i *)(const void *)(src + i));
        __m128i d = _mm_loadu_si128((const __m128i *)(const void *)(dst + i));
        _mm_storeu_si128((__m128i *)(void *)(dst + i), simpleos_sse_blend_pixels(s, d));
    }
    for (; i < count; i++) dst[i] = simpleos_scalar_blend(src[i], dst[i]);
    return chunks;
}
static uint64_t simpleos_vector_blend(uint32_t *dst, const uint32_t *src, uint64_t count) {
    return simpleos_has_avx2() ? simpleos_avx2_blend(dst, src, count) : simpleos_sse_blend(dst, src, count);
}

#define SIMPLEOS_SIMD_PREFIX rt_simpleos_x86_engine2d_simd
#include "../../../compositor/engine2d_simd_intrinsic_owner.inc"
