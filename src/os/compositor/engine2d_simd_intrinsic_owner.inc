/* Shared freestanding ABI implementation. Architecture files provide real
 * vector_fill/vector_copy/vector_blend plus feature/width/lanes. */
#include <stdint.h>
#include <stddef.h>

#define SIMD_CAT2(a, b) a##b
#define SIMD_CAT(a, b) SIMD_CAT2(a, b)
#define SIMD_OWNER(name) SIMD_CAT(SIMPLEOS_SIMD_PREFIX, name)

static uint64_t simpleos_simd_metrics[7][9];

static uint32_t simpleos_scalar_blend(uint32_t src, uint32_t dst) {
    uint32_t sa = src >> 24;
    if (sa == 255u) return src;
    if (sa == 0u) return dst;
    uint32_t inv = 255u - sa;
    uint32_t da = dst >> 24;
    uint32_t dw = (da * inv) / 255u;
    uint32_t oa = sa + dw;
    uint32_t r = ((((src >> 16) & 255u) * sa) + (((dst >> 16) & 255u) * dw)) / oa;
    uint32_t g = ((((src >> 8) & 255u) * sa) + (((dst >> 8) & 255u) * dw)) / oa;
    uint32_t b = (((src & 255u) * sa) + ((dst & 255u) * dw)) / oa;
    return (oa << 24) | (r << 16) | (g << 8) | b;
}

static uint64_t simpleos_checksum(const uint32_t *pixels, uint64_t count) {
    uint64_t hash = 1469598103934665603ull;
    for (uint64_t i = 0; i < count; i++) {
        hash ^= pixels[i];
        hash *= 1099511628211ull;
    }
    return hash == 0 ? 1 : hash;
}

static uint64_t simpleos_mismatches(
    const uint32_t *actual, const uint32_t *expected, uint64_t count
) {
    uint64_t mismatches = 0;
    for (uint64_t i = 0; i < count; i++) mismatches += actual[i] != expected[i];
    return mismatches;
}

static void simpleos_record(
    uint32_t operation, uint64_t chunks, uint64_t count,
    const uint32_t *actual, const uint32_t *expected
) {
    uint64_t lanes = simpleos_vector_lanes();
    simpleos_simd_metrics[operation][1] = 1;
    simpleos_simd_metrics[operation][2] = chunks;
    simpleos_simd_metrics[operation][3] = chunks * lanes;
    simpleos_simd_metrics[operation][4] = count - chunks * lanes;
    simpleos_simd_metrics[operation][5] = chunks == 0 ? 1 : 0;
    simpleos_simd_metrics[operation][6] = simpleos_checksum(expected, count);
    simpleos_simd_metrics[operation][7] = simpleos_checksum(actual, count);
    simpleos_simd_metrics[operation][8] = simpleos_mismatches(actual, expected, count);
}

static void simpleos_init_copy_source(uint32_t *src, uint64_t count) {
    for (uint64_t i = 0; i < count; i++)
        src[i] = 0xff000000u | ((uint32_t)(i * 37u) & 0x00ffffffu);
}

static void simpleos_init_blend(
    uint32_t *dst, uint32_t *expected, uint32_t *src, uint64_t count, int edge
) {
    for (uint64_t i = 0; i < count; i++) {
        uint32_t alpha = edge ? ((i & 1u) ? 255u : 0u) : (uint32_t)((i * 53u + 17u) & 255u);
        dst[i] = 0xff000000u | ((0x00204060u ^ (uint32_t)(i * 97u)) & 0x00ffffffu);
        expected[i] = dst[i];
        src[i] = (alpha << 24) | ((uint32_t)(i * 29u) & 0x00ffffffu);
    }
}

uint64_t SIMD_OWNER(_owner_linked)(void) { return 1; }
uint64_t SIMD_OWNER(_feature)(void) { return simpleos_arch_feature(); }
uint64_t SIMD_OWNER(_vector_width)(void) { return simpleos_arch_vector_width(); }

uint64_t SIMD_OWNER(_fill)(
    uint64_t dst_addr, uint64_t expected_addr, uint64_t count, uint32_t color
) {
    uint32_t *dst = (uint32_t *)(uintptr_t)dst_addr;
    uint32_t *expected = (uint32_t *)(uintptr_t)expected_addr;
    for (uint64_t i = 0; i < count; i++) expected[i] = color;
    uint64_t chunks = simpleos_vector_fill(dst, count, color);
    simpleos_record(1u, chunks, count, dst, expected);
    return chunks;
}

uint64_t SIMD_OWNER(_copy)(
    uint64_t dst_addr, uint64_t expected_addr, uint64_t src_addr, uint64_t count
) {
    uint32_t *dst = (uint32_t *)(uintptr_t)dst_addr;
    uint32_t *expected = (uint32_t *)(uintptr_t)expected_addr;
    uint32_t *src = (uint32_t *)(uintptr_t)src_addr;
    simpleos_init_copy_source(src, count);
    for (uint64_t i = 0; i < count; i++) expected[i] = src[i];
    uint64_t chunks = simpleos_vector_copy(dst, src, count);
    simpleos_record(2u, chunks, count, dst, expected);
    return chunks;
}

static uint64_t simpleos_alpha_operation(
    uint32_t operation, uint64_t dst_addr, uint64_t expected_addr,
    uint64_t src_addr, uint64_t count, int edge
) {
    uint32_t *dst = (uint32_t *)(uintptr_t)dst_addr;
    uint32_t *expected = (uint32_t *)(uintptr_t)expected_addr;
    uint32_t *src = (uint32_t *)(uintptr_t)src_addr;
    simpleos_init_blend(dst, expected, src, count, edge);
    for (uint64_t i = 0; i < count; i++) expected[i] = simpleos_scalar_blend(src[i], expected[i]);
    uint64_t chunks = simpleos_vector_blend(dst, src, count);
    simpleos_record(operation, chunks, count, dst, expected);
    return chunks;
}

uint64_t SIMD_OWNER(_alpha)(uint64_t dst, uint64_t expected, uint64_t src, uint64_t count) {
    return simpleos_alpha_operation(3u, dst, expected, src, count, 0);
}
uint64_t SIMD_OWNER(_alpha_edge)(uint64_t dst, uint64_t expected, uint64_t src, uint64_t count) {
    return simpleos_alpha_operation(4u, dst, expected, src, count, 1);
}
uint64_t SIMD_OWNER(_scroll)(uint64_t dst, uint64_t expected, uint64_t src, uint64_t count) {
    uint32_t *d = (uint32_t *)(uintptr_t)dst;
    uint32_t *e = (uint32_t *)(uintptr_t)expected;
    uint32_t *s = (uint32_t *)(uintptr_t)src;
    simpleos_init_copy_source(s, count);
    for (uint64_t i = 0; i < count; i++) e[i] = s[i];
    uint64_t chunks = simpleos_vector_copy(d, s, count);
    simpleos_record(5u, chunks, count, d, e);
    return chunks;
}
uint64_t SIMD_OWNER(_diagram)(uint64_t dst, uint64_t expected, uint64_t src, uint64_t count) {
    uint32_t *d = (uint32_t *)(uintptr_t)dst;
    uint32_t *e = (uint32_t *)(uintptr_t)expected;
    uint32_t *s = (uint32_t *)(uintptr_t)src;
    for (uint64_t i = 0; i < count; i++) e[i] = 0xff102030u;
    uint64_t fill_chunks = simpleos_vector_fill(d, count, 0xff102030u);
    simpleos_init_blend(d, e, s, count, 0);
    for (uint64_t i = 0; i < count; i++) e[i] = simpleos_scalar_blend(s[i], e[i]);
    uint64_t blend_chunks = simpleos_vector_blend(d, s, count);
    uint64_t chunks = fill_chunks < blend_chunks ? fill_chunks : blend_chunks;
    simpleos_record(6u, chunks, count, d, e);
    return chunks;
}
uint64_t SIMD_OWNER(_metric)(uint32_t operation, uint32_t metric) {
    if (operation < 1u || operation > 6u || metric < 1u || metric > 8u) return 0;
    return simpleos_simd_metrics[operation][metric];
}

#undef SIMD_OWNER
#undef SIMD_CAT
#undef SIMD_CAT2
