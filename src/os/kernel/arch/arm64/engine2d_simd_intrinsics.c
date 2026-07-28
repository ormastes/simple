#include <stdint.h>
#include <arm_neon.h>

static uint64_t simpleos_arch_feature(void) { return 3u; }
static uint64_t simpleos_arch_vector_width(void) { return 128u; }
static uint64_t simpleos_vector_lanes(void) { return 4u; }
static uint64_t simpleos_vector_fill(uint32_t *dst, uint64_t count, uint32_t color) {
    uint64_t chunks = count / 4u, i = 0;
    uint32x4_t value = vdupq_n_u32(color);
    for (; i < chunks * 4u; i += 4u) vst1q_u32(dst + i, value);
    for (; i < count; i++) dst[i] = color;
    return chunks;
}
static uint64_t simpleos_vector_copy(uint32_t *dst, const uint32_t *src, uint64_t count) {
    uint64_t chunks = count / 4u, i = 0;
    for (; i < chunks * 4u; i += 4u) vst1q_u32(dst + i, vld1q_u32(src + i));
    for (; i < count; i++) dst[i] = src[i];
    return chunks;
}
static uint32_t simpleos_scalar_blend(uint32_t src, uint32_t dst);
static uint32x4_t simpleos_neon_div255(uint32x4_t value) {
    return vshrq_n_u32(vaddq_u32(vaddq_u32(value, vdupq_n_u32(1u)), vshrq_n_u32(value, 8)), 8);
}
static uint32x4_t simpleos_neon_blend_pixels(uint32x4_t src, uint32x4_t dst) {
    uint32x4_t mask = vdupq_n_u32(255u);
    uint32x4_t sa = vshrq_n_u32(src, 24);
    uint32x4_t inv = vsubq_u32(mask, sa);
    uint32x4_t sr = vandq_u32(vshrq_n_u32(src, 16), mask);
    uint32x4_t sg = vandq_u32(vshrq_n_u32(src, 8), mask);
    uint32x4_t sb = vandq_u32(src, mask);
    uint32x4_t dr = vandq_u32(vshrq_n_u32(dst, 16), mask);
    uint32x4_t dg = vandq_u32(vshrq_n_u32(dst, 8), mask);
    uint32x4_t db = vandq_u32(dst, mask);
    uint32x4_t r = simpleos_neon_div255(vaddq_u32(vmulq_u32(sr, sa), vmulq_u32(dr, inv)));
    uint32x4_t g = simpleos_neon_div255(vaddq_u32(vmulq_u32(sg, sa), vmulq_u32(dg, inv)));
    uint32x4_t b = simpleos_neon_div255(vaddq_u32(vmulq_u32(sb, sa), vmulq_u32(db, inv)));
    return vorrq_u32(vdupq_n_u32(0xff000000u), vorrq_u32(vshlq_n_u32(r, 16), vorrq_u32(vshlq_n_u32(g, 8), b)));
}
static uint64_t simpleos_vector_blend(uint32_t *dst, const uint32_t *src, uint64_t count) {
    uint64_t chunks = count / 4u, i = 0;
    for (; i < chunks * 4u; i += 4u) {
        vst1q_u32(dst + i, simpleos_neon_blend_pixels(vld1q_u32(src + i), vld1q_u32(dst + i)));
    }
    for (; i < count; i++) dst[i] = simpleos_scalar_blend(src[i], dst[i]);
    return chunks;
}

#define SIMPLEOS_SIMD_PREFIX rt_simpleos_neon_engine2d_simd
#include "../../../compositor/engine2d_simd_intrinsic_owner.inc"
