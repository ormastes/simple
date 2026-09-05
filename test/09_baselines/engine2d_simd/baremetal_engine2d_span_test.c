#include <stdint.h>
#include <stddef.h>

typedef int64_t RuntimeValue;

typedef struct {
    uint8_t type;
    uint8_t gc_flags;
    uint16_t reserved;
    uint32_t size;
} HeapHeader;

typedef struct {
    HeapHeader hdr;
    uint64_t len;
    uint64_t cap;
    RuntimeValue *items;
} RuntimeArray;

RuntimeValue rt_engine2d_simd_blend_span_u32(
    RuntimeValue dst, int64_t dst_offset, RuntimeValue src,
    int64_t src_offset, int64_t count);
RuntimeValue rt_engine2d_simd_blend_const_span_u32(
    RuntimeValue dst, int64_t offset, int64_t count, int64_t color);

static RuntimeValue box(uint32_t pixel) {
    return (RuntimeValue)((uint64_t)pixel << 3);
}

static uint32_t unbox(RuntimeValue value) {
    return (uint32_t)((uint64_t)value >> 3);
}

static RuntimeValue handle(RuntimeArray *array) {
    return (RuntimeValue)((uintptr_t)array | 1u);
}

static uint32_t oracle(uint32_t src, uint32_t dst) {
    uint32_t sa = src >> 24;
    if (sa == 255u) return src;
    if (sa == 0u) return dst;
    uint32_t da = dst >> 24;
    uint32_t inv = 255u - sa;
    uint32_t dw = (da * inv) / 255u;
    uint32_t oa = sa + dw;
    uint32_t r = ((((src >> 16) & 255u) * sa) +
                  (((dst >> 16) & 255u) * dw)) / oa;
    uint32_t g = ((((src >> 8) & 255u) * sa) +
                  (((dst >> 8) & 255u) * dw)) / oa;
    uint32_t b = (((src & 255u) * sa) + ((dst & 255u) * dw)) / oa;
    return (oa << 24) | (r << 16) | (g << 8) | b;
}

static int expect_pixels(RuntimeValue *actual, const uint32_t *expected,
                         int count) {
    for (int i = 0; i < count; i++) {
        if (unbox(actual[i]) != expected[i]) return 0;
    }
    return 1;
}

int main(void) {
    RuntimeValue slots[6];
    uint32_t initial[6] = {
        0x80102030u, 0xff203040u, 0x40305070u,
        0xff405060u, 0x00506070u, 0xff607080u
    };
    for (int i = 0; i < 6; i++) slots[i] = box(initial[i]);
    RuntimeArray array = {{2, 0, 0, 0}, 6, 6, slots};
    RuntimeValue h = handle(&array);

    uint32_t overlap_expected[6];
    for (int i = 0; i < 6; i++) overlap_expected[i] = initial[i];
    for (int i = 3; i >= 0; i--)
        overlap_expected[i + 1] = oracle(initial[i], initial[i + 1]);
    if (rt_engine2d_simd_blend_span_u32(h, 1, h, 0, 4) != h) return 1;
    if (!expect_pixels(slots, overlap_expected, 6)) return 2;

    for (int i = 0; i < 6; i++) slots[i] = box(initial[i]);
    uint32_t forward_expected[6];
    for (int i = 0; i < 6; i++) forward_expected[i] = initial[i];
    for (int i = 0; i < 4; i++)
        forward_expected[i] = oracle(initial[i + 1], initial[i]);
    if (rt_engine2d_simd_blend_span_u32(h, 0, h, 1, 4) != h) return 11;
    if (!expect_pixels(slots, forward_expected, 6)) return 12;

    uint32_t before_invalid[6];
    for (int i = 0; i < 6; i++) before_invalid[i] = unbox(slots[i]);
    if (rt_engine2d_simd_blend_span_u32(h, -1, h, 0, 2) != h) return 3;
    if (!expect_pixels(slots, before_invalid, 6)) return 4;

    if (rt_engine2d_simd_blend_const_span_u32(
            h, 2, 2, (int64_t)0xffa0b0c0u) != h) return 5;
    uint32_t opaque_expected[6];
    for (int i = 0; i < 6; i++) opaque_expected[i] = before_invalid[i];
    opaque_expected[2] = 0xffa0b0c0u;
    opaque_expected[3] = 0xffa0b0c0u;
    if (!expect_pixels(slots, opaque_expected, 6)) return 6;

    uint32_t transparent_before[6];
    for (int i = 0; i < 6; i++) transparent_before[i] = unbox(slots[i]);
    if (rt_engine2d_simd_blend_const_span_u32(h, 0, 6, 0x00112233u) != h)
        return 7;
    if (!expect_pixels(slots, transparent_before, 6)) return 8;

    uint32_t translucent_expected[6];
    for (int i = 0; i < 6; i++)
        translucent_expected[i] = oracle(0x806080a0u, transparent_before[i]);
    if (rt_engine2d_simd_blend_const_span_u32(
            h, 0, 99, (int64_t)0x806080a0u) != h) return 9;
    if (!expect_pixels(slots, translucent_expected, 6)) return 10;
    return 0;
}
