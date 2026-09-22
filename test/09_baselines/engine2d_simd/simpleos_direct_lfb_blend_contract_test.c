#include <stdint.h>
#include <stddef.h>

typedef int64_t RuntimeValue;
typedef struct { uint32_t type; uint32_t size; } HeapHeader;
typedef struct {
    HeapHeader hdr;
    uint64_t len;
    uint64_t cap;
    RuntimeValue *items;
} RuntimeArray;

#define HEAP_ARRAY 2
static uint64_t dst_reads;
static uint64_t dst_writes;
uint64_t g_fb_addr;
uint32_t g_fb_width;
uint32_t g_fb_height;
uint32_t g_fb_pitch;
static uint32_t counted_read(volatile uint32_t *ptr) {
    dst_reads++;
    return *ptr;
}
static void counted_write(volatile uint32_t *ptr, uint32_t value) {
    dst_writes++;
    *ptr = value;
}
#define SIMPLEOS_LFB_DST_READ(ptr) counted_read(ptr)
#define SIMPLEOS_LFB_DST_WRITE(ptr, value) counted_write((ptr), (value))

static RuntimeValue *runtime_array_items(RuntimeArray *a) { return a->items; }
static RuntimeArray *_bm_pixel_array_from_abi(RuntimeValue value) {
    return (RuntimeArray *)(uintptr_t)((uint64_t)value & ~7ULL);
}
static uint32_t _bm_unbox_pixel(RuntimeValue value) {
    return (uint32_t)((uint64_t)value >> 3);
}
static uint32_t _bm_blend_pixel(uint32_t src, uint32_t dst) {
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

#define SIMPLEOS_DEFINE_RT_GUI_BLEND_SPAN8 1
#include "direct_lfb_blend_span.h"

static RuntimeValue box(uint32_t pixel) {
    return (RuntimeValue)((uint64_t)pixel << 3);
}

int main(void) {
    uint32_t registry_a[4] = {0xff010203u, 0xff112233u, 0xff445566u, 0xff778899u};
    uint32_t caller_b[4] = {0xffaabbccu, 0xffddeeffu, 0xff102030u, 0xff405060u};
    RuntimeValue slots[3] = {box(0x00112233u), box(0xffabcdefu), box(0x804080c0u)};
    RuntimeArray src = {{HEAP_ARRAY, 0}, 3, 3, slots};
    RuntimeValue src_handle = (RuntimeValue)((uintptr_t)&src | 1u);
    RuntimeValue xy = (RuntimeValue)((uint64_t)1u << 32);
    g_fb_addr = (uint64_t)(uintptr_t)registry_a;
    g_fb_width = 4;
    g_fb_height = 1;
    g_fb_pitch = 16;

    if (rt_gui_blend_span8(
            (RuntimeValue)(uintptr_t)caller_b, 4, 1, 16,
            xy, src_handle, 0, 3) != 0)
        return 1;
    if (registry_a[1] != 0xff112233u || caller_b[1] != 0xffddeeffu)
        return 2;
    if (dst_reads != 0 || dst_writes != 0) return 3;

    if (rt_gui_blend_span8(
            (RuntimeValue)(uintptr_t)registry_a, 4, 1, 20,
            xy, src_handle, 0, 3) != 0)
        return 9;
    if (dst_reads != 0 || dst_writes != 0) return 10;

    if (rt_gui_blend_span8(
            (RuntimeValue)(uintptr_t)registry_a, 4, 1, 16,
            xy, src_handle, 0, 3) != 1)
        return 4;
    if (registry_a[1] != 0xff112233u) return 5;
    if (registry_a[2] != 0xffabcdefu) return 6;
    if (registry_a[3] != _bm_blend_pixel(0x804080c0u, 0xff778899u)) return 7;
    if (dst_reads != 1 || dst_writes != 2) return 8;
    return 0;
}
