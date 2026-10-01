#include <stdint.h>

typedef intptr_t RuntimeValue;

extern uint64_t g_fb_addr;
extern uint64_t g_fb_w;
extern uint64_t g_fb_h;
extern RuntimeValue rt_gui_fill4(
    RuntimeValue xy, RuntimeValue wh, RuntimeValue color, RuntimeValue unused);
extern RuntimeValue rt_gui_simd_fill_enabled(void);
extern RuntimeValue rt_gui_simd_fill_hits(void);
extern RuntimeValue rt_gui_simd_fill_chunks(void);
extern RuntimeValue rt_gui_simd_fill_tail_pixels(void);
extern RuntimeValue rt_gui_simd_fill_scalar_parity(void);

static uint32_t framebuffer[8 * 4] __attribute__((aligned(64)));

static __attribute__((noreturn)) void probe_exit(long status)
{
    register long a0 __asm__("a0") = status;
    register long a7 __asm__("a7") = 93;
    __asm__ volatile("ecall" : : "r"(a0), "r"(a7) : "memory");
    __builtin_unreachable();
}

void _start(void)
{
    const uint32_t sentinel = 0x11223344U;
    const uint32_t color = 0xff3a7bc1U;
    for (uint32_t i = 0; i < 32U; i++) framebuffer[i] = sentinel;
    g_fb_addr = (uint64_t)(uintptr_t)framebuffer;
    g_fb_w = 8U;
    g_fb_h = 4U;

    const RuntimeValue xy = ((RuntimeValue)1U << 32) | 1U;
    const RuntimeValue wh = ((RuntimeValue)6U << 32) | 2U;
    rt_gui_fill4(xy, wh, (RuntimeValue)color, 0);
    const uint32_t edge_color = 0xff55aa33U;
    rt_gui_fill4(((RuntimeValue)6U << 32) | 3U,
                 ((RuntimeValue)6U << 32) | 2U,
                 (RuntimeValue)edge_color, 0);
    rt_gui_fill4(((RuntimeValue)8U << 32) | 4U,
                 ((RuntimeValue)4U << 32) | 4U,
                 (RuntimeValue)0xffffffffU, 0);

    uint32_t mismatches = 0;
    for (uint32_t y = 0; y < 4U; y++) {
        for (uint32_t x = 0; x < 8U; x++) {
            uint32_t expected = sentinel;
            if (x >= 1U && x < 7U && y >= 1U && y < 3U) expected = color;
            if (x >= 6U && y == 3U) expected = edge_color;
            if (framebuffer[y * 8U + x] != expected) mismatches++;
        }
    }
    if (rt_gui_simd_fill_enabled() != 1 ||
        rt_gui_simd_fill_hits() != 2 ||
        rt_gui_simd_fill_chunks() <= 0 ||
        rt_gui_simd_fill_tail_pixels() != 0 ||
        rt_gui_simd_fill_scalar_parity() != 1 || mismatches != 0) {
        probe_exit(1);
    }
    probe_exit(0);
}
