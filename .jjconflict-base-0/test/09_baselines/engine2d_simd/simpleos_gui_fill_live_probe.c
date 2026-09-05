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

/* Keep a guard row so the height-bound assertion is also memory-safe. */
static uint32_t framebuffer[8 * 5] __attribute__((aligned(64)));

static __attribute__((noreturn)) void probe_exit(long status)
{
#if defined(__x86_64__)
    register long rax __asm__("rax") = 60;
    register long rdi __asm__("rdi") = status;
    __asm__ volatile("syscall" : : "r"(rax), "r"(rdi) : "rcx", "r11", "memory");
#elif defined(__aarch64__)
    register long x0 __asm__("x0") = status;
    register long x8 __asm__("x8") = 93;
    __asm__ volatile("svc #0" : : "r"(x0), "r"(x8) : "memory");
#else
#error unsupported probe architecture
#endif
    __builtin_unreachable();
}

/*
 * ELF enters x86-64 _start with rsp % 16 == 8.  A C function used directly as
 * the entry point therefore has no caller-established SIMD stack alignment;
 * at -O2 its guard-row comparison legitimately uses movdqa and faults before
 * it can report a kernel result.  Normalize the entry ABI once, then execute
 * the same architecture-neutral probe body.  AArch64 already guarantees a
 * 16-byte aligned SP at process entry.
 */
__attribute__((noreturn, noinline)) void probe_main(void);

#if defined(__x86_64__)
__attribute__((naked, noreturn)) void _start(void)
{
    __asm__ volatile(
        "andq $-16, %rsp\n\t"
        "call probe_main\n\t"
        "ud2");
}
#else
void _start(void)
{
    probe_main();
}
#endif

__attribute__((noreturn, noinline)) void probe_main(void)
{
    const uint32_t sentinel = 0x11223344U;
    const uint32_t color = 0xff3a7bc1U;
    for (uint32_t i = 0; i < 40U; i++) framebuffer[i] = sentinel;
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
    /* A row at g_fb_h must be rejected rather than writing the guard row. */
    rt_gui_fill4(((RuntimeValue)0U << 32) | 4U,
                 ((RuntimeValue)8U << 32) | 1U,
                 (RuntimeValue)0xff00ffffU, 0);

    uint32_t mismatches = 0;
    for (uint32_t y = 0; y < 4U; y++) {
        for (uint32_t x = 0; x < 8U; x++) {
            uint32_t expected = sentinel;
            if (x >= 1U && x < 7U && y >= 1U && y < 3U) expected = color;
            if (x >= 6U && y == 3U) expected = edge_color;
            if (framebuffer[y * 8U + x] != expected) mismatches++;
        }
    }
    for (uint32_t x = 0; x < 8U; x++) {
        if (framebuffer[4U * 8U + x] != sentinel) mismatches++;
    }
    if (rt_gui_simd_fill_enabled() != 1 ||
        rt_gui_simd_fill_hits() != 1 ||
        rt_gui_simd_fill_chunks() <= 0 ||
        rt_gui_simd_fill_tail_pixels() != 6 ||
        rt_gui_simd_fill_scalar_parity() != 1 || mismatches != 0) {
        probe_exit(1);
    }
    probe_exit(0);
}
