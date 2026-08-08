/*
 * Bare-metal runtime hooks for the Simple log lib
 * (src/lib/nogc_async_mut_noalloc/log/).
 *
 * Implements the extern symbols that the log lib declares:
 *   rt_simpleos_log_init        — store level + target bitmask
 *   rt_simpleos_log_is_enabled  — level-filter passthrough (always true here;
 *                                 the Simple side owns the level cutoff)
 *   rt_simpleos_log_emit        — compose already done on the Simple side;
 *                                 just dispatch bytes to the device target
 *   rt_log_target_device_write_bytes   — write raw bytes to the UART
 *   rt_log_target_semihost_write_bytes — semihost target (deferred stub)
 *   rt_simpleos_log_set_device  — inject {kind, base} picked from the
 *                                 active MachineProfile at boot
 *
 * Arch dispatch follows the rt_port_outb/inb precedent in runtime_minimal.c.
 */

#include <stdint.h>
#include <stdbool.h>
#include <stddef.h>

/* Kind codes match Simple-side log_set_device_from_profile translation. */
#define LOG_DEV_KIND_COM1    1
#define LOG_DEV_KIND_PL011   2
#define LOG_DEV_KIND_NS16550 3

#if defined(__x86_64__) || defined(__i386__)
#  define LOG_DEV_KIND_DEFAULT   LOG_DEV_KIND_COM1
#  define LOG_DEV_BASE_DEFAULT   ((uint64_t)0x3F8)
#elif defined(__aarch64__) || defined(__arm__)
#  define LOG_DEV_KIND_DEFAULT   LOG_DEV_KIND_PL011
#  define LOG_DEV_BASE_DEFAULT   ((uint64_t)0x09000000)
#elif defined(__riscv)
#  define LOG_DEV_KIND_DEFAULT   LOG_DEV_KIND_NS16550
#  define LOG_DEV_BASE_DEFAULT   ((uint64_t)0x10000000)
#else
#  define LOG_DEV_KIND_DEFAULT   0
#  define LOG_DEV_BASE_DEFAULT   ((uint64_t)0)
#endif

static volatile int64_t  g_log_level   = 2;   /* LOG_INFO */
static volatile int64_t  g_log_targets = 1;   /* TARGET_DEVICE */
static volatile int64_t  g_log_kind    = LOG_DEV_KIND_DEFAULT;
static volatile uint64_t g_log_base    = LOG_DEV_BASE_DEFAULT;

#if defined(__x86_64__) || defined(__i386__)
extern uint8_t rt_port_inb(uint16_t port);
extern void    rt_port_outb(uint16_t port, uint8_t value);
#endif

static void log_write_byte_com1(uint64_t base, uint8_t byte) {
#if defined(__x86_64__) || defined(__i386__)
    uint16_t port = (uint16_t)base;
    /* Wait for transmitter holding register empty (LSR bit 5). */
    while ((rt_port_inb((uint16_t)(port + 5)) & 0x20) == 0) { }
    rt_port_outb(port, byte);
#else
    (void)base; (void)byte;
#endif
}

static void log_write_byte_pl011(uint64_t base, uint8_t byte) {
#if defined(__aarch64__) || defined(__arm__)
    volatile uint32_t *fr = (volatile uint32_t *)(uintptr_t)(base + 0x018);
    volatile uint32_t *dr = (volatile uint32_t *)(uintptr_t)(base + 0x000);
    /* Wait while TXFF (bit 5) is set. */
    while ((*fr) & (1u << 5)) { }
    *dr = (uint32_t)byte;
#else
    (void)base; (void)byte;
#endif
}

static void log_write_byte_ns16550(uint64_t base, uint8_t byte) {
#if defined(__riscv)
    volatile uint8_t *lsr = (volatile uint8_t *)(uintptr_t)(base + 5);
    volatile uint8_t *thr = (volatile uint8_t *)(uintptr_t)(base + 0);
    /* Wait for THR empty (LSR bit 5). */
    while (((*lsr) & 0x20) == 0) { }
    *thr = byte;
#else
    (void)base; (void)byte;
#endif
}

static void log_write_byte(uint8_t byte) {
    switch ((int)g_log_kind) {
        case LOG_DEV_KIND_COM1:    log_write_byte_com1(g_log_base, byte); return;
        case LOG_DEV_KIND_PL011:   log_write_byte_pl011(g_log_base, byte); return;
        case LOG_DEV_KIND_NS16550: log_write_byte_ns16550(g_log_base, byte); return;
        default: return;
    }
}

bool rt_simpleos_log_init(int64_t level, int64_t targets) {
    g_log_level   = level;
    g_log_targets = targets;
    return true;
}

bool rt_simpleos_log_is_enabled(int64_t level) {
    (void)level;
    /* Filtering lives in the Simple-side logger (g_log_level). Return
     * true so the Simple code reaches the compose + emit path; it already
     * short-circuits below its own threshold. */
    return true;
}

bool rt_simpleos_log_set_device(int64_t kind, int64_t base) {
    g_log_kind = kind;
    g_log_base = (uint64_t)base;
    return true;
}

bool rt_log_target_device_write_bytes(int64_t ptr, int64_t len) {
    if ((g_log_targets & 1) == 0) return false;
    if (ptr == 0 || len <= 0)     return false;
    const uint8_t *bytes = (const uint8_t *)(uintptr_t)ptr;
    for (int64_t i = 0; i < len; i++) {
        log_write_byte(bytes[i]);
    }
    return true;
}

bool rt_log_target_semihost_write_bytes(int64_t ptr, int64_t len) {
    /* Semihost target not wired yet — see targets.spl TARGET_SEMIHOST.
     * Returning false lets the Simple-side fallback take over. */
    (void)ptr; (void)len;
    return false;
}

bool rt_simpleos_log_emit(int64_t level, int64_t msg_ptr, int64_t msg_len) {
    (void)level;
    return rt_log_target_device_write_bytes(msg_ptr, msg_len);
}
