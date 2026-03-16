/*
 * SimpleOS -- L4 Microkernel Reference Implementation
 * kernel/core/log.c -- Kernel debug logging implementation
 *
 * Mirrors: spl/kernel/core/log.spl
 *
 * Delegates to uart_write for output.  In a real kernel, arch/x86/io/uart.h
 * provides serial_init / serial_putchar.  For now we declare them extern.
 */

#include "kernel/core/log.h"

/* ---- External UART interface (provided by arch layer) ------------------ */

extern void uart_init(void);
extern void uart_putchar(char c);

/* ---- Module state ------------------------------------------------------ */

static log_level_t g_log_level     = LOG_LEVEL_DEBUG;
static bool        g_log_initialized = false;

/* ---- Internal helpers -------------------------------------------------- */

static void uart_puts(const char *s)
{
    while (*s) {
        uart_putchar(*s++);
    }
}

static void uart_newline(void)
{
    uart_putchar('\r');
    uart_putchar('\n');
}

static const char *level_prefix(log_level_t level)
{
    switch (level) {
    case LOG_LEVEL_DEBUG: return "[DEBUG] ";
    case LOG_LEVEL_INFO:  return "[INFO]  ";
    case LOG_LEVEL_WARN:  return "[WARN]  ";
    case LOG_LEVEL_ERROR: return "[ERROR] ";
    case LOG_LEVEL_PANIC: return "[PANIC] ";
    default:              return "[?????] ";
    }
}

static bool level_enabled(log_level_t level)
{
    return (uint32_t)level >= (uint32_t)g_log_level;
}

static void ensure_init(void)
{
    if (!g_log_initialized) {
        uart_init();
        g_log_initialized = true;
    }
}

static void u32_to_hex_buf(uint32_t value, char buf[9])
{
    static const char hex[] = "0123456789ABCDEF";
    for (int i = 7; i >= 0; i--) {
        buf[i] = hex[value & 0xF];
        value >>= 4;
    }
    buf[8] = '\0';
}

static void u32_to_dec_buf(uint32_t value, char buf[11])
{
    if (value == 0) {
        buf[0] = '0';
        buf[1] = '\0';
        return;
    }

    char tmp[11];
    int  pos = 0;

    while (value > 0) {
        tmp[pos++] = '0' + (char)(value % 10);
        value /= 10;
    }

    /* Reverse */
    for (int i = 0; i < pos; i++) {
        buf[i] = tmp[pos - 1 - i];
    }
    buf[pos] = '\0';
}

/* ---- API --------------------------------------------------------------- */

void klog_init(void)
{
    if (g_log_initialized) {
        return;
    }
    uart_init();
    g_log_initialized = true;
    klog_info("[LOG] Kernel log initialized");
}

/* ------------------------------------------------------------------------ */

void klog_set_level(log_level_t level)
{
    g_log_level = level;
}

/* ------------------------------------------------------------------------ */

void klog(log_level_t level, const char *msg)
{
    ensure_init();

    if (!level_enabled(level)) {
        return;
    }

    uart_puts(level_prefix(level));
    uart_puts(msg);
    uart_newline();
}

/* ------------------------------------------------------------------------ */

void klog_debug(const char *msg) { klog(LOG_LEVEL_DEBUG, msg); }
void klog_info(const char *msg)  { klog(LOG_LEVEL_INFO,  msg); }
void klog_warn(const char *msg)  { klog(LOG_LEVEL_WARN,  msg); }
void klog_error(const char *msg) { klog(LOG_LEVEL_ERROR, msg); }

/* ------------------------------------------------------------------------ */

void klog_hex(log_level_t level, const char *msg, uint32_t value)
{
    ensure_init();

    if (!level_enabled(level)) {
        return;
    }

    char hex_buf[9];
    u32_to_hex_buf(value, hex_buf);

    uart_puts(level_prefix(level));
    uart_puts(msg);
    uart_puts("0x");
    uart_puts(hex_buf);
    uart_newline();
}

/* ------------------------------------------------------------------------ */

void klog_dec(log_level_t level, const char *msg, uint32_t value)
{
    ensure_init();

    if (!level_enabled(level)) {
        return;
    }

    char dec_buf[11];
    u32_to_dec_buf(value, dec_buf);

    uart_puts(level_prefix(level));
    uart_puts(msg);
    uart_puts(dec_buf);
    uart_newline();
}

/* ------------------------------------------------------------------------ */

NORETURN void kpanic(const char *msg)
{
    ensure_init();

    uart_puts("[PANIC] ");
    uart_puts(msg);
    uart_newline();
    uart_puts("*** KERNEL HALTED ***");
    uart_newline();

    /* Disable interrupts and halt */
    __asm__ volatile (
        "cli\n"
        "1: hlt\n"
        "   jmp 1b\n"
    );

    /* Never reached, but satisfy compiler */
    for (;;) {}
}
