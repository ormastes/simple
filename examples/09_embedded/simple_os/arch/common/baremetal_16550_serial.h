#ifndef SIMPLEOS_BAREMETAL_16550_SERIAL_H
#define SIMPLEOS_BAREMETAL_16550_SERIAL_H

#ifndef UART_BASE
#define UART_BASE 0x10000000UL
#endif

#define UART_THR 0x00UL
#define UART_LSR 0x05UL
#define UART_LSR_THRE 0x20U

#ifdef SIMPLEOS_RV64_FDT_CONSOLE
/* riscv64: the console UART is selected from the firmware device tree by pure
 * Simple (src/os/kernel/boot/fdt_console.spl) and stored by boot_entry.c,
 * which owns the single definition of rv64_console_putc. Weak so a TU linked
 * without boot_entry.c (host-side probes) keeps the byte-wide QEMU default. */
void rv64_console_putc(char c) __attribute__((weak));
#endif

static void uart_putc(char c){
#ifdef SIMPLEOS_RV64_FDT_CONSOLE
    if (rv64_console_putc) {
        rv64_console_putc(c);
        return;
    }
#endif
    volatile uint8_t *uart = (volatile uint8_t *)UART_BASE;
    for (uint32_t spin = 0; spin < 100000; spin++) {
        if ((uart[UART_LSR] & UART_LSR_THRE) != 0) break;
    }
    uart[UART_THR] = (uint8_t)c;
}

static void uart_puts(const char *s){
    while (*s) {
        if (*s == '\n') uart_putc('\r');
        uart_putc(*s++);
    }
}

#endif
