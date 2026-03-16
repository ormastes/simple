/*
 * uart.h — COM1 16550 UART driver for x86_64
 *
 * Part of the SimpleOS L4 microkernel reference implementation.
 * Identical to x86 version — UART is I/O-port based, no 64-bit changes.
 */

#ifndef ARCH_X86_64_IO_UART_H
#define ARCH_X86_64_IO_UART_H

#include "common/types.h"
#include "common/config.h"
#include "common/compiler.h"

/* ── COM1 port addresses ───────────────────────────────────────────── */

#define COM1_BASE       0x3F8

#define UART_DATA       (COM1_BASE + 0)   /* Data register (R/W)       */
#define UART_IER        (COM1_BASE + 1)   /* Interrupt Enable Register */
#define UART_FCR        (COM1_BASE + 2)   /* FIFO Control Register (W) */
#define UART_LCR        (COM1_BASE + 3)   /* Line Control Register     */
#define UART_MCR        (COM1_BASE + 4)   /* Modem Control Register    */
#define UART_LSR        (COM1_BASE + 5)   /* Line Status Register      */
#define UART_MSR        (COM1_BASE + 6)   /* Modem Status Register     */

/* Divisor Latch (when DLAB=1) */
#define UART_DLL        (COM1_BASE + 0)   /* Divisor Latch Low         */
#define UART_DLH        (COM1_BASE + 1)   /* Divisor Latch High        */

/* Baud rate configuration */
#define UART_CLOCK      115200
#define UART_BAUD       115200
#define UART_DIVISOR    (UART_CLOCK / UART_BAUD)  /* == 1 */

/* Line Status Register bits */
#define LSR_DATA_READY  0x01
#define LSR_THRE        0x20  /* Transmitter Holding Register Empty */

/* ── Inline I/O helpers ────────────────────────────────────────────── */

static inline void outb(uint16_t port, uint8_t val)
{
    __asm__ volatile ("outb %0, %1" : : "a"(val), "Nd"(port));
}

static inline uint8_t inb(uint16_t port)
{
    uint8_t val;
    __asm__ volatile ("inb %1, %0" : "=a"(val) : "Nd"(port));
    return val;
}

/* ── Public API ────────────────────────────────────────────────────── */

void uart_init(void);
void uart_putc(char c);
char uart_getc(void);
bool uart_has_data(void);
void uart_write(const char *s);
void uart_write_hex64(uint64_t val);
void uart_write_hex(uint32_t val);
void uart_write_dec(uint32_t val);

#endif /* ARCH_X86_64_IO_UART_H */
