/*
 * x86 port I/O primitives — freestanding, single global owner.
 *
 * Extracted verbatim from `src/runtime/startup/baremetal/runtime_minimal.c`
 * (2026-08-10) so the SimpleOS x86_64 sysroot can link
 * `startup/baremetal/runtime_log.c`, whose COM1 path calls
 * `rt_port_outb`/`rt_port_inb`.
 *
 * Why its own TU rather than adding runtime_minimal.c to the sysroot loop:
 * runtime_minimal.c also defines `rt_read_cr3`, `rt_write_cr3`, `rt_invlpg`
 * and `rt_volatile_{read,write}_u{8,16,32,64}` — 11 symbols that
 * `runtime_native.o` already owns in the same sysroot archive. The rt_port_*
 * family is the ONLY part of runtime_minimal.c that runtime_native.c does not
 * define at all (verified by grep: zero rt_port_* definitions there), so it is
 * the exact, minimal cut that resolves the sysroot's need without creating an
 * ODR collision and without preprocessor guards that two archives could drift
 * apart on. Definitions were MOVED, not copied: this file is the single global
 * definition site, so no lane can ever see two.
 *
 * Callers: src/os/kernel/arch/x86/com1_common.spl, arch/reset.spl,
 * arch/x86_32/cpu.spl, arch/x86_64/*, and runtime_log.c's COM1 path — all via
 * `extern fn rt_port_*`.
 *
 * The non-x86 stubs are retained so arch-neutral callers (and the arm/riscv
 * baremetal links that also compile the baremetal startup set) keep resolving
 * to a no-op rather than an undefined symbol, exactly as before the move.
 */

#include <stdint.h>

/* ========================================================================
 * x86 Port I/O — for PS/2 keyboard, PIC, serial, PCI config space.
 * ======================================================================== */

#if defined(__x86_64__) || defined(__i386__)

uint8_t rt_port_inb(uint16_t port) {
    uint8_t result;
    __asm__ volatile ("inb %1, %0" : "=a"(result) : "Nd"(port));
    return result;
}

void rt_port_outb(uint16_t port, uint8_t value) {
    __asm__ volatile ("outb %0, %1" : : "a"(value), "Nd"(port));
}

uint16_t rt_port_inw(uint16_t port) {
    uint16_t result;
    __asm__ volatile ("inw %1, %0" : "=a"(result) : "Nd"(port));
    return result;
}

void rt_port_outw(uint16_t port, uint16_t value) {
    __asm__ volatile ("outw %0, %1" : : "a"(value), "Nd"(port));
}

uint32_t rt_port_inl(uint16_t port) {
    uint32_t result;
    __asm__ volatile ("inl %1, %0" : "=a"(result) : "Nd"(port));
    return result;
}

void rt_port_outl(uint16_t port, uint32_t value) {
    __asm__ volatile ("outl %0, %1" : : "a"(value), "Nd"(port));
}

/* I/O wait — short delay for slow I/O devices */
void rt_port_io_wait(void) {
    __asm__ volatile ("outb %%al, $0x80" : : "a"(0));
}

#else
/* Stubs for non-x86 */
uint8_t rt_port_inb(uint16_t port) { (void)port; return 0; }
void rt_port_outb(uint16_t port, uint8_t value) { (void)port; (void)value; }
uint16_t rt_port_inw(uint16_t port) { (void)port; return 0; }
void rt_port_outw(uint16_t port, uint16_t value) { (void)port; (void)value; }
uint32_t rt_port_inl(uint16_t port) { (void)port; return 0; }
void rt_port_outl(uint16_t port, uint32_t value) { (void)port; (void)value; }
void rt_port_io_wait(void) {}
#endif
