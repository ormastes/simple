/*
 * Bare-metal residual FFI primitives.
 *
 * The high-level startup control-flow (`__spl_start_bare`, `main`,
 * `__spl_exit`, `spl_thread_init`, `spl_init_args`) lives in the Simple
 * port at `src/os/runtime/baremetal/runtime_minimal.spl` (Wave 3,
 * Blocker B). This file retains only the residual rt_* primitives that
 * Simple has no syntax for — the per-arch halt asm, BSS zero loop using
 * linker-defined `__bss_start`/`__bss_end` symbols, MMIO volatile
 * accessors, port I/O, control-register writes, descriptor-table loads,
 * and segment-reload trampolines.
 *
 * The build manifest at `src/compiler/80.driver/build/baremetal.spl`
 * compiles BOTH this file and the .spl port (`compile_runtime_support`
 * + `compile_runtime_support_spl`); the linker resolves the .spl
 * `extern fn rt_zero_bss / rt_halt_exit` references against the
 * primitives defined here.
 */

extern char __bss_start[];
extern char __bss_end[];

/* ========================================================================
 * Wave 3 Blocker A: FFI primitives mirroring the .spl entry points
 * in src/os/runtime/baremetal/runtime_minimal.spl.
 *
 * `rt_zero_bss`  — zeroes [__bss_start, __bss_end). Linker-defined
 *                  symbols the .spl layer cannot name directly.
 * `rt_halt_exit` — per-arch `cli/hlt` (x86) or `wfi` loop (arm/riscv).
 *                  Simple has no inline-asm syntax for these patterns.
 * ======================================================================== */

void rt_zero_bss(void) {
    for (char *p = __bss_start; p < __bss_end; p++) {
        *p = 0;
    }
}

void rt_halt_exit(int status) {
    (void)status;
#if defined(__x86_64__) || defined(__i386__)
    __asm__ volatile (
        "cli\n"
        "1: hlt\n"
        "jmp 1b\n"
    );
#elif defined(__aarch64__)
    __asm__ volatile (
        "msr daifset, #0xF\n"
        "1: wfi\n"
        "b 1b\n"
    );
#elif defined(__arm__)
    __asm__ volatile (
        "cpsid if\n"
        "1: wfi\n"
        "b 1b\n"
    );
#elif defined(__riscv)
    __asm__ volatile (
        "csrci mstatus, 0x8\n"
        "1: wfi\n"
        "j 1b\n"
    );
#else
    for (;;) {}
#endif
    __builtin_unreachable();
}

/* ========================================================================
 * Volatile MMIO — used by Simple baremetal code for hardware register access.
 * These MUST NOT be optimized away by the compiler.
 * ======================================================================== */

#include <stdint.h>

uint32_t rt_mmio_read_u32(uint64_t addr) {
    return *(volatile uint32_t *)(uintptr_t)addr;
}

void rt_mmio_write_u32(uint64_t addr, uint32_t value) {
    *(volatile uint32_t *)(uintptr_t)addr = value;
}

uint16_t rt_mmio_read_u16(uint64_t addr) {
    return *(volatile uint16_t *)(uintptr_t)addr;
}

void rt_mmio_write_u16(uint64_t addr, uint16_t value) {
    *(volatile uint16_t *)(uintptr_t)addr = value;
}

uint8_t rt_mmio_read_u8(uint64_t addr) {
    return *(volatile uint8_t *)(uintptr_t)addr;
}

void rt_mmio_write_u8(uint64_t addr, uint8_t value) {
    *(volatile uint8_t *)(uintptr_t)addr = value;
}

uint64_t rt_mmio_read_u64(uint64_t addr) {
    return *(volatile uint64_t *)(uintptr_t)addr;
}

void rt_mmio_write_u64(uint64_t addr, uint64_t value) {
    *(volatile uint64_t *)(uintptr_t)addr = value;
}

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

/* ========================================================================
 * x86 special registers — CR3, MSR access for kernel.
 * ======================================================================== */

#if defined(__x86_64__)

uint64_t rt_read_cr3(void) {
    uint64_t val;
    __asm__ volatile ("mov %%cr3, %0" : "=r"(val));
    return val;
}

void rt_write_cr3(uint64_t val) {
    __asm__ volatile ("mov %0, %%cr3" : : "r"(val) : "memory");
}

uint64_t rt_read_cr2(void) {
    uint64_t val;
    __asm__ volatile ("mov %%cr2, %0" : "=r"(val));
    return val;
}

void rt_invlpg(uint64_t addr) {
    __asm__ volatile ("invlpg (%0)" : : "r"(addr) : "memory");
}

uint64_t rt_read_msr(uint32_t msr) {
    uint32_t lo, hi;
    __asm__ volatile ("rdmsr" : "=a"(lo), "=d"(hi) : "c"(msr));
    return ((uint64_t)hi << 32) | lo;
}

void rt_write_msr(uint32_t msr, uint64_t val) {
    uint32_t lo = (uint32_t)val;
    uint32_t hi = (uint32_t)(val >> 32);
    __asm__ volatile ("wrmsr" : : "c"(msr), "a"(lo), "d"(hi));
}

void rt_cli(void) { __asm__ volatile ("cli"); }
void rt_sti(void) { __asm__ volatile ("sti"); }
void rt_hlt(void) { __asm__ volatile ("hlt"); }

void rt_lgdt(uint64_t gdtr_addr) {
    __asm__ volatile ("lgdt (%0)" : : "r"(gdtr_addr) : "memory");
}

void rt_lidt(uint64_t idtr_addr) {
    __asm__ volatile ("lidt (%0)" : : "r"(idtr_addr) : "memory");
}

void rt_ltr(uint16_t selector) {
    __asm__ volatile ("ltr %0" : : "r"(selector));
}

void rt_reload_segments(void) {
    __asm__ volatile (
        "mov $0x10, %%ax\n\t"
        "mov %%ax, %%ds\n\t"
        "mov %%ax, %%es\n\t"
        "mov %%ax, %%fs\n\t"
        "mov %%ax, %%gs\n\t"
        "mov %%ax, %%ss\n\t"
        "lea 1f(%%rip), %%rax\n\t"
        "pushq $0x08\n\t"
        "pushq %%rax\n\t"
        "lretq\n\t"
        "1:\n\t"
        :
        :
        : "rax", "memory"
    );
}

#else
uint64_t rt_read_cr3(void) { return 0; }
void rt_write_cr3(uint64_t val) { (void)val; }
uint64_t rt_read_cr2(void) { return 0; }
void rt_invlpg(uint64_t addr) { (void)addr; }
uint64_t rt_read_msr(uint32_t msr) { (void)msr; return 0; }
void rt_write_msr(uint32_t msr, uint64_t val) { (void)msr; (void)val; }
void rt_cli(void) {}
void rt_sti(void) {}
void rt_hlt(void) {}
void rt_lgdt(uint64_t a) { (void)a; }
void rt_lidt(uint64_t a) { (void)a; }
void rt_ltr(uint16_t s) { (void)s; }
void rt_reload_segments(void) {}
#endif
