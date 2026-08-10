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

#include <stdint.h>

extern char __bss_start[];
extern char __bss_end[];
extern char __simple_sandbox_start[] __attribute__((weak));
extern char __simple_sandbox_end[] __attribute__((weak));

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

uint64_t rt_simple_sandbox_section_start(void) {
    if (!__simple_sandbox_start) {
        return 0;
    }
    return (uint64_t)(uintptr_t)__simple_sandbox_start;
}

uint64_t rt_simple_sandbox_section_end(void) {
    if (!__simple_sandbox_end) {
        return 0;
    }
    return (uint64_t)(uintptr_t)__simple_sandbox_end;
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
 * rt_volatile_* / rt_*_barrier — freestanding counterparts of the hosted
 * runtime's `rt_volatile_read_u8/u16/u32/u64`, `rt_volatile_write_u8/u16/
 * u32/u64`, `rt_load_barrier`, `rt_store_barrier` (declared in
 * src/runtime/runtime.h, implemented for the hosted build in
 * src/runtime/runtime_native.c:4874-4906). Signatures match exactly
 * (int64_t addr/value, matching the Simple-side `extern fn` declarations
 * in src/lib/nogc_sync_mut/io/volatile_ops.spl) so callers behave
 * identically whether linked against the hosted or baremetal runtime.
 *
 * Distinct from `rt_mmio_read/write_u8/u16/u32/u64` above: those use an
 * unsigned uint64_t/uintN_t ABI and are a separate, pre-existing call
 * convention used elsewhere in the baremetal tree. `rt_volatile_*` is the
 * signed-int64 ABI the hosted runtime and `io.volatile_ops` module expect;
 * both may legitimately coexist as distinct symbols.
 *
 * `rt_load_barrier`/`rt_store_barrier` are declared in runtime.h but were
 * never implemented in EITHER runtime variant (grepped: no definition in
 * src/runtime/runtime.c or runtime_native.c). They are mechanically trivial
 * (a directional fence, no allocator/heap dependency) so are implemented
 * here as acquire/release fences, matching the semantics documented in
 * io/volatile_ops.spl ("load_barrier() - acquire fence", "store_barrier()
 * - release fence"). `rt_memory_barrier` (a full fence) already exists
 * below for x86/general use; these two round out the family.
 * ======================================================================== */

int64_t rt_volatile_read_u8(int64_t addr) {
    return *(volatile uint8_t *)(uintptr_t)addr;
}

int64_t rt_volatile_read_u16(int64_t addr) {
    return *(volatile uint16_t *)(uintptr_t)addr;
}

int64_t rt_volatile_read_u32(int64_t addr) {
    return *(volatile uint32_t *)(uintptr_t)addr;
}

int64_t rt_volatile_read_u64(int64_t addr) {
    return (int64_t)*(volatile uint64_t *)(uintptr_t)addr;
}

void rt_volatile_write_u8(int64_t addr, int64_t value) {
    *(volatile uint8_t *)(uintptr_t)addr = (uint8_t)value;
}

void rt_volatile_write_u16(int64_t addr, int64_t value) {
    *(volatile uint16_t *)(uintptr_t)addr = (uint16_t)value;
}

void rt_volatile_write_u32(int64_t addr, int64_t value) {
    *(volatile uint32_t *)(uintptr_t)addr = (uint32_t)value;
}

void rt_volatile_write_u64(int64_t addr, int64_t value) {
    *(volatile uint64_t *)(uintptr_t)addr = (uint64_t)value;
}

void rt_load_barrier(void) {
    __atomic_thread_fence(__ATOMIC_ACQUIRE);
}

void rt_store_barrier(void) {
    __atomic_thread_fence(__ATOMIC_RELEASE);
}

/* ========================================================================
 * x86 Port I/O (rt_port_inb/outb/inw/outw/inl/outl/io_wait) MOVED
 * 2026-08-10 to `runtime_port_io.c` in this directory, which is now their
 * single global definition site. The move lets the SimpleOS x86_64 sysroot
 * link `runtime_log.c` (its COM1 path calls rt_port_outb/inb) without
 * pulling in this TU, whose rt_read_cr3/rt_write_cr3/rt_invlpg/
 * rt_volatile_* definitions would collide with runtime_native.o in that
 * archive. See src/os/port/llvm/sysroot.shs and
 * doc/08_tracking/bug/logging_surfaces_that_suppress_errors_by_default_family_2026-08-10.md
 * ======================================================================== */

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
#if defined(__riscv)
/* riscv64/riscv32 have a real wait-for-interrupt instruction; use it so
 * arch-neutral callers (e.g. os.kernel.interrupts.idt._halt()) get a genuine
 * halt instead of a busy-spin. Interrupt masking on riscv is done via SIE/CSR
 * ops (see os.kernel.arch.riscv64.cpu.csrc_sstatus) — rt_cli() intentionally
 * stays a no-op here, callers that need real IRQ masking use that path. */
void rt_hlt(void) { __asm__ volatile ("wfi"); }
#else
void rt_hlt(void) {}
#endif
void rt_lgdt(uint64_t a) { (void)a; }
void rt_lidt(uint64_t a) { (void)a; }
void rt_ltr(uint16_t s) { (void)s; }
void rt_reload_segments(void) {}
#endif
