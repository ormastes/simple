/* boot_entry.c — the missing half of the riscv64 early-boot contract.
 *
 * crt0.S in this directory documents and implements the OpenSBI S-mode handover
 * (a0 = hartid, a1 = dtb, MMU off, running physically at the 0x80200000 link
 * address), sets gp/sp, zeroes .bss, and then does:
 *
 *     call boot_entry
 *
 * Nothing in this tree defined `boot_entry`. Verified 2026-08-31 with
 * `/usr/bin/grep -rn boot_entry --include=*.c --include=*.h --include=*.rs
 * --include=*.S src/ examples/`: the only hits were crt0.S's own call site and
 * its comment, plus the seed's unrelated `_entry32` logic. The Rust seed's
 * freestanding linker aliases `_start`, `spl_start`, `__simple_entry_start` and
 * `main`, but never `boot_entry` (linker.rs ~2470-2525), so every attempt to
 * link a riscv64 entry .spl through this crt0.S ends in
 *
 *     ld.lld: error: undefined symbol: boot_entry
 *     >>> referenced by _boot_crt0.o
 *
 * That is why the existing riscv64 real-firmware gate
 * (scripts/check/check-simpleos-riscv64-opensbi-guest-boot.shs) links a
 * hand-written C probe with gcc instead of going through native-build: the
 * native-build path into this crt0 has never been linkable.
 *
 * This file supplies exactly that missing symbol and nothing else. It is the
 * documented contract, not a workaround: crt0.S promises to call
 * `boot_entry(hartid, dtb)`, and the seed guarantees a `spl_start` alias
 * pointing at the entry module's own `spl_start` function, so the shim between
 * them is one call. Because it is per-lane-neutral (every riscv64 entry .spl
 * that follows the smoke_entry.spl convention defines `spl_start`), a single
 * shared definition here serves all of them rather than each lane carrying a
 * copy.
 *
 * The handover registers are accepted and deliberately ignored: `spl_start`
 * takes no arguments in the Simple entry convention. A future entry that needs
 * hartid/dtb should gain a two-argument Simple entry and this shim should
 * forward to it; until such an entry exists, inventing a forwarding path would
 * be unused code. They are stored to a pair of globals rather than dropped so
 * the values survive for a debugger and for any later runtime that wants them,
 * and so the parameters are genuinely used (silencing -Wunused-parameter
 * without a cast-to-void lie).
 */

/* Firmware handover values, captured before Simple code runs. Read by
 * debuggers and available to any future runtime that needs the FDT. */
unsigned long g_rv64_boot_hartid;
unsigned long g_rv64_boot_dtb;

/* Provided by the entry module: the seed emits
 * `--defsym=spl_start=<mangled module path>__spl_start` on the freestanding
 * link, so this plain declaration resolves to the lane's own entry function. */
void spl_start(void);

/* Runs every module's `__module_init_*` (heap-typed module globals: array,
 * string and struct-literal initializers, which cannot be static .data and
 * must be built at runtime via rt_array_new/rt_string_new/rt_alloc).
 * Synthesized by the linker's init-caller aggregator
 * (pipeline/native_project/linker.rs `generate_init_caller`).
 *
 * The HOSTED link gets this call for free from the generated `main` stub
 * (linker.rs:802-806). A freestanding `--entry-closure` link has no such stub:
 * its entry is the Simple entry function itself, so the call must come from
 * the target's own boot path. x86_64 does it in crt0.s
 * (arch/x86_64/boot/crt0.s, `.skip_module_inits`); riscv64 had NO caller
 * anywhere -- crt0.S does not call it and the entry .spl files do not declare
 * it -- so nothing referenced the aggregator, --gc-sections dropped it along
 * with every `__module_init_*`, and every module-level `var g: [T] = [...]`
 * stayed a null/zero handle in-guest. Measured before this fix on
 * build/os/riscv64_interp/interp/kernel.elf: 7167 symbols, ZERO
 * `__module_init_*`, no `__simple_call_module_inits`.
 *
 * Weak so a link that genuinely has no aggregator still boots. Placed here
 * rather than in crt0.S because boot_entry.c is already the per-lane-neutral
 * shim every riscv64 entry passes through, and C gets the weak-symbol
 * null-check without hand-written HI20/LO12 relocations.
 *
 * Ordering: after the firmware handover capture and before `spl_start`, i.e.
 * the same "heap up, before the entry point" slot the rv64 kernel uses
 * (src/os/kernel/arch/riscv64/boot.spl:89). The freestanding rv64 runtime
 * brings its heap up lazily on first allocation, so no explicit heap-init
 * call is required at this point. */
void __attribute__((weak)) __simple_call_module_inits(void);

/* Defined at the bottom of this file (see the trap-vector block). Declared here
 * so boot_entry can install the vector and paint the stack guard BEFORE any
 * Simple code runs -- a fault during module init must be reported too. */
void rv64_boot_install_trap_vector(void);
void rv64_stack_guard_paint(void);

void boot_entry(unsigned long hartid, unsigned long dtb)
{
    /* FIRST, before anything that can fault: without this the guest has no
     * trap vector at all and every exception is a silent reset. */
    rv64_boot_install_trap_vector();
    rv64_stack_guard_paint();
    g_rv64_boot_hartid = hartid;
    g_rv64_boot_dtb = dtb;
    if (__simple_call_module_inits) {
        __simple_call_module_inits();
    }
    spl_start();
    /* crt0.S parks in `wfi` when this returns, so there is nothing to do here.
     * Returning is the normal path for an entry that completes. */
}

/* ---------------------------------------------------------------------------
 * S-mode trap vector — the other missing half of this boot contract.
 *
 * Until this landed, crt0.S set gp/sp, zeroed .bss and called boot_entry with
 * `stvec` NEVER WRITTEN on the normal boot path. The only `csrw stvec` in this
 * tree lives inside the U-mode fs-exec path (baremetal_stubs.c), which
 * rt_riscv_fs_exec_run() fails closed on and no lane reaches. So every
 * exception a riscv64 guest took — every null jump through an unresolved
 * runtime symbol, every bad load, every misaligned access — vectored to
 * whatever address the firmware happened to leave in stvec, printed NOTHING,
 * and surfaced as "the guest resets and the entry re-enters from the top".
 *
 * That is not a missing debug aid, it is a missing safety control: a
 * freestanding supervisor-mode kernel with no trap vector cannot report its own
 * faults, and three sessions of the riscv64 in-guest rows have now been spent
 * reading a silent reset. See
 * doc/08_tracking/bug/riscv64_in_guest_interp_resets_on_cross_function_call_2026-09-01.md
 *
 * Design notes that matter:
 *   * A DEDICATED trap stack, swapped in via `sscratch`. The most likely fault
 *     in a deeply recursive interpreter is a blown kernel stack; a handler that
 *     ran on the faulting stack would fault again and reproduce the very
 *     silence it exists to end.
 *   * Values are printed as RAW HEX by a nibble loop. Nothing here formats an
 *     integer through the Simple runtime: rt_raw_i64_to_string does not exist
 *     in this freestanding image, and calling it is itself a null jump.
 *   * The handler PARKS. It never returns and never resets, so the transcript
 *     ends at the fault instead of looping.
 *   * Definitions live in boot_entry.c on purpose: it is the one riscv64 boot
 *     TU with no duplicate twin. baremetal_stubs.c and
 *     baremetal_runtime_core.inc.c define the same runtime entry points twice
 *     and the link silently picks one — a trap that has already cost this tree
 *     two sessions. A single definition cannot be shadowed.
 * ------------------------------------------------------------------------- */

#define SIMPLEOS_TRAP_UART_BASE 0x10000000UL
#define SIMPLEOS_TRAP_UART_THR  0x00UL
#define SIMPLEOS_TRAP_UART_LSR  0x05UL
#define SIMPLEOS_TRAP_UART_THRE 0x20U

static void rv64_trap_putc(char c)
{
    volatile unsigned char *uart = (volatile unsigned char *)SIMPLEOS_TRAP_UART_BASE;
    for (unsigned int spin = 0; spin < 100000U; spin++) {
        if ((uart[SIMPLEOS_TRAP_UART_LSR] & SIMPLEOS_TRAP_UART_THRE) != 0U) break;
    }
    uart[SIMPLEOS_TRAP_UART_THR] = (unsigned char)c;
}

static void rv64_trap_puts(const char *s)
{
    while (*s) {
        if (*s == '\n') rv64_trap_putc('\r');
        rv64_trap_putc(*s++);
    }
}

/* Raw hex, nibble by nibble. Never an integer-to-text runtime call. */
static void rv64_trap_puthex(unsigned long v)
{
    static const char digits[] = "0123456789abcdef";
    rv64_trap_puts("0x");
    for (int shift = 60; shift >= 0; shift -= 4) {
        rv64_trap_putc(digits[(v >> shift) & 0xFUL]);
    }
}

/* --- kernel stack guard ---------------------------------------------------
 * linker_riscv_common.ld lays .stack (8 MB) immediately BELOW .bss/.data/.text
 * with no MMU and every page RWX, so a blown kernel stack takes NO fault at
 * all: it silently overwrites .bss, then .data, then code, and the machine
 * wanders off. That is indistinguishable from a reset on the serial console.
 * Painting the bottom of the stack and testing the paint at the single
 * allocation funnel turns that class of failure into one named line. */
extern unsigned char _stack_bottom[];

#define RV64_STACK_GUARD_WORDS 8U
#define RV64_STACK_GUARD_MAGIC 0x5A5AC0DEDEADBEEFUL

static int g_rv64_stack_guard_painted;
static int g_rv64_stack_guard_reported;

void rv64_stack_guard_paint(void)
{
    volatile unsigned long *g = (volatile unsigned long *)_stack_bottom;
    for (unsigned int i = 0; i < RV64_STACK_GUARD_WORDS; i++) {
        g[i] = RV64_STACK_GUARD_MAGIC + (unsigned long)i;
    }
    g_rv64_stack_guard_painted = 1;
}

/* 0 = intact (or not painted yet), 1 = smashed. */
int rv64_stack_guard_smashed(void)
{
    if (!g_rv64_stack_guard_painted) return 0;
    volatile unsigned long *g = (volatile unsigned long *)_stack_bottom;
    for (unsigned int i = 0; i < RV64_STACK_GUARD_WORDS; i++) {
        if (g[i] != RV64_STACK_GUARD_MAGIC + (unsigned long)i) return 1;
    }
    return 0;
}

/* Called from the single allocation funnel (rv_alloc, via RV_ALLOC_GUARD_CHECK
 * in baremetal_stubs.c). Reports ONCE and parks: continuing after the stack has
 * eaten .bss produces arbitrary behaviour, and pretending otherwise is exactly
 * the fail-open this whole file argues against. */
void rv64_stack_guard_check(void)
{
    if (g_rv64_stack_guard_reported) return;
    if (!rv64_stack_guard_smashed()) return;
    g_rv64_stack_guard_reported = 1;
    unsigned long sp = 0;
    __asm__ volatile("mv %0, sp" : "=r"(sp));
    rv64_trap_puts("\n[FATAL] kernel stack overflow: the .stack guard below "
                   "_stack_bottom was overwritten\n[FATAL]   _stack_bottom=");
    rv64_trap_puthex((unsigned long)_stack_bottom);
    rv64_trap_puts(" sp=");
    rv64_trap_puthex(sp);
    rv64_trap_puts("\n[FATAL] parking\n");
    for (;;) __asm__ volatile("wfi");
}

/* The trap stack. 16 KiB, .bss (NOLOAD), zeroed by crt0.S. */
#define RV64_TRAP_STACK_BYTES 16384U
static unsigned char g_rv64_trap_stack[RV64_TRAP_STACK_BYTES]
    __attribute__((aligned(16)));

static volatile unsigned long g_rv64_trap_depth;

/* Called from rv64_boot_trap_vector with the four CSRs already in a0-a3. */
void rv64_boot_trap_report(unsigned long scause, unsigned long sepc,
                           unsigned long stval, unsigned long faulting_sp)
{
    g_rv64_trap_depth++;
    rv64_trap_puts("\n[TRAP] S-mode exception, the guest is parking here\n[TRAP]   scause=");
    rv64_trap_puthex(scause);
    rv64_trap_puts(" sepc=");
    rv64_trap_puthex(sepc);
    rv64_trap_puts("\n[TRAP]   stval=");
    rv64_trap_puthex(stval);
    rv64_trap_puts(" sp=");
    rv64_trap_puthex(faulting_sp);
    rv64_trap_puts("\n[TRAP]   _stack_bottom=");
    rv64_trap_puthex((unsigned long)_stack_bottom);
    rv64_trap_puts(" stack_guard=");
    rv64_trap_puts(rv64_stack_guard_smashed() ? "SMASHED" : "intact");
    rv64_trap_puts("\n[TRAP] parked\n");
}

__asm__(
".section .text.trap, \"ax\", %progbits\n"
/* norvc, and the alignment INSIDE it: with RVC enabled the assembler emitted a
 * 2-byte c.nop ahead of the label and `rv64_boot_trap_vector` landed at
 * section offset 0x2. stvec's low two bits are the MODE field, so writing a
 * misaligned vector silently selects vectored mode and sends every trap to a
 * garbage base -- the exact silent-fault class this vector exists to end.
 * Verified with objdump: without norvc the label sits at +2, with it at +0. */
".option push\n"
".option norvc\n"
".balign 16\n"
".globl rv64_boot_trap_vector\n"
"rv64_boot_trap_vector:\n"
/* Swap to the dedicated trap stack; sscratch then holds the faulting sp. */
"  csrrw sp, sscratch, sp\n"
"  addi  sp, sp, -32\n"
"  csrr  a0, scause\n"
"  csrr  a1, sepc\n"
"  csrr  a2, stval\n"
"  csrr  a3, sscratch\n"
"  call  rv64_boot_trap_report\n"
"1:\n"
"  wfi\n"
"  j 1b\n"
".size rv64_boot_trap_vector, . - rv64_boot_trap_vector\n"
".option pop\n"
);

extern void rv64_boot_trap_vector(void);

/* Direct mode (stvec[1:0] == 00): every trap enters at the base address. */
void rv64_boot_install_trap_vector(void)
{
    unsigned long trap_sp =
        (unsigned long)&g_rv64_trap_stack[RV64_TRAP_STACK_BYTES];
    trap_sp &= ~(unsigned long)15U;
    __asm__ volatile("csrw sscratch, %0" :: "r"(trap_sp));
    unsigned long base = (unsigned long)rv64_boot_trap_vector;
    /* Fail LOUD rather than install a vector whose low bits would be read as
     * stvec's MODE field. Silence here would reproduce the very defect this
     * whole block exists to end. */
    if ((base & 3UL) != 0UL) {
        rv64_trap_puts("\n[FATAL] trap vector is misaligned, refusing to install "
                       "stvec: base=");
        rv64_trap_puthex(base);
        rv64_trap_puts("\n[FATAL] parking\n");
        for (;;) __asm__ volatile("wfi");
    }
    __asm__ volatile("csrw stvec, %0" :: "r"(base));
}
