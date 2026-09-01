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

void boot_entry(unsigned long hartid, unsigned long dtb)
{
    g_rv64_boot_hartid = hartid;
    g_rv64_boot_dtb = dtb;
    if (__simple_call_module_inits) {
        __simple_call_module_inits();
    }
    spl_start();
    /* crt0.S parks in `wfi` when this returns, so there is nothing to do here.
     * Returning is the normal path for an entry that completes. */
}
