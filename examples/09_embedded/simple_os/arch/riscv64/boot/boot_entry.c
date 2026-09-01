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

void boot_entry(unsigned long hartid, unsigned long dtb)
{
    g_rv64_boot_hartid = hartid;
    g_rv64_boot_dtb = dtb;
    spl_start();
    /* crt0.S parks in `wfi` when this returns, so there is nothing to do here.
     * Returning is the normal path for an entry that completes. */
}
