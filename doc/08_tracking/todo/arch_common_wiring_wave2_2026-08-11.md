# arch/common wiring — wave 2 disposition (2026-08-11)

`src/os/kernel/arch/common/` was authored on 2026-04-25 ("Wave 2 AC-3 helper
extraction") and had **zero importers**. Commit `4758bcfd952` wired the first
three (`entropy_mix`, `cstart_bridge`, `canary_state`). This record dispositions
the remaining ten so the layer stops being an open-ended "unwired" claim.

Method (unchanged): keep the per-arch file — `hal_trait_surface_spec` asserts one
per arch — and reduce it to a forwarder holding only the genuinely arch-specific
binding. Only unify what is genuinely arch-independent; MMIO/register-level
differences are NOT arch-independent.

## WIRED

| helper | what was deduped | where |
|--------|------------------|-------|
| `gic_common` | 16 GICv2 GICD/GICC register OFFSETS, byte-identical copies in `arm32/interrupt.spl` and `arm64/interrupt.spl`. The MMIO `GICD_BASE`/`GICC_BASE` stay per-arch — a base address is a platform fact, not a GIC-architecture fact. | `arch/arm32/interrupt.spl`, `arch/arm64/interrupt.spl` |
| `sbi_shim` (wave 3) | The seven SBI error codes (`SBI_ERR_*`, i64) and the extension IDs were duplicated between `arch/common/sbi_shim.spl` and `arch/riscv64/sbi.spl`. `riscv64/sbi.spl` now imports them; **zero casts** — the shim's extension IDs were retyped `i64 -> u64` (an ext ID is an unsigned a7 value), which is rv64's native width, so this is the same same-width alias shape as `x86_descriptor`. The `ecall` trampoline (`extern fn rt_riscv64_sbi_call` / `fn sbi_call`) is the genuinely arch-specific part and stays in the arch file. `SBI_SUCCESS` and `SBI_EXT_SYSTEM_RESET` remain as this file's historical spellings, now derived (`= SBI_OK`, `= SBI_EXT_SRST`) rather than fresh literals. **Latent defect fixed:** `SbiResult.val` used the reserved keyword `val`, so the struct could not be constructed by named argument at all (`SbiResult(err: 0, val: 0)` → parse error) — the field is now `value`. Nothing consumed it, which is why the module having zero importers hid the defect. The four legacy ext IDs (putchar/getchar/send-IPI/shutdown) were added to the shim so all three live copies are covered. | `arch/riscv64/sbi.spl`, `arch/common/sbi_shim.spl` |
| `x86_descriptor` | The x86 GDT selector table existed in five copies with three different value sets. `arch/x86_32/cpu.spl` and `arch/x86_64/gdt.spl` now forward; `interrupts/gdt.spl` remains the live builder and the spec asserts agreement. **Latent defect fixed:** the shared copy had `SEL_USER_CODE_64 = 0x18\|3` — that is the 32-bit COMPAT slot, not the 64-bit user code segment (live value `0x28`), and it baked RPL into the constant. RPL is now a separate `RPL_USER`. | `arch/x86_32/cpu.spl`, `arch/x86_64/gdt.spl`, `arch/common/x86_descriptor.spl` |

Coverage: `test/01_unit/os/multiarch/arch_common_wave2_dedupe_spec.spl`
(mirrored in `test/unit/`), 16/16 GREEN. The pre-existing
`arch_common_dedupe_spec.spl` stays 12/12 GREEN.

Wave 3 coverage: `test/01_unit/os/multiarch/arch_common_wave3_sbi_dedupe_spec.spl`
(byte-identical mirror in `test/unit/`), 11/11 GREEN. Regression-checked GREEN
alongside it: `hal_smp_spec` 12/12, `hal_riscv64_phase_a_spec` 6/6.
`riscv64_syscall_raw_contract_spec` is 3/4 — **pre-existing**, measured 3/4 both
with and without these edits (`semantic: variable sbi_probe_then_send_ipi not
found`, in the stdlib baremetal riscv module, untouched here).

## Re-affirmed on 2026-08-11 (reasons re-read, not overridden)

`paging_walker` and `interrupt_dispatch` are **redesigns, not extractions** —
the common module is a trait-table / `IrqTable` design whose per-arch
counterparts are PTE-bit-layout and XLEN-typed storage. Forcing them would be an
MMU/IRQ rewrite disguised as a dedupe, and is not done. `timer_math` stays
deferred on the same grounds as before: substituting Q32 fixed-point for the
per-arch exact divide CHANGES NUMERIC RESULTS to delete two one-line
expressions. `console_framing` and `relocations` have no per-arch counterpart at
all — there is nothing to dedupe, and the modules are authored-not-extracted.
No kernel build or WM gate was run for this change (constants-and-forwarders
with identical values); anything needing one is recorded above as deferred.

## SKIPPED — with reason

| helper | reason |
|--------|--------|
| `paging_walker` | Per-arch `paging.spl` (6 files, 418-626 lines each) is PTE-bit-layout and MMIO-register level: `_flags_to_pte_bits`, `_pte_phys_addr`, `_read_pte` differ per format (LPAE / long-mode / Sv32 / Sv39 / Sv48) and per XLEN. The common module is a *trait-table redesign*, not an extraction of those bodies. Rewiring is an MMU rewrite with no test coverage. |
| `interrupt_dispatch` | Per-arch handler tables are XLEN-typed and differently sized (`[u32;256]` arm32, `[u64;256]` arm64, `[u32;64]` riscv32); handler width is genuinely pointer width. The common `IrqTable` struct is a different design, not the extracted storage. |
| `timer_math` | `ticks_to_ns` here is a **32.32 fixed-point approximation**; the per-arch sites (`arm32/timer.spl`, `arm64/timer.spl`) do exact `elapsed * 1e9 / freq`. Substituting changes numeric results with no timer test coverage, to remove two one-line expressions. `x86_64/timer.spl` uses a third algorithm (sec/rem split, for i64 overflow). |
| `console_framing` | No per-arch counterpart exists. The ANSI-strip and UTF-8-boundary state machines were authored, never extracted — there is nothing to dedupe. The only overlap is the literal bytes `0x0D`/`0x0A`; replacing hex literals with imports is over-engineering. |
| `sbi_shim` — **rv64 now WIRED** (see above); rv32 half still deferred | The original deferral over-estimated the work: it assumed a cast at every `ecall` SITE. In fact the width binding is needed only at the DEFINITION, and on rv64 no cast is needed at all. What remains deferred is `riscv32/sbi.spl`, whose six shared ext IDs are `u32`: aliasing them would need a module-level `= SHARED as u32`, a width-crossing construct not yet exercised anywhere in this layer and adjacent to the documented "module-level val reads zero" hazard, on the riscv boot path with no kernel build gate available on this host. Instead the rv32 values are **pinned by assertion** in `arch_common_wave3_sbi_dedupe_spec` so they cannot drift from the shim silently. Convert when a riscv32 build gate is runnable. |
| `sbi_shim` — `src/lib/nogc_async_mut_noalloc/baremetal/riscv/sbi.spl` | Third live copy of `SBI_EXT_BASE`/`SBI_EXT_IPI`/`SBI_EXT_LEGACY_IPI` (values agree with the shim). **Not wirable as-is:** it is stdlib, and importing `os.kernel.arch.common.*` from `src/lib/**` inverts the layering. Correct fix is to move the SBI constant set down into the baremetal riscv module and have `arch/common/sbi_shim.spl` import UP from stdlib — a directional change worth doing deliberately, not as a side effect of this sweep. |
| `relocations` | Zero consumers anywhere in the tree: `/usr/bin/grep -rn` for `R_X86_64_`, `R_AARCH64_`, `R_RISCV_` over unrestricted scope returns only this file's own definitions. No duplication exists to remove. (The only `R_*` users are the compiler's own linker specs, a different layer.) |
| `context_layout` | Per-arch `context.spl` is register save/restore. The stack alignment and callee-saved counts appear per-arch only in DOC COMMENTS, never as code constants — there is no duplicated code to collapse. |

## Note on the audit report

`src/os/port/multiarch_audit_report.spl` prints
`"direct_arch_imports_outside_arch": 0` as a hardcoded string literal. It
measures nothing and must not be cited as evidence for any of the above.
