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
| `x86_descriptor` | The x86 GDT selector table existed in five copies with three different value sets. `arch/x86_32/cpu.spl` and `arch/x86_64/gdt.spl` now forward; `interrupts/gdt.spl` remains the live builder and the spec asserts agreement. **Latent defect fixed:** the shared copy had `SEL_USER_CODE_64 = 0x18\|3` — that is the 32-bit COMPAT slot, not the 64-bit user code segment (live value `0x28`), and it baked RPL into the constant. RPL is now a separate `RPL_USER`. | `arch/x86_32/cpu.spl`, `arch/x86_64/gdt.spl`, `arch/common/x86_descriptor.spl` |

Coverage: `test/01_unit/os/multiarch/arch_common_wave2_dedupe_spec.spl`
(mirrored in `test/unit/`), 16/16 GREEN. The pre-existing
`arch_common_dedupe_spec.spl` stays 12/12 GREEN.

## SKIPPED — with reason

| helper | reason |
|--------|--------|
| `paging_walker` | Per-arch `paging.spl` (6 files, 418-626 lines each) is PTE-bit-layout and MMIO-register level: `_flags_to_pte_bits`, `_pte_phys_addr`, `_read_pte` differ per format (LPAE / long-mode / Sv32 / Sv39 / Sv48) and per XLEN. The common module is a *trait-table redesign*, not an extraction of those bodies. Rewiring is an MMU rewrite with no test coverage. |
| `interrupt_dispatch` | Per-arch handler tables are XLEN-typed and differently sized (`[u32;256]` arm32, `[u64;256]` arm64, `[u32;64]` riscv32); handler width is genuinely pointer width. The common `IrqTable` struct is a different design, not the extracted storage. |
| `timer_math` | `ticks_to_ns` here is a **32.32 fixed-point approximation**; the per-arch sites (`arm32/timer.spl`, `arm64/timer.spl`) do exact `elapsed * 1e9 / freq`. Substituting changes numeric results with no timer test coverage, to remove two one-line expressions. `x86_64/timer.spl` uses a third algorithm (sec/rem split, for i64 overflow). |
| `console_framing` | No per-arch counterpart exists. The ANSI-strip and UTF-8-boundary state machines were authored, never extracted — there is nothing to dedupe. The only overlap is the literal bytes `0x0D`/`0x0A`; replacing hex literals with imports is over-engineering. |
| `sbi_shim` | Extension IDs are SBI-spec constants, but `riscv32/sbi.spl` types them `u32` and `riscv64/sbi.spl` types them `u64`/`i64` because they are passed straight into a register-width `sbi_call` — SBI argument width IS XLEN. Wiring means a cast at every `ecall` site in both files, i.e. touching the register ABI, on the riscv boot path with no build gate available. Deferred, not refused. |
| `relocations` | Zero consumers anywhere in the tree: `/usr/bin/grep -rn` for `R_X86_64_`, `R_AARCH64_`, `R_RISCV_` over unrestricted scope returns only this file's own definitions. No duplication exists to remove. (The only `R_*` users are the compiler's own linker specs, a different layer.) |
| `context_layout` | Per-arch `context.spl` is register save/restore. The stack alignment and callee-saved counts appear per-arch only in DOC COMMENTS, never as code constants — there is no duplicated code to collapse. |

## Note on the audit report

`src/os/port/multiarch_audit_report.spl` prints
`"direct_arch_imports_outside_arch": 0` as a hardcoded string literal. It
measures nothing and must not be cited as evidence for any of the above.
