# Strict-use census batch 4: unmasked pre-existing failures (2026-11-27)

Specs that now load under `SIMPLE_STRICT_USE=1` (after the batch 4 import fixes) and
expose failures that were hidden by the earlier load error. None are regressions from batch 4.

Repro (from repo root):
`SIMPLE_STRICT_USE=1 C:/dev/keep/seeds/simple-local-20261127h.exe test <spec>`

## 1. fe_p256_full_spec: 53 of 55 pass
Spec: `test/01_unit/lib/math/field/fe_p256_full_spec.spl`.
`fe_to_bytes` and `fe_is_zero` assume a reduced (canonical) input; the spec builds the
non-canonical value `p` itself, so both return wrong results on it. Fix: reduce inside
`fe_to_bytes`/`fe_is_zero`, or have the spec build canonical inputs. Failing examples: the two
that feed `p` to `fe_to_bytes` / `fe_is_zero`.

## 2. riscv_noalloc_dtb_capability_spec: 23 of 25 pass
Spec: `test/01_unit/os/kernel/boot/riscv_noalloc_dtb_capability_spec.spl`.
- ISA NUL check failures (the ISA string is not NUL-terminated or checked as the spec expects).
- `src/os/kernel/boot/riscv_noalloc_handoff.spl` lines 86 and 96 never call
  `riscv_noalloc_dtb_capability_init`, so the capability table is never populated on the handoff path.

## 3. cipher_parity_spec: 10 of 12 pass
Spec: `test/01_unit/compiler/mir_opt/cipher/cipher_parity_spec.spl`.
Two failures: the AES-rewrite example, and "full caps produces Intrinsic" (the rewrite does not
yield the Intrinsic form when all capabilities are available).

## 4. hal_smp_ipi_broadcast uses a logical mask at base 0
`src/os/kernel/arch/riscv64/hal_smp.spl` (around line 205; riscv32 twin likewise).
`hal_smp_ipi_broadcast` builds a logical hart mask relative to base 0, which is inconsistent
with the new `hal_smp_ipi_send` window (hart-id base plus mask). Broadcast should use the same
window computation.

See also: `strict_use_default_blocked_by_unprovided_imports_2026-11-27.md`.

## Resolution (2026-11-27, work/census4-unmasked-fixes-20261127)
1. FIXED. `fe_to_bytes` and `fe_is_zero` now apply the constant-time `_fe_sub_p_once`
   before serializing/comparing. fe_p256_full_spec 55/55, fe_p256_skeleton_spec 6/6.
2. FIXED. (a) `riscv_noalloc_handoff` and `riscv_noalloc_handoff_with_layout` now call
   `riscv_noalloc_dtb_capability_init(hart_id, dtb_addr)` right after pinning
   `g_riscv_boot_dtb_addr` and before the RAM-base pin. (b) The "ISA without terminating
   NUL" example was a spec bug: it poked `isa + 14` (alignment padding) but
   "rv64gc_zicbom" is 13 chars so its NUL is at `isa + 13`; the production check was correct.
   Now 25/25.
3. NOT A CODE BUG - OPEN BY DESIGN. Root cause: `run_pattern_idiom_pass_x86`
   (`src/compiler/60.mir_opt/mir_opt/pattern_dispatch.spl`) is an intentional identity since
   f177c893a61 "quarantine unsupported pattern idioms" ("Preserve MIR while PatternIdiom lacks
   complete backend parity"). The two failing examples assert Intrinsic rewrites with full caps,
   which only `run_pattern_idiom_candidate_pass_x86` still performs (no spec calls it). The
   other 10 examples pass vacuously on identity. Fix is an owner decision: either re-enable the
   production pass when backend parity lands, or point these two examples at the candidate
   pass. Left unchanged.
4. FIXED (riscv64). `hal_smp_ipi_broadcast` now resolves each non-self logical hart to its
   physical ID (DTB map, logical==physical fallback) and sends one SBI IPI per 64-hart window
   via `hal_smp_ipi_window`; new helper `hal_smp_ipi_window_mask`, new hal_smp_spec case.
   The riscv32 twin (`hal_smp32_ipi_broadcast`) has no window/base concept (32-bit mask,
   logical==physical, no DTB map), so it is not affected by this defect.

## Review follow-ups (Fable, 2026-11-27)
- rv32 FPGA lane (`src/os/kernel/arch/riscv32/fpga_boot.spl`) forwarded reset-state `a1` into `riscv_noalloc_handoff`; with the restored capability init that is now dereferenced, so a garbage `a1` on a firmware-less M-mode board would trap. Fixed: the lane passes 0, like the rv64 FPGA lanes.
- `hal_smp_ipi_broadcast` loop bound is now `i < MAX_HARTS` (was `n < MAX_HARTS`), so `HAL_SMP_PENDING_IPI[i]` cannot be indexed at 8 when an unclamped test seam sets count > 8.
- DONE (2026-11-27): self-exclusion in `hal_smp_ipi_broadcast` now uses the boot hart PHYSICAL id (`riscv_noalloc_dtb_hart_id(0)`, which holds the observed boot hart even in fallback) via `hal_smp_ipi_broadcast_plan`. `hal_smp_ipi_send` has no self-exclusion (unchanged). Residual: in a count-1 fallback with count>1 state, hart 0 is still not reachable since logical 0 maps to the boot hart. Original note: self-exclusion was by logical 0 only. If the DTB capability falls back (count 1) while `HAL_SMP_CPU_COUNT_STATE` > 1 and the boot hart is not physical 0, the logical==physical fallback can target the boot hart and miss hart 0. Needs the boot hart's physical id from the capability.
- DONE (2026-11-27): broadcast now shares `hal_smp_ipi_windows`/`hal_smp_ipi_broadcast_plan` with the mock, which records windowed (mask, base); spec covers sparse ids 3,7,64,130 and physical self-exclusion. Original note: production loop untested; `hal_smp_ipi_broadcast_with_mock` still models the old logical mask.

## cipher_parity_spec 10/12 (2026-11-27) — DONE
Production `run_pattern_idiom_pass_x86` is a deliberate identity (f177c893a61). The two Intrinsic examples now call `run_pattern_idiom_candidate_pass_x86`; one new example pins the production pass as identity; the all-symbols example no longer expects CRC32 (x86 CRC32 idioms are deliberately unsupported: SSE4.2 crc32 is CRC-32C), with a separate example asserting CRC32 stays Call. Spec: 14/14.
