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
