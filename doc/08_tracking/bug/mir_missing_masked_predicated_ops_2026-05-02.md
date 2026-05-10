# Bug: MIR missing MaskFromCmp, MaskedAdd/Mul/Fma, PredicatedAdd/Mul/Fma opcodes

**Date:** 2026-05-02
**Status:** FIXED (opcodes added 2026-05-09; fusion pass body + tests remain for Wave I2)
**Component:** `src/compiler/50.mir/mir_instructions.spl`, `src/compiler/60.mir_opt/mir_opt/predicate_promote.spl`

## Summary

Wave I task I2 requires implementing a liveness pass in `predicate_promote.spl` that
fuses scalar-boolean-comparison-feeding-SIMD-masked-operation patterns into k-register
predicated ops. The pass specification calls for recognising and rewriting these MIR
instruction pairs:

1. `MaskFromCmp { cmp_kind, a, b, out }` followed by `MaskedAdd/MaskedMul/MaskedFma`
   using `out` as a mask → fused `PredicatedAdd / PredicatedMul / PredicatedFma`

None of the required opcodes exist anywhere in the codebase.

## Missing Op Names (exact)

Searched with `grep -rn` across `src/` (excluding `src/compiler_rust/vendor/**`):

| Op name | Expected location | Found? |
|---------|------------------|--------|
| `MaskFromCmp` | `src/compiler/50.mir/mir_instructions.spl` `MirInstKind` enum | NO |
| `MaskedAdd` | `src/compiler/50.mir/mir_instructions.spl` `MirInstKind` enum | NO |
| `MaskedMul` | `src/compiler/50.mir/mir_instructions.spl` `MirInstKind` enum | NO |
| `MaskedFma` | `src/compiler/50.mir/mir_instructions.spl` `MirInstKind` enum | NO |
| `PredicatedAdd` | `src/compiler/50.mir/mir_instructions.spl` `MirInstKind` enum | NO |
| `PredicatedMul` | `src/compiler/50.mir/mir_instructions.spl` `MirInstKind` enum | NO |
| `PredicatedFma` | `src/compiler/50.mir/mir_instructions.spl` `MirInstKind` enum | NO |

Also absent from `doc/04_architecture/simd_unified_architecture_detail.md` and
`doc/05_design/simd_test_catalog.md` — these op names appear nowhere in design docs.

## What Does Exist

The current MIR SIMD opcode set in `src/compiler/50.mir/mir_instructions.spl` (lines
199–241) contains:

- `MirSimdBinop(dest, lhs, rhs, op: text)` — unmasked binary op, `op` encodes `SimdBinop` variant name
- `MirSimdTernop(dest, a, b, c, op: text)` — unmasked ternary (fma/fnmadd)
- `MirSimdCmp(dest, lhs, rhs, op: text)` — comparison producing a mask `LocalId`
- `MirSimdSelect(dest, mask, t, f)` — predicated select (blend)
- `MirSimdMaskOp(dest, lhs, rhs, op: text)` — mask-on-mask boolean ops (And/Or/Xor/Not)

No instruction carries a `mask_mode: SimdMaskMode` field. The `SimdMaskMode` enum
(`Zero`/`Merge`/`Undef`) is defined in `src/compiler/00.common/simd_types.spl` line 267
but is not embedded in any `MirInstKind` variant.

## Actual Skeleton vs. Task Description Mismatch

The existing `predicate_promote.spl` skeleton (Wave E5, 101 lines) implements a
DIFFERENT transformation than what I2's task description specifies:

- **Skeleton intent** (`_z`→`_x` via liveness): Walk `MirSimdMaskOp` instructions whose
  destination carries `SimdMaskMode.Zero`; when liveness proves inactive lanes are never
  read, replace `Zero` with `Undef` (`_x`). Referenced by `simd_unified_architecture_detail.md`
  §5.3 and `simd_test_catalog.md` §3.3.

- **I2 task intent** (`MaskFromCmp`+`Masked*`→`Predicated*` fusion): Completely different
  pattern — requires ops that don't exist in MIR.

Additionally, even the skeleton's own `_z`→`_x` transformation is blocked: `MirSimdMaskOp`
has `op: text` (the mask boolean kind) but no `mask_mode` field. The instruction cannot
currently represent which mode it uses.

## Required Work to Unblock I2

Two options, to be decided by the design owner:

**Option A — Implement the skeleton's intended `_z`→`_x` transformation:**
1. Add `mask_mode: SimdMaskMode` field to `MirSimdBinop` and `MirSimdTernop` in
   `src/compiler/50.mir/mir_instructions.spl` (separate commit per task rules).
2. Implement liveness analysis in `predicate_promote.spl` over `MirSimdBinop` /
   `MirSimdTernop` with `mask_mode == SimdMaskMode.Zero`.
3. Write 8 tests per `simd_test_catalog.md` §3.3.

**Option B — Implement the task-description fusion transformation:**
1. Add `MaskFromCmp`, `MaskedAdd`, `MaskedMul`, `MaskedFma` variants to `MirInstKind`
   in `src/compiler/50.mir/mir_instructions.spl`.
2. Add `PredicatedAdd`, `PredicatedMul`, `PredicatedFma` variants to `MirInstKind`.
3. Implement the fusion pass in `predicate_promote.spl`.
4. Write 8+ tests.

Both options require MIR changes in a separate commit before the pass can be implemented.

## Files to Modify (when unblocked)

- `src/compiler/50.mir/mir_instructions.spl` — add missing `MirInstKind` variants
- `src/compiler/60.mir_opt/mir_opt/predicate_promote.spl` — replace skeleton with real pass
- `test/unit/compiler/mir_opt/predicate_promote_spec.spl` — new spec (8+ tests)
