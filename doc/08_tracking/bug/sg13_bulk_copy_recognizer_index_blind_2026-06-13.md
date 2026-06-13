# Bug: SG-1.3 bulk-copy recognizer is index-blind (latent miscompile footgun)

- **ID:** sg13_bulk_copy_recognizer_index_blind
- **Severity:** P2 (latent — not currently reachable; becomes P0 miscompile if wired)
- **Area:** compiler / 60.mir_opt (self-hosted), C backend lowering
- **Status:** OPEN (documented, guarded by comments; no sound producer wired)
- **Date:** 2026-06-13

## Summary

`optimize_bulk_copy` (`src/compiler/60.mir_opt/optimization_passes_part2.spl`) recognizes a
bulk array-copy pattern and emits an advisory `bulk_copy_hint(src_base, dst_base, count)`
intrinsic. It is **index-blind**: it counts Stores of the shape
`dst[anyGEP] = Load(src[anyGEP])` with `src_base != dst_base` and fires at `count >= 2`. It
does NOT verify that:

1. the indices match on both sides (`dst[i] == src[i]`, not `dst[5] = src[2]`);
2. the indices are contiguous from 0 (`0..count-1`);
3. the matched GEP/Load/Store form a **consecutive, uninterrupted run** (nothing reads the
   destination region between copy steps — element-wise would observe half-copied state
   that a single `memmove` does not);
4. `count` is a compile-time constant span.

Today this is SAFE: the pass is additive (keeps all element-wise ops) and `bulk_copy_hint`
lowers to a **NO-OP** in the C backend.

## The footgun

This session landed a sound `bulk_copy` → `memmove((void*)dst,(void*)src,count*8)` lowering
in the C backend (`emit_bulk_copy`, `c_backend_translate_ops.spl`). It is correct **only**
for a producer that guarantees conditions 1–4. The current recognizer does not. A naive
future change that renames/lowers `bulk_copy_hint` → `bulk_copy` (or routes the hint to
`emit_bulk_copy`) without adding the guard is a **silent miscompile**, e.g.
`dst[5]=src[2]; dst[9]=src[7]` becomes a copy of `dst[0..1] = src[0..1]`.

Guard comments are in place at both sites (`optimize_bulk_copy` and `emit_bulk_copy`).

## Fix (to enable the perf path soundly)

Add a strict, conservative elision pass (C-backend + `SIMPLE_MIR_BULK_OPS=1` only) that
emits the active `bulk_copy` ONLY when it has positively verified all of: `dst[i]=src[i]`
for `i=0..k-1`, contiguous from 0, the matched ops are exactly consecutive (only the copy's
own GEP/Load/Store, nothing interleaved), and `k` constant. Err toward NOT firing (a miss is
harmless; an over-eager match miscompiles). Verify by MIR module inspection with **non-firing
tests as the safety proof**: non-contiguous indices, reordered indices, and an intervening
dst read must all leave the block UNCHANGED with no `bulk_copy` emitted.

## Verification status

- `bulk_copy` → memmove backend lowering: DONE, seed-verified
  (`test/01_unit/compiler/backend/c_backend_bulk_copy_memmove_spec.spl`, 5/0, pins arg order).
- sound producer / elision pass: NOT DONE (this bug).
