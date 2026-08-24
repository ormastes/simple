# Bug: SG-1.3 bulk-copy recognizer is index-blind (latent miscompile footgun)

- **ID:** sg13_bulk_copy_recognizer_index_blind
- **Severity:** P0 when enabled; legacy flag path quarantined
- **Area:** compiler / 60.mir_opt (self-hosted), C backend lowering
- **Status:** REOPENED AND QUARANTINED 2026-08-24 — H1/H2 landed, but the documented M1
  overlap/alias precondition remained unproved. The direct adapter and module hook are
  identities, and the legacy environment flag cannot activate the rewrite.
- **Date:** 2026-06-13

## Summary

`optimize_bulk_copy` (`src/compiler/60.mir_opt/_OptimizationPasses/io_passes.spl`) recognizes a
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

This session landed a conditional `bulk_copy` → `memmove((void*)dst,(void*)src,count*8)`
lowering in the C backend (`emit_bulk_copy`, `c_backend_translate_ops.spl`). It is correct
**only** for a producer that satisfies the complete backend contract: structural conditions
1–4, H1 temporary dead-out, H2 exact element width, and M1 complete-span non-overlap. The
current recognizer does not. A naive
future change that renames/lowers `bulk_copy_hint` → `bulk_copy` (or routes the hint to
`emit_bulk_copy`) without adding the guard is a **silent miscompile**, e.g.
`dst[5]=src[2]; dst[9]=src[7]` becomes a copy of `dst[0..1] = src[0..1]`.

Guard comments are in place at both sites (`optimize_bulk_copy` and `emit_bulk_copy`).

## Fix (to enable the perf path soundly)

An eventual producer must positively verify all structural conditions (`dst[i]=src[i]`,
contiguous `0..k-1`, an uninterrupted run, and constant `k`), H1 temporary dead-out, H2 exact
eight-byte element width, and M1 complete-span non-overlap from region/alias facts. Unknown or
incomplete facts leave MIR unchanged. Reactivation also requires positive activation witnesses,
negative cases for every guard, and semantic differential execution covering overlap, traps,
and partial/zero execution. Structural non-firing tests alone are not a safety proof.

## Draft elision pass + adversarial review (2026-06-13)

A draft `elide_bulk_copy` was implemented (strict consecutive-unit matcher + firing/non-firing
specs, all green at unit level) and then put through an adversarial higher-level review BEFORE
landing. The review found the matcher's structural guard is necessary but **NOT sufficient** —
three additional HIGH-severity miscompile holes that the non-firing specs did not exercise:

- **H1 — temp liveness.** The pass deletes the run's GEP/Load/Store, removing the defs of each
  unit's element pointers and loaded value. It did not verify those temps are dead outside the
  run. If a later instruction uses the loaded value (e.g. `BinOp t = Add ld, 1`) or an element
  pointer, deletion yields a dangling local. **Guard:** before firing, no operand outside the
  run (incl. the terminator) may reference any unit temp. Use `get_inst_uses`
  (`mir_opt/auto_vectorize_analysis.spl:153`).
- **H2 — element stride.** The C backend hardcodes a `count*8` byte memmove (stride 8). GEP
  *addresses* line up at `*8`, but each element Store writes `sizeof(value-type)` bytes — for
  i32/i16/bool/f32 that is < 8, leaving gap bytes the element-wise copy never touches while
  memmove overwrites them with src padding. **Guard:** require every copied element type to be
  exactly 8 bytes. Use `find_local_type` (`mir_opt/outline.spl:675`) + a type-size check; note
  synthetic test fixtures must then populate `MirFunction.locals` with real types.
- **M1 — overlap/alias.** `dst_local == src_local` is a local-id check, not a value check; two
  base locals can hold overlapping pointers. memmove is overlap-safe but not equivalent to a
  *forward* element loop on overlap. Document as a precondition the producer cannot discharge
  cheaply (needs alias analysis).

Decision: the draft was **NOT landed** — shipping it (even flag-gated/default-off) would be
known-unsound codegen. A sound producer must implement H1+H2 guards, add non-firing specs that
exercise BOTH (a temp-used-after case and a sub-8-byte-element case → assert UNCHANGED), and be
re-reviewed. The backend `emit_bulk_copy` precondition now lists conditions 5 (8-byte),
6 (temp dead-out), and 7 (complete-span non-overlap).

## Verification status

- `bulk_copy` → memmove backend lowering: DONE, seed-verified
  (`test/01_unit/compiler/backend/c_backend_bulk_copy_memmove_spec.spl`, 5/0, pins arg order).
- sound producer / elision pass: **NOT DONE**. Commit 4c8d519 added the strict matcher plus
  H1 (temp dead-out) and H2 (8-byte element), but did not prove M1 non-overlap. On 2026-08-24
  the direct adapter, module hook, and environment flag were quarantined. The retained specs
  now require canonical witnesses and rejected shapes alike to remain unchanged. Manual
  execution was intentionally omitted under the user's no-verification instruction.
