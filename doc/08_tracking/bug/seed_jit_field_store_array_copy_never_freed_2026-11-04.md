# Seed JIT: field store of an array copies and never frees (`st.buf = o` leaks per iteration)

- **Filed:** 2026-11-04 (jitvoid lane, follow-up 2 of PR #6627)
- **Status:** FIXED for the dead-source case in seed source (2026-11-04); the general "JIT lane frees nothing" baseline remains (see `seed_jit_array_copy_never_freed_2026-10-19`).

## Symptom

PR #6627 made every `obj.f = <array place>` emit `rt_array_copy` (value
semantics). The JIT lane has no release (`MirInst::Drop` is a no-op), so
`var o = ...; st.buf = o` in a loop retained one extra buffer per iteration.

## Why not "release the old field buffer"

Unsafe on this lane: struct literals store array arguments uncopied and the
`array_move.rs` pass hands buffers over on `Let`, so the replaced field buffer
may still be held by a live local or another struct. Freeing it would be a
use-after-free.

## Fix

Extend the existing compile-time move analysis (`mir/lower/array_move.rs`):
`obj.f = Local(o)` where `o` is a `var` array local, provably uniquely owned,
mentioned once in the store and dead after it, hands the buffer to the field
with no copy (`ArrayMoveSites::field_store_locals`, consumed in
`lowering_stmt.rs`). A live source (or one declared outside the loop) still
copies.

## Measurement (seed built from the worktree, `/usr/bin/time -l`, max RSS)

Loop: `var o: [i64] = <16-element literal>; o[0] = i; st.buf = o`.

| iterations | #6627 seed | fixed | control (`st.buf = [o[0]]`) |
|---|---|---|---|
| 100k | 63.4 MB | 45.6 MB | 53.4 MB |
| 400k | 168.2 MB | 98.5 MB | 129.5 MB |

Remaining growth is the pre-existing baseline (fresh literal per iteration is
never freed on the JIT lane).

Regression test: `compiler/tests/jit_field_store_array_handover.rs` — the
dead-local loop's live array bytes must be < 80% of a forced-copy twin
(fails before the fix: `moved=4194432 copied=4194432`), plus value-semantics
cases. Spec: `test/01_unit/compiler/interpreter/nullable_receiver_method_and_field_handover_spec.spl`.


## Follow-up (2026-11-04): replaced buffer is now freed

The remaining linear growth above is gone for function-local structs: the
replaced field buffer is released when provably unshared. 100k: 27.8 MB,
400k: 27.8 MB (flat). Details and proof obligations:
`seed_jit_array_copy_never_freed_2026-10-19.md` § "Field-store release".
