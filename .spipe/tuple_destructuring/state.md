# Lane TUPLE — tuple destructuring does not bind

**Status:** DIAGNOSIS COMPLETE. No compiler fix applied (deliberate — see below).
**Date:** 2026-07-27
**Bug doc:** `doc/08_tracking/bug/tuple_destructuring_does_not_bind_2026-07-27.md`
**Regression spec:** `test/01_unit/compiler/tuple_destructuring_spec.spl` (7/7 green)
**Repros:** `build/tuple_repro/t1..t10`
**Backup:** `/tmp/tuple_lane_backup/`

## Verdict

Flat tuple destructuring is **not** broken. The failing shape is destructuring a
**struct** as if it were a tuple. `process.run` returns `ProcessResult`
(`src/lib/process.spl:8`), not a tuple — so `val (out, err, code) = process.run(...)`
binds nothing.

## Root cause

`src/compiler_rust/compiler/src/interpreter_helpers/patterns.rs:772-790` —
`Pattern::Tuple` arm falls back to `_ => Vec::new()` for any non-tuple/array
value; `bind_collection_pattern` then zips against an empty vec, binding zero
names and returning `()`. No error path exists. HIR side
(`hir/lower/stmt_lowering.rs:1606-1673`) silently degrades to `TypeId::ANY` plus
an integer `Index` into the struct, and never checks arity.

## Cross-`it` "leak"

Not a leak. Pinned with `t8_leak_spec.spl` (bad destructure in `it` B → only B
fails; C and D pass) and `t9_gate_spec.spl`. The real spec's destructure lives in
module-level helper `has_nightly_rustc()` (smoke_rustc_spec.spl:37), reached from
`it` at :66 and `it` at :89 via `rust_gate()`. The error names a callee variable
with no call-frame context, so it reads as a leak in an unrelated example.

## Why no fix applied

Rule 4 of the lane brief: `src/compiler_rust/**` has live lane GFIX. The fix is
in `interpreter_helpers/patterns.rs` and `hir/lower/stmt_lowering.rs` — both in
that tree. Fix sketch (3 steps) is in the bug doc; nothing raced.

## Handoff

- Compiler fix → whoever owns `src/compiler_rust/**` after GFIX lands.
- 22 broken `process.run` call sites across 8 files → lanes FSDICT (`test/**`
  port specs) and the `src/os/**` owner. Not lane TUPLE's paths.
- Two separate defects filed inside the bug doc, do not bundle: nested tuple
  patterns unsupported in HIR lowering (deopts silently); `variable not found`
  carries no call-frame context.

## Not committed

Per lane brief: DO NOT commit or push. Files are in the working tree only.
