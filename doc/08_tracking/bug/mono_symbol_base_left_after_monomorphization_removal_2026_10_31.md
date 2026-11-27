# MIR lowering still references the removed monomorphization module

Status: CLOSED (2026-11-01). Severity: P2. Date: 2026-10-31.

`200a05f5bc8` removed monomorphization, but
`src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl:59` still imports
`compiler.mono.monomorphize_integration`, and lines 8666 and 8760-8778 still use
`MONO_SYMBOL_BASE`. On the Phase 1 seed, pure-Simple MIR lowering of a call to a user
function fails with `semantic: variable MONO_SYMBOL_BASE not found`.

Found by a `.to_i64()` regression spec for
`native_to_i64_compound_receiver_2026_10_31.md`: 10 of its 12 scenarios passed and the
2 reaching this path failed. The spec is on branch `work/to-i64-lowering-20261031` and
was not landed. Restore it after this reference is fixed.

## 2026-11-01 closure (verified on origin/release/1.0.0 @ 7c7444b8682)

`src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl` no longer imports
`compiler.mono.monomorphize_integration` (its `use` lines 1-12 import only
`compiler.frontend` / `compiler.mir` modules), and `git grep MONO_SYMBOL_BASE -- src`
returns no match. The `.to_i64()` regression spec on `work/to-i64-lowering-20261031` can
be restored; that restore is a separate packet. Tracked by packet E1 in
`doc/03_plan/compiler/generics/generics_refactoring_formal_verification_plan_2026-10-31.md`.
