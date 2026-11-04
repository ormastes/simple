# Pure-Simple interpreter copies `mut` struct parameters instead of aliasing them

- **Date:** 2026-11-04
- **Status:** fixed (2026-11-04)
- **Severity:** P2 (engine divergence)
- **Area:** `src/compiler/` T1 interpreter, `eval_calls.spl:283`

## Contract

A `mut T` parameter is the exclusive-writer spelling, so the caller observes the
mutation:
- `doc/04_architecture/language/memory_model_implementation.md` (capability table)
- `doc/04_architecture/compiler/array_value_abi_contract.md` §3.2 (write back only `mut` params)
- `src/compiler/50.mir/_MirLowering/function_lowering.spl:847-856` and seed
  `src/compiler_rust/compiler/src/mir/lower/lowering_core.rs:2262-2276` both alias `mut` params

The Rust seed interpreter (`write_back_mutable_arguments`) and Cranelift JIT agree:
`fn f(mut r: Route): r.execution = 99` makes the caller see 99.

## Defect

The pure-Simple T1 interpreter copies the argument regardless of `mut`
(`eval_calls.spl:283`), so the caller keeps the old value. This is the only engine
that disagrees.

## History

`bafc15f38a7` encoded local-copy semantics in
`test/01_unit/compiler/interpreter/borrow_mut_param_write_back_spec.spl`
("by-value struct unchanged" also called `by_value_mut`). A seed patch to match it
was BLOCKED in review on 2026-11-04 because it contradicts the contract above and
creates an interpreter-vs-JIT divergence. The spec now pins both cases: a plain
by-value struct stays unchanged, and a `mut` param writes through (20/20 on the
release/1.0.0 seed).

## Fix direction

Make the T1 interpreter alias `mut` struct params (copy only when not `mut`). Then
add a pure-Simple-interpreter lane run of the same spec.

## Fix evidence (2026-11-04)

Root cause: `eval_function_call` (`src/compiler/10.frontend/core/interpreter/eval_calls.spl`,
param binding ~L283) ran `val_copy_for_parameter` for every param. Fix: consult
`decl_get_param_muts`; `mut` params bind the caller's value_id (alias), and after the
body the final value of `mut` params passed as plain identifiers is written back
(env + LOAD_FAST slot) so whole reassignment matches the seed. Plain params still copy.
Spec `test/01_unit/compiler/interpreter/core_interpret_mut_struct_param_alias_spec.spl`:
RED 2/5 -> GREEN 5/5 (field write, nested field, whole reassign; by-value and class
unchanged). Related interpreter specs (7 files) unchanged, 0 pass->fail.
Limit: whole reassignment write-back covers identifier args only (not `f(a.b)`).
Named-argument calls (`k(r: a)`) are covered; per-decl `mut` flags are memoized.
Known: `two(a, a)` into two `mut` params is last-write-wins; it violates the
exclusive-writer contract and belongs to a checker diagnostic, not the interpreter.
