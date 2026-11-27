# Perf: for-in / enumerate() struct element copy allocates per iteration

- **Date:** 2026-11-05
- **Status:** open
- **Severity:** P2 (perf)
- **Area:** `src/compiler/50.mir/mir_lowering_stmts.spl` (`lower_for_array_indexed`)

## Cost path

The value-semantics fix in `mir_enumerate_struct_binding_skips_value_copy_2026-11-05.md`
binds each struct element through `maybe_copy_struct_value` ->
`copy_struct_value_recursive` (mir_lowering_stmts.spl:599). That ends in
`emit_aggregate`, which the backend lowers to `rt_alloc` (malloc) per iteration
(`aggregate_intrinsics.spl:143`), plus a nil/null guard, N field load/stores and
recursive copies of nested value structs. Reclamation of these per-iteration
records is unverified.

## Upper bound

25,910 `for x in y` loops and 46 `enumerate()` uses in `src/`. Only the
struct-array subset pays; that subset is unmeasured. Class and primitive elements
pay nothing.

## Elision plan

Skip the copy only when ALL hold: the loop variable is never mutated, does not
escape (stored, returned, captured), and the collection is not mutated in the
body (`arr[0].x = 5; use(v.x)` differs under aliasing). Reuse existing hooks:
`_alias_mutated`, `escapes`, `borrow_reference_escapes` (35.semantics, 55.borrow).
Measure before/after (time + RSS) on a struct-array loop benchmark.
