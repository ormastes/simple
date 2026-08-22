# Seed interpreter: a match-expression with a returning arm makes every later statement in the frame cost ~10 ms

**Status:** OPEN (interpreter). Compiler-side symptom fixed by shape (MATCHRET,
`src/compiler/20.hir/hir_lowering/_Items/module_import_registration.spl`).
**Found:** 2026-08-22, while locating the ~40 ms per first-time HIR import
registration (`doc/08_tracking/bug/hir_phase_per_module_cost_2026-08-21.md`,
sixth session).

## Observation

Inside `HirLowering.register_imported_symbol_inner`, on the deployed Rust seed
(`bin/release/x86_64-unknown-linux-gnu/simple`), a scalar statement
`val dbg_n = imported_index + 1` timed with the RIS profile slots costs:

| position | per call |
|---|---|
| function entry | 0.03 ms |
| after `val composite = imported_mod.composite_values[...]` | 0.05 ms |
| after the `same_owner` if-block | 0.01 ms |
| after `val kind = match composite.kind:` (two arms `return`) | **12 ms** |

An empty 3-iteration `for`/`while` loop after that line cost 8-10 ms. Every
later statement in the branch (the field loop, the projection loop, the
`define` call: 8 ms here vs 2 ms called from a spec) paid the same cliff.
Replacing the expression with two hoisted `if ...: return` checks plus
`val kind = if ...: A else: B` removed it (62 ms -> 11 ms per registration on
the fixture in `test/01_unit/compiler/hir/hir_import_registration_per_symbol_cost_spec.spl`).

## Hypothesis (not verified in the seed source)

The seed evaluates a match-expression arm that may `return` on a path that
leaves the frame in a slower mode for the rest of the function (control-flow
signal handling / environment snapshot that is then consulted or re-copied per
statement). Needs a minimal reproduce in `src/compiler_rust/compiler/tests/`
(`val x = match v: case 1: ...; return` followed by N trivial statements,
ratio against the hoisted form).

## Why it matters

`val x = match ...:` with returning arms is an idiomatic shape across the
compiler; every frame using it pays this per statement after the match, so hot
frames (HIR lowering, MIR lowering, parser) are candidates. A census of the
shape and a seed-side fix are owed; until then, hot paths should hoist the
early-exit (as MATCHRET does).
