# Seed interpreter: a match-expression with a returning arm makes every later statement in the frame cost ~10 ms

**Status:** FIXED in the seed (2026-08-22, see "Mechanism and fix" below). Compiler-side symptom fixed by shape (MATCHRET,
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

## Mechanism and fix (2026-08-22)

Located in `src/compiler_rust/compiler/src/interpreter/expr/control.rs`
(`Expr::Match` in `eval_control_expr`). The `return` arm was a red herring:
the cost is paid by EVERY match expression, returning arms or not, and the
hoisted form only avoided it by removing the match.

The arm ran in `arm_env = env.clone()` and was written back with

```rust
for (key, value) in &arm_env {          // CowEnv::iter = visible_entries():
    if env.contains_key(key) {          // overlay + live module scope + base
        env.insert(key.clone(), value.clone());
    }
}
```

`visible_entries()` materializes every module global the frame can see, and
`env.contains_key` is true for all of them, so after one match expression the
frame's OVERLAY holds every module global, all marked dirty. That is the
"slow mode": `sync_owned_captured_globals` (`interpreter_call/core/function_exec.rs`)
walks the callee overlay on every call return and re-publishes each entry
through `set_owned_global`, so every later statement that calls anything
(loops, `define`, ...) costs O(visible globals) publishes + COW copies.
Script-level globals are not owner globals, which is why a single-file
reproduce is flat; the frame must live in an imported module.

Fix: the write-back is dirty-only — `arm_env.clear_dirty()` after the clone
and `block_exec::copy_back_block_writes(&arm_env, env)` — exactly the path
the if-expression (`BlockClosure`) branch already used. Semantics unchanged:
pattern bindings, arm-local writes to outer names, the refreshed-global
channel and `return`-from-arm (TryError) all behave as before.

Measured on the seed interpreter (`SIMPLE_EXECUTION_MODE=interpret`), module
with N `var` globals, `work(5)` = match expr + three 3-iteration loops each
calling a noop, per call:

| N globals | pre-fix match form | hoisted form | post-fix match form |
|---|---|---|---|
| 30  | 413 us  | 75 us | 79 us |
| 100 | 780 us  | 51 us | 72 us |
| 300 | 2971 us | 52 us | 95 us |

(Post-fix the match form is flat in N and within noise of the hoisted form;
Rust test: 200 calls x 300 globals, hoisted 24.2 ms vs match 22.0 ms, ratio 0.91.
The pins are ratios, not absolutes.)

Pins (fail pre-fix, pass post-fix):
- `src/compiler_rust/compiler/tests/interpreter_match_expr_post_statement_cost.rs`
  (ratio < 3.0 against the hoisted form at 300 globals; plus a semantics test)
- `test/01_unit/compiler/interpreter/match_expr_post_statement_cost_spec.spl`
  with fixture `test/fixtures/interpreter_match_expr_post_statement_cost/shapes.spl`
- rows in `scripts/check/check-perf-regression-tests.shs`

Census (`grep -rn "= match" src/compiler --include=*.spl`): 869 match
expressions in the compiler — 10.frontend 30 sites / 12 files, 20.hir 39 /
10, 50.mir 114 / 18 — of which ~589 have a `return` within the arms. All of
them were paying this per statement on the seed; none needs a source change
now (MATCHRET in `module_import_registration.spl` may stay as is).
