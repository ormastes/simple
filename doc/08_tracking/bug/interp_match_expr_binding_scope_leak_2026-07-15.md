# Interpreter match-expression bindings leak into caller scope

- status: **RESOLVED 2026-09-06 — executable proof landed.** (Was: "source fixed
  2026-07-15; executable interpreter proof pending a runnable pure-Simple
  compiler artifact".) No deployed self-hosted binary was needed — see
  "Executable proof (2026-09-06)" below.
- severity: high (silent caller-state mutation)
- component: core tree-walking interpreter

## Symptom

`match` expressions bound identifier patterns before opening the arm scope.
A failed guard or completed arm therefore overwrote an outer variable with the
same name.

## Resolution

`eval_match_expr` now opens the arm scope before pattern matching and closes it
on pattern failure, guard failure/error, body error, and success. Focused tests
cover both a failed guard and a successful binding while asserting that the
outer value remains unchanged.

## Executable proof (2026-09-06)

Spec: `test/01_unit/compiler_core/interpreter/match_expr_binding_scope_spec.spl`
(6 `it` blocks: 2 reproduction — the failed-guard and the successful-arm cases
the Resolution section names — 1 control, 3 generalization).

The "runnable pure-Simple compiler artifact" this record waited on was never
required: the spec imports
`compiler.core.interpreter.eval.{eval_expr}`, `compiler.core.interpreter.env.*`
and `compiler.frontend.core.ast.{arm_new}` /
`compiler.frontend.core.ast_expr.{expr_match_expr, ...}` directly and builds the
match expression as an AST by hand, so `eval_match_expr` in
`src/compiler/10.frontend/core/interpreter/eval.spl` is the subject. Same
technique as `doc/08_tracking/bug/interp_logical_short_circuit_2026-07-15.md`.

Lane: `SIMPLE_TEST_RUNNER_RUST=1 bin/simple test <spec>` on the Rust seed
`bin/release/aarch64-unknown-linux-gnu/simple` (50093192 bytes, 2026-09-06
09:59) as host; subject is the pure-Simple `.spl` source. No JIT/native claim.

Discrimination proven by re-injecting the ORIGINAL defect — swapping
`env_push_scope()` back to AFTER `match_pattern(scrutinee, pattern_eid)`, which
is exactly "bound identifier patterns before opening the arm scope" — then
re-measuring in the same tree with the same binary:

```
defect injected : Files: 1   Passed: 3   Failed: 3
restored        : Files: 1   Passed: 6   Failed: 0
```

`git diff --stat` on `eval.spl` was empty after restoring.

One `it` block asserts the binding IS visible inside the arm body (`match 41:
case captured: captured` returns 41), so "the outer value is unchanged" is not
being satisfied by the binding simply never happening.

**Runner trap:** `bin/simple test` caches per spec file by mtime and not by the
source under test — `touch` the spec before every A/B measurement.
