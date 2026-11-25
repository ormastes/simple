# Interpreter logical operators eagerly evaluate the right operand
## Closed 2026-09-16 — RESOLVED 2026-09-06 with executable proof: spec 9/9 green, defect re-injection discriminates

Reviewed in the 2026-09-16 bug-ledger normalization pass; classification is
bookkeeping from in-file evidence, not a re-run of the repro. Re-open with a
fresh dated repro if the symptom returns.

- status: **RESOLVED 2026-09-06 — executable proof landed.** (Was: "source fixed
  2026-07-15; executable interpreter proof pending a runnable pure-Simple
  compiler artifact".) The proof did not need a deployed self-hosted binary
  after all — see "Executable proof (2026-09-06)" below.
- severity: high (unexpected effects and errors)
- component: core tree-walking interpreter

## Symptom

`eval_binary` evaluated both operands before dispatching `and` or `or`.
Consequently `false and effect()` and `true or effect()` still ran `effect`.

## Resolution

After evaluating the left operand, the shared evaluator now returns false for
a false `and` and true for a true `or` without evaluating the right operand.
Focused tests use division by zero on the skipped side and also cover both
paths where the right operand remains required.

## Executable proof (2026-09-06)

Spec: `test/01_unit/compiler_core/interpreter/short_circuit_eval_spec.spl`
(9 `it` blocks: 2 reproduction, 2 control, 5 generalization).

**The blocker in the old status line was a wrong assumption, and that is the
main finding here.** The record assumed proving this needed "a runnable
pure-Simple compiler artifact" — i.e. a deployed self-hosted `bin/simple` that
could *execute a Simple program* through the pure-Simple interpreter. It does
not. A spec can `use compiler.core.interpreter.eval.{eval_expr}` /
`compiler.frontend.core.ast_expr.{expr_binary, ...}` directly, build the AST by
hand, and call `eval_binary`'s dispatcher. The code under test is then
`src/compiler/10.frontend/core/interpreter/eval.spl` itself, even though the
*host* engine running the spec is the Rust seed. Every other row in this family
that is blocked on the same sentence ("executable interpreter proof pending a
runnable pure-Simple compiler artifact") is unblocked by the same technique.

Lane: `SIMPLE_TEST_RUNNER_RUST=1 bin/simple test <spec>` on the Rust seed
`bin/release/aarch64-unknown-linux-gnu/simple` (50093192 bytes, 2026-09-06
09:59). The seed is only the *host*; the *subject* is the pure-Simple
interpreter's own `.spl` source, read from the working tree on every run.
No claim is made about the JIT or native lanes — they never reach this code.

Oracle: a `1 / 0` sub-expression on the operand that must be skipped.
`ops.spl` records `"division by zero"` only when the operand is actually
evaluated, so an empty `ops_get_error()` is direct evidence of the skip
(rather than evidence that nothing happened).

Discrimination proven by deleting the four short-circuit lines from
`eval_binary` and re-measuring in the same tree with the same binary:

```
defect injected : Files: 1   Passed: 3   Failed: 6
restored        : Files: 1   Passed: 9   Failed: 0
```

`git diff --stat` on `eval.spl` was empty after restoring, so the injection
left no residue.

**Runner trap worth recording:** `bin/simple test` caches per spec file by
mtime and *not* by the source under test — the first re-measurement after
injecting the defect printed `Skipped 1 unchanged test(s) (cached)` and a false
`Passed: 3 / Failed: 0`. `touch` the spec before every A/B measurement.

**Separate finding, not fixed here:** the default (pure-Simple)
`bin/simple test <spec>` path — `dispatch_to_simple_app("src/app/test_runner_new/
test_runner_single.spl", ...)` in `src/compiler_rust/driver/src/main.rs:198` —
exits 0 in ~2.7s printing **no verdict, no summary and no test output at all**
in this worktree, for every spec tried (`ops_spec.spl`, `todo_builtin_spec.spl`,
and a three-line hand-written probe). That is a silent vacuous pass on the
default test command. `SIMPLE_TEST_RUNNER_RUST=1` is the documented escape hatch
and is what every measurement above used.


## Verification 2026-11-25 (P1 ledger sweep, Windows worktree) — RESOLVED stands

- **Fix confirmed present in source:** `eval_binary` in
  `src/compiler/10.frontend/core/interpreter/eval.spl:750-758` still returns
  early (`val_make_bool(false)` for a falsy left `and`, `val_make_bool(true)`
  for a truthy left `or`) BEFORE `eval_expr(e_node.right)` — the exact fix
  this record describes, unchanged.
- **Gating spec re-run attempted, environment-blocked:**
  `test/01_unit/compiler_core/interpreter/short_circuit_eval_spec.spl` fails
  as a whole file (0 passed / 1 failed, `error: null`) under
  `SIMPLE_TEST_RUNNER_RUST=1 bin/simple.exe test` on the pinned tracked
  binary (`bin/simple.exe`, 38,403,072 B, Rust seed v1.0.0-rc.1). Cause is
  NOT a short-circuit regression: the spec imports private fns
  (`eval_reset`, `val_reset`, `val_get_bool`, `ops_clear_error` — all
  confirmed non-`pub` in the current source), and the pinned seed now
  enforces private-fn visibility. Reproduced with a minimal spec importing
  only `eval_reset`: same opaque whole-file failure. This is the same
  pinned-seed/source drift class as the `@representation_boundary` rejection
  that blocks the default runner at HEAD (the 2026-09-06 green run used a
  newer aarch64 seed build). The spec needs either `pub` exports in
  `src/compiler` or a seed that matches HEAD's visibility rules — a
  harness/infra item, not this bug.
- No code changed; the 2026-09-16 closure stands on the source inspection
  above plus the original 2026-09-06 executable proof.
