# Interpreter logical operators eagerly evaluate the right operand

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

## Re-check 2026-09-12 (bug fan-out shard 01) — confirms RESOLVED; bug_db row is stale

Binary: `bin/simple` = Rust seed `bin/release/aarch64-unknown-linux-gnu/simple`,
sha256 `3d120a6f9ab5704b…`, `Simple Language v1.0.0-rc.1` (aarch64 host).

```simple
var hits = 0
fn effect() -> bool:
    hits = hits + 1
    return true
fn probe() -> str:
    val a = false and effect()
    val b = true or effect()
    return "a=" + str(a) + " b=" + str(b) + " effects=" + str(hits)
print probe()
```

```
$ SIMPLE_EXECUTION_MODE=jit         bin/simple run sc.spl   -> a=false b=true effects=0
$ SIMPLE_EXECUTION_MODE=interpreter bin/simple run sc.spl   -> a=false b=true effects=0
```

`effects=0` on both lanes: neither right operand ran. The counter is the point —
asserting only `a` and `b` would pass even if `effect()` had run, which is the
whole defect. This row's own status has read **RESOLVED 2026-09-06** since the
executable proof landed; `doc/08_tracking/bug/bug_db.sdn` still carries it as an
open P1. The db row, not the defect, is what needs updating (db sync is the
fan-out lead's step, not edited here).
