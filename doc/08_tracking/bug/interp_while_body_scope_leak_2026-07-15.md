# Interpreter while-body locals leak into enclosing scope

- status: **RESOLVED 2026-09-06 — executable proof landed.** (Was: "source fixed
  2026-07-15; executable interpreter proof pending a runnable pure-Simple
  compiler artifact".) No deployed self-hosted binary was needed. Building the
  proof also uncovered a SEPARATE, previously unknown defect that made the fix
  unobservable past the first iteration — see below.
- severity: high (silent caller-state mutation)
- component: core tree-walking interpreter

## Symptom

Both statement and expression `while` evaluators executed their bodies in the
enclosing environment. A body-local declaration could therefore overwrite an
outer binding and remain visible after the loop.

## Resolution

Each successful iteration now opens one body scope and closes it after the body
stops for normal completion, continue, break, return, or error. The regression
test runs two iterations and asserts that an outer same-named binding survives.

## Executable proof (2026-09-06)

Spec: `test/01_unit/compiler_core/interpreter/while_body_scope_spec.spl`
(6 `it` blocks: 2 reproduction, 1 control that proves the body is entered at
all, 3 generalization — write-through of a plain assignment from the body,
scope-stack balance after a loop that runs, and after a loop that never runs).

The "runnable pure-Simple compiler artifact" this record waited on was never
required: the spec imports
`compiler.core.interpreter.eval.{eval_stmt}`,
`compiler.core.interpreter.env.*` and
`compiler.frontend.core.ast_stmt.{stmt_while_stmt, stmt_val_decl, ...}`
directly, builds the `while` statement as an AST by hand, and drives
`eval_stmt_while` in `eval_stmts.spl`. Same technique as
`doc/08_tracking/bug/interp_logical_short_circuit_2026-07-15.md`.

The two reproduction blocks are exactly what the Resolution section promises:
two iterations, an outer `x = 99` that must survive a body-local `val x = 7`,
and a body-local name that must not remain visible after the loop.

Lane: `SIMPLE_TEST_RUNNER_RUST=1 bin/simple test <spec>` on the Rust seed
`bin/release/aarch64-unknown-linux-gnu/simple` (50093192 bytes, 2026-09-06
09:59) as host; subject is the pure-Simple `.spl` source. No JIT/native claim.

## The proof was blocked by a second, unrelated defect (now fixed)

Written against the tree as it stood, this spec came back
`Passed: 3 / Failed: 3`. The scope-leak fix described above is correct; what
failed was every block that needed a **second** loop iteration.

`env_push_scope` recycles a scope slot once that depth has been used before,
and its bucket-head reset was a no-op because the helper took the bucket row as
a non-`mut` (snapshot) array parameter. The recycled slot therefore kept stale
chain heads while its keys array was cleared, and the next `env_define` indexed
element 0 of an empty array:
`error: semantic: array index out of bounds: index is 0 but length is 0`.

Filed and fixed as
`doc/08_tracking/bug/interp_scope_slot_reuse_stale_bucket_heads_2026-09-06.md`.

Measured in one tree with one binary, `git stash` toggling only `env.spl`:

```
defect present : Files: 1   Passed: 3   Failed: 3
fixed          : Files: 1   Passed: 6   Failed: 0
```

That is also the discrimination evidence for this spec: it is not vacuous, and
it detected a real regression the first time it was run.
