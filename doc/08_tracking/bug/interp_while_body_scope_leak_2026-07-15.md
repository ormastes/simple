# Interpreter while-body locals leak into enclosing scope
## Closed 2026-09-16 — Status RESOLVED 2026-09-06: executable proof spec landed and passing
## Re-verified 2026-11-25 by code inspection (runtime re-run blocked by seed/decorator incompatibility at release/1.0.0 HEAD)

Reviewed in the 2026-09-16 bug-ledger normalization pass; classification is
bookkeeping from in-file evidence, not a re-run of the repro. Re-open with a
fresh dated repro if the symptom returns.

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


## Re-verification 2026-11-25 (p2w3-ae lane, release/1.0.0 worktree)

The resolution described above is present in current source:

- `src/compiler/10.frontend/core/interpreter/eval_stmts.spl:678-685` — the
  statement-`while` evaluator wraps each iteration's body in
  `env_push_scope()` / `env_pop_scope()` (same pattern in the `for` loops and
  match arms).
- `src/compiler/10.frontend/core/interpreter/env.spl:62-66,68-74` —
  `_reset_scope_buckets` mutates the recycled bucket row in place, the fix for
  the second defect (`interp_scope_slot_reuse_stale_bucket_heads_2026-09-06`).
- Proof spec `test/01_unit/compiler_core/interpreter/while_body_scope_spec.spl`
  exists (5,320 bytes).

Attempted re-run: `SIMPLE_LIB=src bin/simple.exe test
test/01_unit/compiler_core/interpreter/while_body_scope_spec.spl
--mode=interpreter` fails before reaching the spec with
`error: semantic: ... unknown decorator '@representation_boundary'` — the
known release/1.0.0 HEAD source/binary inconsistency (pinned Rust seed
v1.0.0-rc.1 vs tree-wide decorator commit cfd89933699), not a regression of
this fix. **Verdict: STALE-CLOSED, confirmed by code inspection; runtime
re-verification environment-blocked.**
