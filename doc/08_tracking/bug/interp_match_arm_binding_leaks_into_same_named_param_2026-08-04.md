# Interpreter match-arm binding leaks into same-named param/outer variable

- Status: FIXED
- Status re-verified 2026-08-17 by source inspection (triage shard 01).
- **Component:** Rust seed tree-walk interpreter
- **Severity:** High — silent runtime data corruption

## Symptom

A `case Ctor(x)` payload binding whose name collides with an enclosing
function's parameter or an outer variable **permanently overwrites** that
variable after the match arm runs. First observed 2026-07-30 as an
impossible-looking "class MirOperand has no field named signature" error:
`compile_instruction`'s `case Call(dest, func, args):` arm bound a
`MirOperand` to `func`, corrupting the enclosing `func: MirFunction`.
See `cuda_backend_mirop_signature_field_semantic_false_positive_2026-07-29.md`.

## Root cause

Three interpreter match-arm execution sites inserted pattern bindings
directly into the live environment and never restored what they shadowed:

- `src/compiler_rust/compiler/src/interpreter_control.rs` — `exec_match_core`
  (shared by `exec_match` and `exec_match_expr` statement paths)
- `src/compiler_rust/compiler/src/interpreter_call/block_execution.rs` —
  two duplicated `Node::Match` handlers in the block-closure executors

The match-*expression* evaluator in `interpreter/expr/control.rs` already ran
arms in a cloned `arm_env` and was not affected.

## Fix

At each site: `env.insert` now records the previous value per binding name
(`Option<Value>`), the arm body executes, then bindings are restored
(previous value re-inserted, or the name removed if it did not exist) —
including on the error path, before `?` propagation.

## Probe evidence

Probe spec (same-named param leak, same-named outer val leak, cross-call
leak, in-arm visibility):

- Before fix (interpret lane): `Results: 4 total, 2 passed, 2 failed` —
  `same_fn_leak(7)` returned 999, `outer_var_leak()` returned 777.
- After fix: `Results: 4 total, 4 passed, 0 failed` on `bin/simple test`,
  and the run-mode probe prints `VERDICT: ALL PASS` on `bin/simple run`.

Binary identity was verified by a positive capability probe (running the
probe through each binary) rather than by mtime or size: both the deployed
`bin/release/x86_64-unknown-linux-gnu/simple` and the
`src/compiler_rust/target/debug/simple` child that `bin/simple test`
actually delegates to were confirmed fix-bearing.

## Regression gates

- `test/01_unit/lib/gc_async_mut/gpu/browser_engine/dom_build_gpu_offload_spec.spl`:
  `Results: 38 total, 38 passed, 0 failed`
- `test/03_system/gui/web_showcase_full_gpu_offload_spec.spl`: `13 examples,
  0 failures`. Measured by running the spec directly on the fix-bearing
  release binary; the `bin/simple test` runner lane (which delegates to the
  much slower debug build) never reached its `Results:` line under a load
  average of ~30 from a concurrent bootstrap plus parallel agent sessions,
  and its parent shell was killed twice. Both lanes execute the same code.

`bin/simple build check` exits 0 (clippy + rustfmt clean on both edited
files). Its "Running Tests" stage reports `error: unknown command 'test'`,
a pre-existing harness quirk unrelated to this change.

## Landing note

This session's working copy was silently reverted twice by a parallel
session (both edited `.rs` files at 02:15, and this bug doc twice), so the
fix was landed from blobs hashed straight into the object store via the
plumbing CAS protocol rather than from the shared working copy.
