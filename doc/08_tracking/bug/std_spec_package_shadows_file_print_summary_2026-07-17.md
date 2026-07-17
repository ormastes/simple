# std.spec: package directory shadows sibling spec.spl file, print_summary unreachable

**Date:** 2026-07-17
**Severity:** high (breaks `build_interpreter_result_wrapper`, the shared
zero-executed/spec-failed contract used by the multi-file interpreter test
path and `src/app/test/font_evidence_runner.spl`)
**Status:** open — interpreter/module-resolution defect, NOT fixed as part of
the test-runner greenwash work (out of scope for the runner layer; reported
per the task's escape-hatch instructions)

## Symptom

Any interpreter-mode spec wrapped by
`std.test_runner.test_result_wrapper.build_interpreter_result_wrapper`
(which injects `use std.spec.{print_summary, get_exit_code,
get_executed_test_count}` ahead of the original source, then calls
`print_summary()` / checks `get_executed_test_count()` / `get_exit_code()`
at the end) hard-fails to compile — **even for a genuinely green, one-`it`
spec**:

```
error[E1002]: function `print_summary` not found
  = help: check the function name or import the module that defines it
```

Verified on both the bootstrap seed (`src/compiler_rust/target/bootstrap/simple`)
and the deployed `bin/simple` (which itself currently still prints the
"bootstrap seed only" warning — see Notes).

## Minimal repro

From the repo root (module resolution depends on being inside the tree):

```
cat > scripts/check/fixtures/.repro_spec.spl <<'EOF'
use std.spec.{print_summary, get_exit_code, get_executed_test_count}
use std.spec.*

describe "sanity":
    it "passes":
        expect(1).to_equal(1)

print_summary()
if get_executed_test_count() == 0:
    panic("test-runner: no examples executed")
if get_exit_code() != 0:
    panic("test-runner: spec failed")
EOF
bin/simple run scripts/check/fixtures/.repro_spec.spl
# → error[E1002]: function `print_summary` not found
rm scripts/check/fixtures/.repro_spec.spl
```

Also reproduces with the import fully qualified
(`use std.nogc_sync_mut.spec.{print_summary, get_exit_code,
get_executed_test_count}`) — qualifying the family does not help.

## Root cause

Every family under `src/lib/` that has BDD spec support ships BOTH:

- `src/lib/<family>/spec.spl` — a real implementation (`nogc_sync_mut`) or a
  re-export shim (`nogc_async_mut`, `gc_*`) that includes `print_summary`,
  `get_exit_code`, `get_test_count`, `get_executed_test_count`.
- `src/lib/<family>/spec/__init__.spl` — a package directory with its OWN
  (different, weaker) `pending`/`check`/`check_msg`/`skip`/`skip_it`/`step`
  plus re-exports from `condition.spl`/`decorators.spl`/`env_detect.spl`/
  `feature_doc.spl`. This directory package does NOT export
  `print_summary`/`get_exit_code`/`get_test_count`/`get_executed_test_count`
  at all.

`use std.spec...` (qualified or not) resolves to the `spec/` package
directory, not the sibling `spec.spl` file, so the file's exports —
including the three functions the result-wrapper contract depends on — are
unreachable via that import path. (`describe`/`it`/`expect`/`pending` still
appear to work because interpreter-mode intrinsic BDD reporting handles those
independently of which module resolves — see Notes.)

This means `build_interpreter_result_wrapper`
(`src/lib/nogc_sync_mut/test_runner/test_result_wrapper.spl`) and its only
current callers — `run_test_file_interpreter` in
`src/lib/nogc_sync_mut/test_runner/test_runner_execute.spl` and
`src/app/test/font_evidence_runner.spl` — are exercising a harness that has
never actually run successfully at runtime; its only regression coverage
(`test/01_unit/lib/test_runner_result_wrapper_spec.spl`) checks the
*generated wrapper text* only, never executes it, so this defect went
uncaught.

## Impact

- Any `bin/simple test --mode=interpreter` run that goes through
  `run_test_file_interpreter` and hits this wrapper will report every file as
  FAILED (`function print_summary not found`), including genuinely green
  specs, UNLESS something else masks it (e.g. a different execution mode is
  actually selected by default).
- `src/app/test/font_evidence_runner.spl` cannot currently produce a real
  PASS for any spec — it always hits this compile error.

## Suggested fix direction (not implemented here)

Either:
1. Add `print_summary, get_exit_code, get_test_count, get_executed_test_count`
   to the re-export list in every `src/lib/<family>/spec/__init__.spl` so the
   package directory exposes the same summary/exit-code API as the sibling
   file, or
2. Give the module resolver a way to reach the file when both a file and a
   same-named directory exist (today the directory silently wins), or
3. Move `print_summary`/`get_exit_code`/`get_test_count`/
   `get_executed_test_count` into the `spec/` package directory itself (as
   the canonical home) and have `spec.spl` re-export from there instead.

Whichever direction is chosen, add a RUNTIME (not just string-shape)
regression spec that actually executes a wrapped file end-to-end, since the
existing `test_runner_result_wrapper_spec.spl` did not catch this.

## Notes

- `bin/simple` (`bin/release/x86_64-unknown-linux-gnu/simple`, last built
  2026-07-11) still prints "WARNING: this Rust-built Simple binary is a
  bootstrap seed only" at startup when running `.spl` files in interpreter
  mode, and also currently rejects `rt_cli_arg_count`/`rt_cli_arg_at`
  (`error: semantic: unknown extern function: rt_cli_arg_count`) — i.e. it is
  stale relative to the current source tree (the externs ARE registered in
  `src/compiler_rust/compiler/src/interpreter_extern/cli.rs`). This blocks
  any spec that calls `cli_get_args()` (including
  `src/app/test_runner_new/test_runner_single.spl` and the existing
  `test/03_system/check/test_runner_single_example_failure_contract_spec.spl`,
  which invokes it via `bin/simple run ...` in every `it` block) from running
  via the deployed `bin/simple` until it is rebuilt/redeployed. This is a
  pre-existing, unrelated deployment-staleness issue, not something
  introduced by the greenwash fixes.
- `describe`/`it`/`expect`/`pending` continuing to work despite this
  resolution gap is itself evidence that BDD block execution is handled by
  interpreter intrinsics rather than by whichever `.spl` module `std.spec`
  resolves to — worth confirming explicitly if anyone relies on the `.spl`
  fallback implementations (e.g. compiled/native mode) matching intrinsic
  behavior exactly.

## Cross-refs

Discovered while fixing
[[test_runner_zero_executed_single_file_greenwash_2026-07-17]], which works
around this by counting real ✓/✗ execution markers directly instead of using
the result-wrapper contract.
