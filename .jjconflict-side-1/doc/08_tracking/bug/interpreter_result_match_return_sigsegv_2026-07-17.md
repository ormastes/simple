# seed driver: `RunningType::Interpreter` SIGSEGVs on `match` over a
# `Result`-returning call with `return` in each arm

**Severity:** medium (crash, not silent-wrong -- found while regression-testing task #170)
**Found:** 2026-07-17, task #170 (BoxInt<<3 tag-shift verification) lane
**Status:** filed, not yet root-caused or fixed -- out of scope for #170

## Symptom

Any program of the shape

```simple
fn get() -> Result<i64, text>:
    return Ok(1)

fn main() -> i64:
    match get():
        case Ok(v):
            return v
        case Err(e):
            return -1
```

run through the Rust seed driver's `Interpreter::run` API with
`RunConfig { running_type: RunningType::Interpreter, .. }` (the pure AST
tree-walking backend, exercised via `driver/tests/test_helpers.rs`'s
`backend_test!(name, interp_jit, ...)` / `backend_test!(name, interp, ...)`
macros) crashes the test process with SIGSEGV. Reproduced with a minimal
`Ok(1)` payload (not a multiple of 8), so this is unrelated to the
BoxInt/tag-shift value bug tracked under task #170 -- it is a crash, not a
wrong value, and it reproduces on trivially-valued payloads.

Confirmed independent of any local change: a clean checkout of
`driver/tests/interpreter_jit.rs` (no new tests added) already SIGSEGVs when
the full file is run under `cargo test -p simple-driver --test
interpreter_jit` (parallel execution, ~112 pre-existing tests) -- the crash
surfaces on an unrelated pre-existing test (`jit_abs_interpreter`, plain
arithmetic, no `Result`/`match` at all) once enough interpreter-backend
tests run in the same process. This suggests the underlying defect may be
a general interpreter-backend resource/state issue (e.g. stack depth,
thread-local corruption, or cross-test global-registry contamination under
parallel `cargo test` execution) rather than something specific to `match`
over `Result`, though the `Result`+`match`+`return`-in-each-arm shape was
the smallest deterministic single-test repro found.

## Reproduce

```rust
// driver/tests/*.rs, using test_helpers::backend_test!
backend_test!(
    mini_result_ok_match,
    interp,
    r#"
fn get() -> Result<i64, text>:
    return Ok(1)

fn main() -> i64:
    match get():
        case Ok(v):
            return v
        case Err(e):
            return -1
"#,
    1
);
```

`cargo test -p simple-driver --test <file> mini_result_ok_match` -> SIGSEGV
(signal 11), no assertion output.

## Impact

- Blocks `interp_jit`-scoped (both-backend) regression tests for any
  `Result`/`match`/`return` combination; such tests must be scoped to `jit`
  only until this is root-caused (see
  `doc/08_tracking/bug/native_result_unwrap_silent_wrong_161_2026-07-14.md`-adjacent
  task #170 regression tests in `driver/tests/interpreter_jit.rs`, which are
  deliberately `jit`-only for this reason).
- Also destabilizes the full `interpreter_jit.rs` suite when run
  multi-threaded (default `cargo test` behavior): observed to crash on an
  unrelated pre-existing test (`jit_abs_interpreter`) once ~112+ interpreter
  tests run together in one process, independent of any change in this
  lane. Running with `--test-threads=1` was not yet verified as a
  workaround; not attempted further since it's out of scope for #170.

## Next steps (not done here, out of scope for #170)

1. Bisect whether the crash is single-test-reproducible in isolation
   (`cargo test <one-test-name>` only) vs. requires the full-file parallel
   run to manifest -- if the former, it's a real per-call defect in
   `RunningType::Interpreter`; if only the latter, it's cross-test/global
   state contamination in the test harness or interpreter singleton state.
2. Root-cause in the tree-walking interpreter's `match`/`case Ok(v)`/`return`
   handling (`compiler/src/interpreter_patterns.rs`,
   `compiler/src/interpreter_call/block_execution.rs`) or in the test
   harness's `Interpreter::new()` per-test isolation.
