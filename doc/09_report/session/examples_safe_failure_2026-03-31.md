# Examples Safe Failure Research

Date: 2026-03-31

## Scope

Investigate why problematic examples appear to "crash" instead of ending with a safe classified result such as parse error, compile error, timeout, or runtime failure.

## Rechecked Cases

- `examples/02_language_features/blocks/custom_blocks.spl`
  - Direct compile result: ordinary parse failure
  - Current output: `function arguments: expected Comma, found RBrace`
- `examples/03_concurrency/async_basics.spl`
  - Prior report already showed timeout behavior rather than a native crash
- `examples/02_language_features/bdd_spec/calculator_example.spl`
  - Direct checker result: ordinary parse failure

## Agent Findings

### Dirac

- `run` path already wraps top-level execution in `catch_unwind`, so Rust panics become fatal errors instead of process aborts.
- `run` path has no default wall-clock timeout; timeout exists only through `SIMPLE_TIMEOUT_SECONDS`.
- `compile` path did not consistently apply equivalent top-level panic containment.
- Some compile argument parsing paths used `std::process::exit(1)` directly, which bypasses cleaner error-return flow.

### Faraday

- No completed result captured during this session.

## Root Cause Model

What users perceive as "crash" currently mixes multiple different failure modes:

1. Ordinary compile or parse failure
2. Rust panic escaping a less-defended CLI path
3. Long-running or stuck execution with no default timeout
4. Self-hosted interpreter/runtime issues in helper tooling

The main issue is not only "crash vs error". It is missing failure normalization at command boundaries. Several paths still do not consistently map internal failures into one of:

- `FAIL`
- `CRASH`
- `TIMEOUT`

## Implemented Changes

### 1. Safer examples checker

Added:

- `src/app/examples_check/main.spl`

Behavior:

- checks files one by one
- applies per-file timeout
- classifies outcomes as `PASS`, `FAIL`, `CRASH`, `TIMEOUT`
- writes a markdown report

CLI wiring added:

- `src/app/cli/main.spl`
- `src/app/cli/cli_helpers.spl`
- `src/app/cli/dispatch/table.spl`

### 2. Safer compile argument handling

Updated:

- `src/compiler_rust/driver/src/cli/commands/compile_commands.rs`

Changes:

- target parsing now returns `Result` instead of hard-exiting
- linker parsing now returns `Result` instead of hard-exiting
- `handle_compile()` now reports the error and returns exit code `1`

### 3. Panic containment on compile path

Updated:

- `src/compiler_rust/driver/src/cli/compile.rs`

Changes:

- top-level compile path now catches panics
- panic is converted into:
  - `fatal: compiler crashed: ...`
  - exit code `101`

## Verification Notes

Confirmed:

- `bin/simple compile examples/02_language_features/blocks/custom_blocks.spl -o /tmp/custom_blocks.smf`
  ends with a normal parse failure, not a native abort.

Confirmed through direct checker execution:

- representative files under `examples/02_language_features` were classified as `PASS` or `FAIL`
- no misclassification into `CRASH` for those checked files

Still open:

- direct interpreted execution of `src/app/examples_check/main.spl` can itself spin in some runs
- this appears to be a self-hosted interpreter/runtime issue, separate from the child example compile result
- cargo-based Rust verification was blocked by existing build directory lock contention during this session

## Current Assessment

The repo has two separate problems:

1. Example files often fail for normal reasons and should be reported as such
2. Some command entrypoints and self-hosted tooling still lack fully consistent safe-end containment

The first problem is now better normalized in the added checker and the hardened compile path.

The second problem still needs runtime/driver follow-up.

## Next Implementation Plan

1. Rebuild the Rust driver and validate `simple examples-check ...` through the normal CLI path.
2. Add default timeout policy for example and app execution paths, not only optional env-driven timeout.
3. Audit remaining top-level CLI commands so all panics become structured fatal errors instead of abrupt exits.
4. Fix the self-hosted interpreter/runtime spin seen while running the checker source directly.
5. Reduce unresolved-export warning noise from module hubs so tooling output is readable and actionable.
