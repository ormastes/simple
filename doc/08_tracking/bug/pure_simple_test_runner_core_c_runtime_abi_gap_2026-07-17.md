# Pure-Simple test runner core-C runtime ABI gap

**Status:** Open
**Date:** 2026-07-17
**Owner:** runtime / bootstrap

## Symptom

The admitted Stage 2 compiler can compile and code-generate
`src/app/test_runner_new/main.spl`, but the fail-closed standalone runner does
not link against `core-c-bootstrap`. Rust-hosted bundles are removed for this
entry and must not be used as a workaround.

## Reproduction

Build with the pure-Simple Stage 2 compiler, bootstrap environment variables
unset, `SIMPLE_NO_STUB_FALLBACK=1`, `--backend cranelift`,
`--runtime-bundle core-c-bootstrap`, `--entry-closure`, and no
`--runtime-path` override. The fresh core-C archive still leaves hosted ABI
references unresolved.

Representative missing groups include process/file/fd operations
(`rt_process_exists`, `rt_file_rename`, `rt_fd_write`), collection/text helpers
(`rt_range`, `rt_array_filter`, `rt_string_trim_start`), test execution
(`rt_cli_run_file`), and two Simple closure symbols (`starts_with`,
`run_spl_doctest_mode`). The full retained linker log is
`build/native_probe/test-runner-stage2-core-c-cranelift/build.log`.

## Required fix

1. Port every live runner ABI dependency to the admitted core-C or proven
   ABI-complete pure-Simple runtime; do not re-enable `native_all`.
2. Fix entry-closure ownership for live Simple helpers so they are linked with
   their canonical mangled symbols.
3. Add a runner-specific runtime-symbol inventory gate, then build and execute
   `simple-test` with stub fallback disabled.

## Progress 2026-07-18

- Fixed the CLI preclosure feature-family owner omission: a cache miss now
  falls back to the existing bounded driver resolver, with a
  directory-sensitive cache preventing reuse across source directories.
- Added focused source and behavior regressions for that resolver path.
- A native runner link rerun is still pending. The core-C fd ABI trio
  (`rt_fd_close`, `rt_fd_read_until`, and `rt_fd_write`) and fresh link/runtime
  evidence remain open.

## Acceptance

- Core-C runner link has zero unresolved symbols.
- `simple-test --help` exits successfully.
- The focused module-global function-pointer regression executes through the
  runner.
- The font/SPipe focused suite executes without hosted fallback.
