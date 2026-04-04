# Anti-Dummy / Anti-Stub Enforcement Report

**Date:** 2026-04-04  
**Status:** Implemented on primary CLI surfaces, with migration debt still open

## What Was Added

- `STUB003` denies explicit `pass_todo(...)` placeholders in production code.
- `SSPEC004` denies print-based skip placeholders in specs/examples.
- `SSPEC005` denies examples that have no real assertion or sanctioned `skip:`.
- `SSPEC006` denies boolean-wrapper assertions such as `expect(a != b).to_equal(true)`.
- the pure-Simple lint path now uses the real `Linter` result stream instead of only fix-rule output.
- the compiled Rust CLI now applies the same quality checks through:
  - `simple lint`
  - `simple verify quality`

## Files Changed

- [main.spl](/home/ormastes/dev/pub/simple/src/compiler/90.tools/lint/main.spl)
- [stub_impl.spl](/home/ormastes/dev/pub/simple/src/compiler/35.semantics/lint/stub_impl.spl)
- [test_quality_gate.spl](/home/ormastes/dev/pub/simple/src/app/verify/test_quality_gate.spl)
- [cli_commands.spl](/home/ormastes/dev/pub/simple/src/app/io/cli_commands.spl)
- [lint_entry.spl](/home/ormastes/dev/pub/simple/src/app/cli/lint_entry.spl)
- [sspec_quality_lint_spec.spl](/home/ormastes/dev/pub/simple/test/integration/app/sspec_quality_lint_spec.spl)
- [verify_test_quality_gate_spec.spl](/home/ormastes/dev/pub/simple/test/integration/app/verify_test_quality_gate_spec.spl)
- [code_quality.rs](/home/ormastes/dev/pub/simple/src/compiler_rust/driver/src/cli/code_quality.rs)
- [verify.rs](/home/ormastes/dev/pub/simple/src/compiler_rust/driver/src/cli/verify.rs)
- [help.rs](/home/ormastes/dev/pub/simple/src/compiler_rust/driver/src/cli/help.rs)
- [anti_dummy_quality_cli_tests.rs](/home/ormastes/dev/pub/simple/src/compiler_rust/driver/tests/anti_dummy_quality_cli_tests.rs)
- [lint.md](/home/ormastes/dev/pub/simple/doc/07_guide/tooling/lint.md)

## Verification

Passed:

- `./bin/simple check src/compiler/35.semantics/lint/stub_impl.spl src/compiler/90.tools/lint/main.spl src/app/verify/test_quality_gate.spl src/app/verify/main.spl test/integration/app/sspec_quality_lint_spec.spl test/integration/app/verify_test_quality_gate_spec.spl test/unit/compiler/lint/stub_impl_spec.spl`
- `./bin/simple test test/integration/app/sspec_quality_lint_spec.spl`
- `./bin/simple test test/integration/app/verify_test_quality_gate_spec.spl`
- `./bin/simple test test/unit/compiler/lint/stub_impl_spec.spl`
- `cargo test -p simple-driver --test anti_dummy_quality_cli_tests -- --nocapture`
- `./bin/simple lint /tmp/bad_quality_spec.spl` -> `SSPEC006`
- `./bin/simple verify quality /tmp/placeholder_spec.spl` -> fails with `SSPEC002` and `SSPEC005`
- `./bin/simple verify quality /tmp/good_spec.spl` -> passes

## Research Basis

- test smell detection as a structural analysis problem:
  - https://testsmells.org/assets/publications/EASE2021_TechnicalPaper.pdf
- explicit failure-path assertion guidance:
  - https://docs.junit.org/5.0.1/user-guide/index.pdf
- mutation testing as a stronger later-stage verifier:
  - https://pitest.org/

## Remaining Debt

- a tree-wide grep still finds many legacy placeholder patterns in `src/` and `test/`
- mutation-style verification has not yet been added
- some source-entry wrappers still have their own interpreter-path issues, but the installed compiled CLI path is now closed

## Repo Debt Snapshot

Representative remaining placeholder-heavy areas from the 2026-04-04 audit:

- `src/os/posix/`
- `src/os/tools/`
- `src/lib/gc_async_mut/gpu/`
- `src/os/userlib/`
- legacy spec buckets under `test/specs/`, `test/app/`, and hardware-oriented integration suites

These no longer block the enforcement feature itself, but they do block a truthful “universal repo-wide cleanliness” claim.

## Practical Status

The feature is now implemented on both the source and compiled CLI paths, but the repo still has migration debt. It should be described as:

- `Implemented with migration debt`
