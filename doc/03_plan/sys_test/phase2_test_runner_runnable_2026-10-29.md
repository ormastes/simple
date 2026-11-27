# Phase 2 test runner and runnable acceptance

The user selected this scope: build with the Phase 2 compiler on `release/1.0.0`, repair executable tests in source comments, Markdown, SSpec, and bare `test`, enable logging, and diagnose with LLDB. This document records acceptance, not successful execution. The root agent owns integration, final review, and landing; parallel repair owners report their exact files and evidence.

## Build and identity

- Record the admitted Phase 2 compiler path, immutable digest, provenance, target triple, and build command. Do not substitute the Rust seed.
- Phase 2 is compiler-only: build the full CLI and test runner from this worktree through the supported bootstrap verification entrypoint. Record output digests and build logs. A linked executable alone does not establish qualification.
- Run a real Hello program with the produced executable. Confirm subprocess tests use that executable through the explicit binary override and through executable discovery without an override.

## Executable acceptance matrix

Run each case once after its relevant implementation changes, recording command, executable digest, exit status, stdout/stderr, and actual verdict count. Use bounded process timeouts and isolated caches, output directories, and test databases. Disable result reuse for correctness probes. Never accept an exit-zero process without an executed verdict.

| Case | Fixture or setup | Required evidence |
|---|---|---|
| Markdown passing | `test/fixtures/doctest/green.md` | One executed passing example; exit 0; no source-comment or spec lane |
| Markdown failing | `test/fixtures/doctest/red.md` | Executed failure; nonzero exit |
| Markdown empty | `test/fixtures/doctest/empty.md` | Explicit no-example diagnostic; nonzero exit |
| Source comments passing | `test/fixtures/doctest/green.spl` with `--spl-doctest` | Executed passing comment examples; exit 0; no unrelated Markdown lane |
| Source assertions | `assert_green.spl`, `assert_red.spl`, `expect_red.spl` in that fixture directory | Real assertion results propagate, including nonzero exits for both failing assertion forms |
| Source comments empty | `test/fixtures/doctest/empty.spl` with `--spl-doctest` | Explicit no-example diagnostic; nonzero exit |
| SSpec passing | `scripts/check/fixtures/test_runner_calibration_green_spec.spl` | Executed passing example; exit 0; no inherited documentation lanes |
| SSpec failing | `scripts/check/fixtures/test_runner_calibration_red_spec.spl` | Executed failing example; nonzero exit |
| Bare test | Isolated small project containing known spec and configured comment/Markdown examples; invoke `test` without a path | Default discovery executes the known examples in configured lanes; log counts and paths; failing example changes aggregate exit status |
| Whole scope | Existing whole-scope regression | `--whole` preserves repository-wide documentation scopes despite positional spec root |

Explicit flags must retain their documented meaning. Test named specs with explicitly requested documentation lanes separately from inherited configuration. Check mixed source files containing both BDD and comments. Unsupported or empty explicit targets must not silently pass.

## Logging and LLDB

Enable `--verbose` for acceptance runs and retain the command in the evidence record. The new stderr diagnostic reports the target and resolved spec/Markdown/source lane booleans; its named-spec regression must observe `spec=true markdown=false source=false`. Combine that diagnostic with execution logs and the artifact record to identify discovered paths/counts, child executable, execution outcome, and relevant elapsed time; use SDN for new structured records. Existing `SIMPLE_TRACE_CASE_EVENTS=1` provides supplementary case-event evidence where supported.

Use LLDB against the actual built executable for at least one bounded failing or runnable probe. Preserve debugger command, executable identity, stop reason, thread backtrace, and process exit status. Distinguish debugger attach restrictions from application failures. After a repaired crash, preserve the original failure and one corresponding successful rerun.

## Regression integrity and stop conditions

Subprocess CLI regression tests must provide child-local `SIMPLE_TEST_DEPTH=0` when intentionally testing a fresh top-level invocation; do not clear the parent recursion guard globally. Ordinary nested tests must remain rejected. Assert verdict counts and lane behavior as well as exit status. Tests that merely inspect source text do not qualify runtime acceptance.

Run required repository guards and affected compiler/core/MCP checks once with the qualified runtime, retaining results. Verify generated spec layout before committing. Review the final diff and PR comments, then land only owned changes. Stop when acceptance passes; never repeat green checks. Limit repair cycles to six and report any remaining blocked or unverified criteria honestly.
