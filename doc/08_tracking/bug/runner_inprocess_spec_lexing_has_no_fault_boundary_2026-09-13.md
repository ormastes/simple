# The test runner lexes spec sources in its OWN process, with no fault boundary
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

- Status: OPEN (2026-09-13)
- Binary: `/home/yoon/dev/cargo-fulltest/release/simple`, sha256 `4dfdf671742007d30210` (Rust seed, 2026-09-13 16:00)
- Base: `origin/main` `f4cd1c306dd`
- Found while fixing `doc/08_tracking/bug/lexer_comment_run_recursion_overflow_2026-09-13.md`

## What is wrong

`bin/simple test <dir>` runs each spec in a CHILD process, so an assertion
failure, a panic or a segfault in the spec is contained and reported. But
before it spawns that child, the runner does real compiler work on the spec's
SOURCE **inside its own process**, and that work has no fault boundary at all.
Any hard failure there kills the sweep: every spec after it in the directory is
never run, never reported, and never counted — the run simply exits rc=1 with
no summary.

Measured 2026-09-13, before the lexer fix: `bin/simple test
test/01_unit/compiler/hir` reported 85 of the directory's 165 spec files and
dropped the other 80 with no indication that anything was missing.

## The call chain

```
app.test_runner_new.test_runner_main::run_test_file
  print "[route] mode=..."                      <- last output before the abort
  run_test_file_interpreter                     (std.test_runner.test_runner_execute)
    env_set("SIMPLE_EXECUTION_MODE", "interpret")   <- sets it on the RUNNER's own process
    preprocess_infix_matchers_only(file_path)
    build_coverage_wrapper(...) / run_test_file_native(...)
      preprocess_spipe_file(file_path)
        simple_string_continuation_lines(content)  (compiler.frontend.core.source_facts)
        simple_code_lines(content)                 -> drives the real CoreLexer
```

Two consequences, both load-bearing:

1. The runner lexes attacker-shaped input (an arbitrary spec file) in the
   process that owns the whole sweep.
2. Because `env_set("SIMPLE_EXECUTION_MODE", "interpret")` lands on the
   runner's OWN environment, that in-process lexing runs under the tree
   interpreter — and therefore under the interpreter's recursion guard —
   rather than the JIT. This is why the recursion-overflow bug reproduced only
   inside a sweep and never when the same spec was run by itself.

## Why `try` cannot fix it

The recursion guard raises `CompileError::StackOverflow`
(`src/compiler_rust/compiler/src/interpreter_state.rs:819`, constructed in
`push_call_depth`, message at `error.rs:514`). That is a Rust-side compile
error that propagates out to the top level and terminates the program; it is
not a Simple-level exception, so no `try` / `??` / matcher in the runner can
observe it. The same is true of a genuine native stack overflow or a segfault
in the in-process compiler path.

## What a real fix requires

A subprocess boundary around the in-process preprocessing — the runner should
either derive the wrapper in the same child that runs the spec, or shell out
for it — so that a spec whose SOURCE defeats the compiler is reported as one
FAIL and the sweep continues. That is a runner redesign, not a small change,
which is why it is filed rather than done here.

## Partial mitigation landed 2026-09-13

`test_runner_main.spl:780` now prints the file path alongside the route line:

```
[route] mode=interpreter file=test/01_unit/compiler/hir/hir_lowering_spec.spl
```

Before this, a crash between two verdict lines named no file at all, and
identifying the offending spec took a from-scratch bisect. This is a
diagnostic, not a boundary: the sweep still dies.

## Related, still uncovered

`CoreLexer.scan_token()`'s newline branch has the same recursive shape that
`handle_indentation()` had — `scan_token_rescan()` once per newline while
`paren_depth > 0`, under `token_requires_rhs`, or on a leading-dot/leading-pipe
continuation. A long run of blank lines inside an open bracket would recurse
identically. This was NOT censused — no file in the tree is known to trigger
it, and none did in the 2026-09-13 sweeps, but that is an absence of
observations, not a measured bound. Recorded rather than fixed.

## Addendum 2026-11-11 — lane runner5: SUPERSEDED (fix verified on refreshed seed)

The redesign this bug called for has landed: a real fault boundary now wraps
in-process spec preprocessing.

- `src/lib/nogc_sync_mut/test_runner/test_runner_execute.spl`
  `preprocess_boundary_failure()` runs before `preprocess_infix_matchers_only`
  and, for any spec that needs isolation (heuristic: >1 MB source or >2000
  consecutive blank lines; `SIMPLE_TEST_PREPROCESS_BOUNDARY=always` probes
  every spec), lexes the source in an ISOLATED child
  (`src/app/test_runner_new/preprocess_probe.spl`,
  `process_run_bounded(..., 120 s)`) instead of in the runner's own process.
  A child crash is converted to ONE spec FAIL
  ("spec preprocessing (lexing) crashed or failed in an isolated child
  (rc=…)") via `_compiler_select_failure`, and the sweep continues. When the
  probe program cannot be located the boundary FAILS CLOSED rather than
  lexing in-process. Ordinary specs never pay for the extra child.
- Ledger `doc/08_tracking/bug/bug_db.sdn:3757` recorded
  "fix-implemented-verification-pending" on 2026-11-07; this addendum supplies
  the pending verification.

Seed-smoke verification on refreshed seed (build-commit 0791c2b7f4a7):
`bin/simple.exe test test/01_unit/app/test_runner_new/preprocess_fault_boundary_spec.spl
--mode=interpreter --no-cache` → **1/1 PASS**. That spec builds a directory
holding a hostile spec (200 000 blank lines inside an open bracket) plus a
good spec, runs `bin/simple test <dir>` through the runner, and asserts the
hostile file is exactly one FAIL naming the front-end fault, the sibling runs
OK, and the runner prints its summary — i.e. the sweep survives a hostile
source instead of dying with no verdict.

Verdict: SUPERSEDED — fault boundary implemented and verified on the
refreshed seed. (The residual "Related, still uncovered" lexer note above is
hardened, not censused; the boundary now contains it if it ever triggers.)

