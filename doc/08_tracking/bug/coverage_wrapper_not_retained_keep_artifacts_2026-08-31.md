# A failing coverage/MC-DC wrapper cannot be captured for inspection

Date: 2026-08-31
Status: FIXED 2026-11-11 — asks #1 (retain on failure) and #2a (name the artifact) implemented in the live runner twin with paired spec evidence; per-run subdirectory isolation (ask #2b) remains open (P3 runner6 lane)
Impact: has blocked **three** separate investigations in one day.

## The gap

`build_coverage_wrapper` (`src/lib/nogc_sync_mut/test_runner/test_executor_parsing.spl`)
and the `spipe_*` native-entry builder
(`src/lib/nogc_sync_mut/test_runner/test_runner_execute.spl:893`) write generated
sources into `_tp_get_temp_dir()` and the runner then deletes them via
`cleanup_native_generated_files`. When one of those generated files fails to
compile, the error text names only the generated path — and by the time anyone
reads it, the file is gone.

`--keep-artifacts` (`test_runner_args.spl:323`) did **not** preserve one in
practice: two runs with `--keep-artifacts` (one also with `--force-rebuild`) left
no `spipe_wrapped__*` or `simple_cov_*` file for either spec. Whether that is a
plumbing bug in the flag or a path where cleanup runs regardless has not been
traced; either way the flag does not currently deliver the artifact.

## Why it matters

The compile error names the ROOT compile unit, never the module the bad
identifier is in:

```
error: compile failed (/mnt/data/tmp/spipe_wrapped__..._spec_native.spl):
  semantic: ...: Undefined("undefined identifier: io_runtime")
```

So the only way to locate a failure is to reconstruct the closure by hand with
probe files. That works, but it answers a *different question* — a probe's
closure is not the wrapper's — and it is exactly how a wrong root cause got
written up and had to be retracted (see
`coverage_wrapper_undefined_identifier_clusters_2026-08-31.md`, cause A). Roughly
20 symbols in that document sit in cause F, unlocatable, purely because no
wrapper can be captured.

## Two things worth fixing

1. **Retain on failure, unconditionally.** A generated source that failed to
   compile should never be deleted, `--keep-artifacts` or not. The artifact is
   the only evidence of the failure and it costs one file.
2. **Name the artifact in the diagnostic, and isolate it per run.** Wrappers are
   written to a shared temp dir (`/mnt/data/tmp` here) under spec-derived names
   with no per-run scoping; wrappers from other concurrent sessions were observed
   appearing there mid-investigation. A per-run subdirectory would make captures
   attributable and rule out cross-run interference — currently listed as an
   unexcluded hypothesis in cause F.

## Suggested acceptance check

A spec whose wrapper fails to compile leaves exactly one readable generated
source on disk, whose path is printed in the error, and
`bin/simple compile <that path>` reproduces the same diagnostic standalone.

## 2026-11-10 triage (P3 runner2 lane, work/p3-runner2-20261110): LIVE — flag plumbing landed, both core asks still open; owner out of lane

Measured on this base (origin/release/1.0.0, Rust seed bin/simple.exe,
Windows worktree), one verification cycle plus follow-up probes:

1. `--keep-artifacts` plumbing EXISTS on every failure arm of the live twin
   (`src/lib/nogc_sync_mut/test_runner/test_runner_execute.spl`: cleanup
   calls at :1456, :1478, :1505, :1512 all pass `options.keep_artifacts`;
   `cleanup_native_generated_file` gates each delete on
   `not keep_artifacts`, :871-894) — unlike at filing time. At filing the
   flag "did not deliver"; the plumbing gap itself appears repaired.
2. Fail-closed abort verified live: `bin/simple.exe test <dir> --coverage
   --no-cache` on a spec whose wrapper cannot compile produced
   "ABORTED BEFORE EXECUTION — coverage instrumentation wrapper failed to
   compile ... this is NOT a test result" with
   `mcdc_skip_reason: coverage-abort: wrapper compile failure`, exit 1.
   On this host the wrapper compile was refused by the
   SIMPLE_BUILD_MEMORY_RESERVE_BYTES admission gate, and the abort named
   exactly that diagnostic ( ranked-line chooser working).
3. Without `--keep-artifacts`, the generated wrapper IS deleted on the
   completed abort (temp dir held 0 `simple_cov_*` files after the run;
   1 while the compile was in flight — lifecycle confirmed).
4. Ask #1 (retain on failure UNCONDITIONALLY, "--keep-artifacts or not")
   is NOT implemented: every retention path is flag-gated; nothing
   retains a failed wrapper by default.
5. Ask #2 (name the artifact in the diagnostic, per-run isolation) is NOT
   implemented: `coverage_wrapper_compile_failure_v1`
   (test_runner_execute.spl:1019) takes no path parameter and the abort
   text names no wrapper file; wrappers still share
   `_tp_get_temp_dir()` (`sosix_test_temp_dir()`, %TEMP% on Windows) under
   spec-derived names with a pid/hash component, no per-run subdirectory.
6. Wrapper artifact itself verified real and readable: a killed mid-compile
   run left `simple_cov_<pid>_<hash>_spec.spl` (62 lines) in the temp dir —
   MC/DC manifest-guarded instrumented copy with the spec body embedded.
   Retention-on-failure evidence remains live-UNCONFIRMED for
   `--keep-artifacts` on this host: the SCV inventory cold-init that gates
   the first instrumented build did not complete within 15 minutes on this
   Windows worktree (git/LFS walk; run killed at timeout, retried without
   timeout, still in cold-init at handoff), so the post-abort retention
   check could not be observed end-to-end. Static plumbing (item 1)
   indicates the flag retains; the filing-time "flag did not deliver"
   observation predates this plumbing.

Not fixed in this lane: the live twin is `src/lib/nogc_sync_mut/...`
(explicitly out of scope); the app twin `src/app/test_runner_new/
test_runner_execute.spl` is dead code ("reached by no import", confirmed
again this session) and editing it would change no behavior. Suggested
owner-lane fix, per this doc's own acceptance check: retain the wrapper
whenever the coverage compile fails (regardless of flag), include
`wrapped_path` in `coverage_wrapper_compile_failure_v1`'s detail, and
scope wrappers to a per-run subdirectory of the temp dir.

## 2026-11-11 triage + fix (P3 runner lane, work/p3-runner6-20261111): LIVE -> FIXED

**Verdict: FIXED.** The 2026-11-10 runner2 lane confirmed both core asks were
still open and suggested the owner-lane fix; this lane owns the test-runner
area, so the fix landed here, in the live twin
(`src/lib/nogc_sync_mut/test_runner/test_runner_execute.spl`; the app twin
`src/app/test_runner_new/test_runner_execute.spl` remains dead code and was
not edited).

What changed (all in `test_runner_execute.spl`):

1. **Ask #1 — retain on failure, unconditionally.**
   `cleanup_native_generated_files` gained a trailing `retain_source_path`
   parameter (now `pub`, so the behaviour is spec-pinned), threaded into
   `cleanup_native_generated_file` as an additional preservation. Both
   coverage wrapper compile-failure arms — the fail-closed abort
   (:1473-1494) and the explicit `SIMPLE_COVERAGE_FALLBACK=interpreter`
   degrade (:1495-1508) — pass the wrapper path, so a failed wrapper
   survives cleanup regardless of `--keep-artifacts`. With the production
   invariant `wrapped_path == cleanup_path` and the staged source deleted,
   exactly one generated source remains on disk, matching this doc's
   suggested acceptance check.
2. **Ask #2a — name the artifact in the diagnostic.** New pure helper
   `coverage_wrapper_retention_note_v1(wrapped_path)`; when a path is in
   scope the abort/degrade messages end with
   `Wrapper source retained at: {wrapped_path}`.
   `coverage_wrapper_compile_failure_v1` takes an optional trailing
   `wrapped_path` (default `""`; the 5-arg call shape and message text are
   unchanged when absent).
3. **Ask #2b — per-run subdirectory isolation: NOT implemented.** Wrappers
   still share `_tp_get_temp_dir()` under spec-derived names. Reason: the
   compile of the relocated wrapper depends on the temp path's relative-import
   resolution behaviour, and this lane cannot run an instrumented build to
   end (the SCV inventory cold-init and the build-admission memory gate block
   it on this host), so an isolation change would ship unverified. Left as
   the remaining open item for a lane that can drive a real coverage build;
   it is hygiene, not evidence integrity — asks #1/#2a cover the acceptance
   check.

**Paired test.** `test/01_unit/app/test/coverage_wrapper_fail_closed_spec.spl`
gained a describe block (5 examples): abort names the retained wrapper path
(compile failure and timeout), message shape unchanged with no path, and two
behavioural examples driving the real `cleanup_native_generated_files`
(retained wrapper survives `keep_artifacts=false`; everything is deleted
without a retention path).

**Seed-smoke evidence (fresh Rust seed bin/simple.exe, build-commit
46fe8f6b6def, SIMPLE_LIB=src,
`bin/simple.exe test test/01_unit/app/test/coverage_wrapper_fail_closed_spec.spl
--mode=interpreter --no-cache`):**
`SPEC FILE VERDICT outcome=OK declared>=16 executed=16 passed=16 failed=0`
(first run 15/16 exposed a test-modelling bug — production never has
`wrapped_path != cleanup_path`; the test was corrected to the production
invariant, not the code).

**Residual / limits.** End-to-end confirmation of retention-on-real-abort is
still unobservable on this host (the wrapper compile is refused by the
SIMPLE_BUILD_MEMORY_RESERVE_BYTES admission gate before a real compile
failure path completes, and the SCV cold-init blocks the instrumented lane);
the behaviour is covered by the direct cleanup test above, and the abort
message contract is unit-pinned. Per-run isolation remains OPEN as stated.
