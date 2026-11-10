# native-build worker wrapper exits abnormally, so no coverage-native spec can build (2026-08-31)

Status: STALE 2026-11-11 — host-side 2026-08-31 Linux toolchain state; subjects gone from tree, runner-side fail-closed contract verified live in source (p3-boot12).

`bin/simple test <spec> --coverage --mode=native` never produces a binary on this
host. The compile step (`native-build --backend llvm --source src/lib
--entry-closure --entry <wrapped spec> --runtime-bundle core-c-bootstrap`) exits
non-zero after ~12s with:

    !!!!!! END NATIVE-BUILD TRUNCATED STDERR !!!!!!
    error: native-build worker wrapper exited abnormally (signal or wait failure,
    code -1) before producing a binary; its process group has been terminated.

Reproduce (seed built from the tree, `--no-cache` to defeat the result cache):

    bin/release/x86_64-unknown-linux-gnu/simple test \
      test/perf/graphics_2d/no_duplication_spec.spl --coverage --mode=native --no-cache

Independent of PR #155: reproduces with #155 applied and with it reverted.
Plain `--mode=native` without `--coverage` also fails to compile on this host
(pre-existing `Compilation failed:` arm), so the fault is not coverage-specific.

Why it went unnoticed: until PR #157 this failure was converted into a green
verdict by the coverage interpreter fallback -- the spec was re-run unwrapped on
the interpreter and its pass counts reported as a normal pass. With the
fail-closed default the failure is now visible as
`ABORTED BEFORE EXECUTION ... this is NOT a test result`.

Known remaining (separate, minor): the non-coverage `Compilation failed:
{compile_stderr}` arm still leads with the seed's "bootstrap seed only" banner
instead of the real diagnostic; the `first_line` fix in PR #157 covers only the
abort/degrade messages.

## 2026-11-10 triage (P3 runner2 lane, work/p3-runner2-20261110): runner-side SUPERSEDED; host-side root cause is the native-build lane

Runner-side, both things this bug asked for are on this base
(origin/release/1.0.0):

1. The fail-closed visibility fix (PR #157 lineage) is live in
   `src/lib/nogc_sync_mut/test_runner/test_runner_execute.spl:1473-1494`:
   a coverage run whose wrapper fails to compile returns
   "ABORTED BEFORE EXECUTION ... this is NOT a test result" with
   `mcdc_skip_reason: "coverage-abort: wrapper compile failure"` instead of
   the old silent interpreter fallback.
2. The diagnostic-quality fix called "known remaining (separate, minor)"
   is PARTIALLY landed: `compile_output_diagnostic_line_v1`
   (commit 202ab47c283b, 2026-10-19) now ranks error lines for the
   abort/degrade messages. What is still LIVE is the sibling arm this doc
   named: the non-coverage `Compilation failed:` return
   (`test_runner_execute.spl:1511`) still interpolates raw
   `compile_stderr`, which leads with the seed's "bootstrap seed only"
   banner. That arm's owner is the live twin in src/lib/nogc_sync_mut —
   outside this lane's scope.

The headline failure itself — "native-build worker wrapper exited
abnormally (signal or wait failure, code -1)" after ~12s on the filing
host — is a property of the native-build toolchain on that host (the doc
notes plain `--mode=native` without --coverage failed identically), i.e.
the compiler/native-build lane, not the test runner.

Seed-smoke evidence (Rust seed `bin/simple.exe`, Windows, this worktree):
`bin/simple.exe test <dir> --coverage --no-cache` reaches the wrapper
compile and fails CLOSED with the abort verdict; on this host the wrapper
compile is refused by the build-admission memory gate ("15622 MiB of
RAM/commit headroom free, below the 24576 MiB reserve
(SIMPLE_BUILD_MEMORY_RESERVE_BYTES)") and the abort message names exactly
that diagnostic. No Linux-style signal/-1 worker reaping occurs here, so
the filing host's root cause cannot be reproduced or verified from this
lane; handed back to the native-build lane with the runner-side contract
confirmed green.

---

## Triage 2026-11-10 (p3-boot4 lane, assignment row 28)

**Verdict: STALE — host-specific 2026-08-31 state; reporting gap it named is closed.**

- The reproducer's subject artifact `bin/release/x86_64-unknown-linux-gnu/simple`
  no longer exists in-tree: committed binaries/build byproducts were untracked
  in #1054 (`6b3e640c3fde`). The exact host state (seed built from that tree,
  `--runtime-bundle core-c-bootstrap` compile dying after ~12 s) cannot be
  reconstituted from this lane.
- The complaint's actionable half — the worker's fatal error being lost to
  stderr spill — has been rewritten. `src/app/cli/native_build_main.spl:2298-2346`
  (`native_build_worker_failure_lines_v1`) now classifies the exit-status
  space explicitly: core dump (`dumped core`), Windows native status, POSIX
  signal (SIGSEGV/SIGABRT vs SIGKILL/SIGTERM with OOM-reaper hint), the
  `-1`-without-`[TIMEOUT:]` case (this doc's exact message, now labelled
  "NOT a timeout"), and true timeouts; and `:2285-2291` preserves bounded
  worker **stdout** (which carries the `[build]` step log and real error
  line) on the failure path instead of discarding it.
- The residual core condition (the native compile itself dying on the
  reporter's Linux host even without `--coverage`) is a compiler/runtime
  defect, not bootstrap scripting, and is not verifiable from this Windows
  lane. No change made in this lane.


## Triage 2026-11-11 (P3 boot12 lane, work/p3-boot12-20261111)

**Verdict: STALE — confirms the 2026-11-10 p3-boot4 verdict with first-hand
evidence on this base (origin/release/1.0.0 tip + boot11 merge).**

- Subject binary `bin/release/x86_64-unknown-linux-gnu/simple` absent in this
  worktree (ls rc=2) — the 2026-08-31 filing-host state cannot be reconstituted.
- Reporting rewrite live: `native_build_worker_failure_lines_v1` at
  `src/app/cli/native_build_main.spl:2298` (classifies core dump / Windows
  status / POSIX signal / `-1`-without-timeout / true timeout); bounded worker
  stdout preserved at the :2294 call site.
- Runner fail-closed contract live: "ABORTED BEFORE EXECUTION — coverage
  instrumentation wrapper failed to compile ... this is NOT a test result" at
  `src/lib/nogc_sync_mut/test_runner/test_runner_execute.spl:1007` (degrade
  twin :1033); `compile_output_diagnostic_line_v1` error-line ranker at :1041
  (commit 202ab47c283b verified ancestor of this base).
- Seed-smoke (fresh seed 46fe8f6b6def, label seed-smoke, 2026-11-11):
  `bin/simple.exe test test/01_unit/compiler/driver --coverage --no-cache`
  entered the one-time SCV compile-event-journal inventory cold init and was
  killed at the 150 s bounded probe limit (rc=124). Per this lane's routing
  rules the coverage instrumented-build lane is not retried and no hang is
  re-diagnosed; the filing host's Linux-side worker reaping (signal/-1 after
  ~12 s) stays with the native-build/compiler lane.

No change made in this lane.
