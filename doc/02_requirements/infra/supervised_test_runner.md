# Feature request: a supervising test runner that survives spec death

- **Filed:** 2026-08-17
- **Status:** REQUESTED
- **Domain:** infra / test runner
- **Severity:** P1 — a crashed spec currently ends the suite, and a spec that
  never ran currently reads as a pass

Twin of `doc/02_requirements/compiler/supervised_builder.md`. Same defect shape,
opposite side of the toolchain: the builder must reach the end of the source list,
the runner must reach the end of the suite.

## The ask

A crashing spec must not end the run. Each spec executes as a supervised unit in
its own process; the suite continues; the final report names every crashed spec
**separately from failed ones**.

## Why: measured, today

1. **Silent green is real and OPEN.** `bin/simple test <spec>` has been measured
   printing ~1897 lines — all warnings — with **zero** pass/fail/total lines, and
   exiting **0**. A spec that never ran is indistinguishable from one that passed,
   on the command every session uses as evidence.
   `doc/08_tracking/bug/test_runner_emits_no_result_summary_silent_exit0_2026-08-17.md`
2. **Verdicts are not being obtained at all under load.** Only **2 of 33** `simple
   test` runs on this host reached a verdict in one day; 58 processes were queued
   against 6 slots. Three lanes had specs SIGKILLed (exit 144) rather than merely
   slowed.
3. **`rc=143`/`rc=144` with no `Results:` line means UNVERIFIED, not failed** —
   already a written rule, but nothing in the runner enforces the distinction, so
   contention manufactures phantom failures and phantom passes in equal measure.
4. **Captured output is silently truncated.** `rt_fork_parent_wait_bounded`
   (`src/runtime/runtime_fork.c`) exits its read loop early, truncating captured
   test output repo-wide — so per-spec capture must be verified, not assumed.

## Requirements

### R1 — Per-spec isolation
Each spec runs in a child process. A segfault, abort, or OOM in one spec must not
end the suite.

### R2 — Categories that cannot collapse into each other
Final summary distinguishes at least: `passed` · `failed` · **`crashed`** ·
`timed out` · **`unverified`** (external SIGTERM/SIGKILL) · `not run`.

A crashed spec is reported as CRASHED — **never as passed, never as absent**.
This is the load-bearing requirement: "continue past crashes" implemented by
swallowing crashes into exit 0 would *be* defect 1 above, not a fix for it.

### R3 — Presence of a verdict is mandatory
A spec whose child produced no result line is `unverified`, and the suite exit
code reflects it. Exit 0 must mean "every spec produced a verdict and all
verdicts passed" — nothing weaker.

### R4 — Read status directly
Never through a pipe: `cmd | tail` yields *tail's* status, which has produced
false greens here. Assign rc on the line after the invocation. Signal deaths
surface as 128+N (139 SIGSEGV, 137 SIGKILL, 143 SIGTERM).

### R5 — Do not parallelise to get resilience
Parallel `simple test <dir>` invocations **corrupt the shared test database**
(rule F2); section/directory runs must stay sequential. Isolation is per-spec
process supervision, not concurrency. Respect the 12-slot cap
(`scripts/resource/test-slot.shs`).

### R6 — Attribution
Per spec: path, outcome, signal/exit code, wall time, peak RSS. Needed to tell
host contention apart from a real defect — the single most expensive ambiguity in
this campaign.

## Acceptance

A fixture suite of five specs — one that segfaults, one that infinite-loops (hits
the timeout), one that fails an assertion, and two that pass — must in **ONE** run
report all five correctly, exit non-zero, and never claim five passed.

**Negative control:** with the change reverted, the same fixture must behave
worse. A control that fails to fail means the test is broken, not the code.

## Related

- `doc/02_requirements/compiler/supervised_builder.md` — the build-side twin.
- `.claude/rules/testing.md` § "Silent green: exit 0 is not a pass".
- `doc/08_tracking/bug/run_vs_test_harness_divergence_2026-07-28.md` — `test` is
  the tree-walk interpreter, `run` is the Cranelift JIT; 711 of 23,958 spec files
  call a divergent method and would stay green through any JIT regression. A
  supervised runner does not fix this, but R6's attribution makes it visible.
