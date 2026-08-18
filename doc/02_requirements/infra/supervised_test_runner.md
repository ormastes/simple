# Feature request: a supervising test runner that survives spec death

- **Filed:** 2026-08-17
- **Status:** PARTIALLY DELIVERED — verified clause-by-clause 2026-08-18 (Lane
  REQ). See § *Verification status* for the per-clause table and the three
  code/contract contradictions found. Not done; not nothing.
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

## Unstable mode — the frozen contract (2026-08-17)

"Unstable mode" is the name of the delivered shape of this request:

- **Per-unit SEPARATE PROCESS for build and for test.** One child per source
  file on the build side, one child per spec on the test side.
- **Run to the END of the source list and the END of the test list.** No early
  exit on a dead unit, on either side.
- **Classified outcomes:** `OK` · `ERROR` · `CRASHED` · `TERMINATED` ·
  `TIMEOUT` · `NOT_RUN`. **`TERMINATED` (rc 143, SIGTERM) and `TIMEOUT` are
  UNVERIFIED and are NEVER failures** — they say the host interfered, not that
  the code is wrong. `NOT_RUN` is likewise not a pass.
- **Default ON for the bootstrap path, OFF for interactive runs**, with an
  explicit `--unstable` / `--no-unstable` flag overriding in either direction.
- **The session daemon stays.** Daemon-served execution remains valid for
  ordinary interactive use; it is not the problem this request solves.

Frozen field/flag names (other lanes depend on them verbatim):
`TestOptions.unstable_mode: bool` (`test_runner_types.spl`); error-text
prefixes on `TestFileResult.error` — `CRASHED:` / `TERMINATED:` / `TIMEOUT:` /
`NOT EXECUTED:`.

### D1 correction — read this before touching `run_all`

**`run_all` is a FILE-SELECTION flag, not a keep-going flag.** It is set by
`--all` / `--whole` (`test_runner_args.spl:299,301`) and `--ci` (`:383`), and
read at exactly three places, all file selection:
`test_runner_files.spl:328,407,468`. Nothing else consumes it.

The keep-going control is **`fail_fast`**, default `false`
(`test_runner_args.spl:184`), whose only effect is the break at
`test_runner_main.spl:448`. And each spec is **already** its own process on the
interpreter lane — `process_run_bounded(...)`, `test_runner_execute.spl:172`.

So "continue past a crash" was already true. The real gaps are: the missing
explicit flag, the collapsed outcome classes (`exit_code == -1` is one
sentinel for both timeout and death-by-signal), the entirely unaddressed BUILD
side, and the absence of any crash fixture.

Layer detail and the earlyoom evidence hazard:
`doc/00_llm_process/layer_expert/test_runner/skill.md`.

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

## Verification status (Lane REQ, 2026-08-18)

Every row below was checked by reading code. Nothing is marked SATISFIED on the
strength of a commit message. **No acceptance run was performed by this lane.**

**Source-location correction:** the runner types/args/execute/fork/output modules
live in `src/lib/nogc_sync_mut/test_runner/`, **not** `src/app/test_runner_new/`.
Only `test_runner_main.spl`, `main.spl` and `test_runner_single.spl` are under
`src/app/test_runner_new/`. The D1 section above cites `test_runner_args.spl:299`
etc. without a directory — read those as the `src/lib/...` copies.

| Clause | Status | Evidence |
|---|---|---|
| R1 per-spec isolation | **SATISFIED, but not by unstable mode** | `process_run_bounded` at `test_runner_execute.spl:186,288,807` and `test_runner_single.spl:193`. It is **unconditional** — `unstable_mode` is never read there. This restates D1: per-spec isolation predates the flag. |
| R2 non-collapsing categories | **SATISFIED** | Set at `test_executor_parsing.spl:442,446,448,449`, `test_runner_fork.spl:80,86,87,92`, `test_runner_execute.spl:71-75`. Counted and printed separately at `test_runner_output.spl:192-216` (`crashed` / `terminated (unverified)` / `timed out (unverified)` / `not run`). |
| R2a `137` (SIGKILL) ⇒ CRASHED | **NOT SATISFIED — code diverges from the frozen contract** | `test_runner_fork.spl:72` `is_outside_kill(signo) = 1 or 2 or 9 or 15`, applied at `:86` — SIGKILL(9) is classified **TERMINATED/unverified**, not CRASHED. Only fault signals (SEGV/ABRT/BUS/ILL/FPE) reach CRASHED (`:87`). An unbudgeted OOM-kill therefore reads unverified. Defensible under earlyoom, but it is **not what this doc froze**; one of the two must move. |
| R2b `137` in the subprocess lane | **NOT SATISFIED** | `test_executor_parsing.spl:444` branches only on `-1 / 143 / 144`. `137` falls through unclassified on that path — the fork lane and the subprocess lane disagree. |
| R3 verdict mandatory | **SATISFIED** | Classification `test_runner_types.spl:202-221` → `Unverified` (`:215-216`) via `test_file_result_is_unverified` (`:226-236`); exit map `:237-245` (`Unverified` ⇒ 5, timeout ⇒ 124). Applied `test_runner_main.spl:1109,1141-1152`, returned `:1199`. Single-spec lane returns **2** for verdict-less at `test_runner_single.spl:1226-1231`. Guard spec: `test/01_unit/.../test_runner/no_verdict_is_unverified_spec.spl`. Note the two lanes use **different** unverified exit codes (2 vs 5) — undocumented. |
| R4 rc read directly | **SATISFIED (as a rule), NOT enforced by code** | The rule holds and `shell()`'s signal collapse — the mechanism that made it unenforceable — is **FIXED** (`doc/08_tracking/bug/shell_collapses_every_signal_death_to_minus_one_2026-08-17.md`). But no check prevents a future pipe; this is convention, not a gate. |
| R5 no parallelism | **SATISFIED (unchanged)** | Nothing in the unstable-mode work introduced concurrency; the sequential constraint is untouched. |
| R6 attribution: path, outcome, exit code | **SATISFIED** | Per-`TestFileResult` path/outcome/code; verdict lines at `test_runner_main.spl:986`. |
| R6 attribution: wall time | **SATISFIED** | `duration_ms` on every `TestFileResult`; totals `test_runner_output.spl:220-223`. |
| R6 attribution: **peak RSS** | **NOT SATISFIED** | No `rss` / `peak_rss` / `max_rss` anywhere in the test-runner sources. The field exists only on the **build** side (`build_outcome.spl:214`) and is filed as always-0: `doc/08_tracking/bug/supervised_builder_unwired_and_no_peak_rss_2026-08-17.md`. R6's stated purpose — telling host contention from a real defect — is therefore only half-served. |
| Contract: `TestOptions.unstable_mode` | **SATISFIED** | `test_runner_types.spl:94`, with `unstable_mode_set: bool` at `:95`. |
| Contract: `--unstable` / `--no-unstable` | **SATISFIED** | `test_runner_args.spl:327-332`; passthrough allowlist `:156`; struct init `:629-630`. |
| Contract: default ON for bootstrap, OFF interactive | **SATISFIED** | `test_runner_main.spl:192` reads `SIMPLE_BOOTSTRAP == "1"`; resolution `:194-200` (explicit flag wins either direction); announced `:203`. |
| Contract: error-text prefixes | **PARTIAL** | `CRASHED:` / `TERMINATED:` / `TIMEOUT:` are produced by the classifier and consumed at `test_runner_output.spl:196-204`. `NOT EXECUTED:` is set at `test_runner_main.spl:949`. Verified as *emitted and counted*; **not** verified end-to-end on a real crashing child by this lane. |
| **Unstable mode changes behaviour** | **NOT SATISFIED — this is the headline gap** | Grep over `src/` shows `unstable_mode` has exactly two consumers: `test_runner_main.spl:194-205` (resolve + print) and the unrelated `parallel.spl`. Its **only** behavioural effect is forcing `fail_fast = false` at `test_runner_main.spl:207`. Isolation and classification are unconditional. So on the test side the flag today is an announcement plus a keep-going toggle — the run-to-end guarantee is real, but nothing else is gated on it. |
| BUILD-side per-unit isolation | **BLOCKED (genuine, and now honest)** | `parallel.spl:402-406` prints that unstable mode is REQUESTED but NOT ACTIVE, with the reason: `build()` is in-process because MIR capsules cannot cross a process boundary. `build_supervised()` is implemented and unit-verified but has **zero callers in `src/`** — `doc/08_tracking/bug/supervised_builder_unwired_and_no_peak_rss_2026-08-17.md` Gap 1. Blocked on a capsule-crossing design, not on effort. |
| Acceptance: five-fixture run | **UNDER TEST BY LANE ACCEPT** | Fixtures exist: `test/fixtures/unstable_mode/{crash,timeout,fail,pass_a,pass_b}_spec.spl` (commit `af0f05f08c5c`). The one-run acceptance execution is owned by another lane; this lane did **not** run it and asserts nothing about its outcome. |
| Acceptance: negative control | **NOT SATISFIED** | No reverted-change control run has been performed or recorded anywhere. |
| Defect 1 (silent green) closed? | **OPEN** | `doc/08_tracking/bug/test_runner_emits_no_result_summary_silent_exit0_2026-08-17.md` remains OPEN. R3's machinery is the intended fix, but the originating defect has not been re-measured as closed. |

### Honest overall verdict

The **classification and verdict-accounting half of this request is real and
landed** (R2, R3, R6-minus-RSS). The **isolation half is not delivered by this
work**: on the test side it already existed and is not gated on the flag; on the
build side it is blocked and now says so out loud instead of pretending.

Three things are marked satisfied in spirit but wrong in detail and should be
reconciled before this doc is called done: the `137`⇒CRASHED contract that the
code contradicts, the two lanes disagreeing on `137` at all, and the two
different unverified exit codes (2 and 5).

## Related

- `doc/02_requirements/compiler/supervised_builder.md` — the build-side twin.
- `.claude/rules/testing.md` § "Silent green: exit 0 is not a pass".
- `doc/08_tracking/bug/run_vs_test_harness_divergence_2026-07-28.md` — `test` is
  the tree-walk interpreter, `run` is the Cranelift JIT; 711 of 23,958 spec files
  call a divergent method and would stay green through any JIT regression. A
  supervised runner does not fix this, but R6's attribution makes it visible.
