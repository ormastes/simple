# Feature request: a supervising test runner that survives spec death

- **Filed:** 2026-08-17
- **Status:** PARTIALLY DELIVERED — verified clause-by-clause 2026-08-18 (Lane
  REQ), rows R2a/R2b corrected 2026-08-18 (Lane AUDITFIX), mode scope redefined
  and R1/R2b/R3/headline rows amended 2026-08-18 (Lane REDEFINE). See § *Verification
  status* for the per-clause table. Not done; not nothing.
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

- **Scope of the MODE itself (REDEFINED 2026-08-18, Lane REDEFINE): classification
  + run-to-end + the bootstrap-path default.** The mode does **not** "turn on
  isolation" and never did. Its one behavioural effect in the whole tree is
  `fail_fast = false` (`src/app/test_runner_new/test_runner_main.spl:205-207`)
  — i.e. run to the END of the test list.
- **Per-unit SEPARATE PROCESS for build and for test — a PRECONDITION, not a
  mode feature.** On the test side this is **unconditional** and predates this
  work: `run_test_file_interpreter` (`test_runner_execute.spl:186`), `_smf`
  (`:288`) and `_native` (`:807`) each spawn a child on every path, gated on
  nothing, and that file reads `unstable_mode` **nowhere** (its only textual
  hits, `:85-95`, are the comment recording exactly this). Rationale, so nobody
  later "fixes" it by adding a gate: CRASHED / TERMINATED / TIMEOUT are all
  derived from a child's exit status, so gating isolation behind the flag would
  make ordinary (non-unstable) runs strictly LESS able to report the truth — a
  segfaulting spec would take the whole runner down — in exchange for an
  unmeasured speed gain via an in-process path that does not exist. The genuine
  gap is the BUILD half, which the old "isolation is what the mode buys you"
  framing concealed.
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
| R1 per-spec isolation | **SATISFIED — unconditional, predates this work, and must STAY ungated** | `process_run_bounded` / `process_run_with_limits_bounded` at `test_runner_execute.spl:186,288,807` (re-read 2026-08-18, Lane REDEFINE: the limits variant is chosen when `max_mem_gb`/`max_procs` are set, the plain variant otherwise — both spawn a child, so no branch reaches an in-process path) and `test_runner_single.spl:193`. `unstable_mode` is read **nowhere** in `test_runner_execute.spl` — its only hits there are the `:85-95` comment stating this. Do not add a gate: isolation is a precondition of the outcome contract, not a mode feature. |
| R2 non-collapsing categories | **SATISFIED** | Set at `test_executor_parsing.spl:442,446,448,449`, `test_runner_fork.spl:80,86,87,92`, `test_runner_execute.spl:71-75`. Counted and printed separately at `test_runner_output.spl:192-216` (`crashed` / `terminated (unverified)` / `timed out (unverified)` / `not run`). |
| R2a `137` (SIGKILL) ⇒ CRASHED | **SATISFIED** (corrected 2026-08-18, Lane AUDITFIX — the earlier NOT SATISFIED row was a misreading) | `is_outside_kill` in `src/lib/nogc_sync_mut/test_runner/test_runner_fork.spl` returns `signo == 1 or signo == 2 or signo == 15`. **SIGKILL(9) is deliberately NOT in the set**, so 137 falls through to the CRASHED branch, exactly as this doc froze. The previous row cited "line 72 … `1 or 2 or 9 or 15`"; line 72 is **inside the docstring**, where the `9` appears in the prose sentence explaining why SIGKILL is excluded — comment text was read as implementation. The docstring further records that budgeted kills are already classified as TIMEOUT by the earlier `rt_fork_parent_timed_out()` branch in `classify_fork_exit`, so any SIGKILL reaching the predicate is unbudgeted, and states the known earlyoom-escalation tension explicitly, choosing to over-report a crash because under-reporting one is the silent-green defect. No code change is warranted here. |
| R2b `137` in the subprocess lane | **PARTIAL — different mechanism, plus one real gap** (rewritten 2026-08-18, Lane AUDITFIX) | The subprocess lane classifies by *evidence*, not by signal number: `make_result_from_output` (`test_executor_parsing.spl`) branches on `-1 / 143 / 144`, then tries `take_crash_sentinel(file_path)` ⇒ CRASHED, then `has_crash_evidence(stdout+stderr)` (fault-runtime-error / SIGSEGV / SIGABRT / `panicked at` / stack-overflow / double-free markers) ⇒ CRASHED, falling back to TERMINATED/unverified only when neither exists. That is not a disagreement with the fork lane — it is the best available classification for a lane with less information, and it fails to the unverified side rather than to green. **The real gap:** `exit_status_to_code` (`src/compiler_rust/runtime/src/value/sffi/env_process.rs:22-34`) now returns `128 + signal` — the `-1` collapse was *fixed* — so a signalled child on this path arrives as **137/139/134**, and those values match none of the `-1/143/144` arms and fall through to the legacy stdout-scrape path. `-1` now means only *timeout* (`:539,563-567`, `timed_out=true`, `\nTIMEOUT\n` appended at `:1275`) or a spawn/reap failure. The in-source comment above `make_result_from_output` still described the old always-`-1` behaviour and was **stale**. **Update 2026-08-18 (Lane REDEFINE, read not assumed):** the fix now appears in the WORKING TREE — `test_executor_parsing.spl:456-476` computes `signo = exit_code - 128` for `128 < exit_code < 192`, routes SIGILL/ABRT/BUS/FPE/KILL/SEGV (4/6/7/8/9/11 ⇒ 132/134/135/136/137/139) to CRASHED, and adds `signo > 0` to the unverified arm alongside `-1/143/144`, matching the fork lane. `git status` shows the file as ` M` (uncommitted, owned by a live lane), so this is **verified as present in the tree, NOT verified as landed on `main` and not executed** — re-check after that lane commits before marking SATISFIED. |
| R3 verdict mandatory | **SATISFIED** | Classification `test_runner_types.spl:202-221` → `Unverified` (`:215-216`) via `test_file_result_is_unverified` (`:226-236`); exit map `:237-245` (`Unverified` ⇒ 5, timeout ⇒ 124). Applied `test_runner_main.spl:1109,1141-1152`, returned `:1199`. Guard spec: `test/01_unit/.../test_runner/no_verdict_is_unverified_spec.spl`. The single-spec lane's divergent `2` is **resolved to 5** — see § *Unverified exit code* below. |
| R4 rc read directly | **SATISFIED (as a rule), NOT enforced by code** | The rule holds and `shell()`'s signal collapse — the mechanism that made it unenforceable — is **FIXED** (`doc/08_tracking/bug/shell_collapses_every_signal_death_to_minus_one_2026-08-17.md`). But no check prevents a future pipe; this is convention, not a gate. |
| R5 no parallelism | **SATISFIED (unchanged)** | Nothing in the unstable-mode work introduced concurrency; the sequential constraint is untouched. |
| R6 attribution: path, outcome, exit code | **SATISFIED** | Per-`TestFileResult` path/outcome/code; verdict lines at `test_runner_main.spl:986`. |
| R6 attribution: wall time | **SATISFIED** | `duration_ms` on every `TestFileResult`; totals `test_runner_output.spl:220-223`. |
| R6 attribution: **peak RSS** | **NOT SATISFIED** | No `rss` / `peak_rss` / `max_rss` anywhere in the test-runner sources. The field exists only on the **build** side (`build_outcome.spl:214`) and is filed as always-0: `doc/08_tracking/bug/supervised_builder_unwired_and_no_peak_rss_2026-08-17.md`. R6's stated purpose — telling host contention from a real defect — is therefore only half-served. |
| Contract: `TestOptions.unstable_mode` | **SATISFIED** | `test_runner_types.spl:94`, with `unstable_mode_set: bool` at `:95`. |
| Contract: `--unstable` / `--no-unstable` | **SATISFIED** | `test_runner_args.spl:327-332`; passthrough allowlist `:156`; struct init `:629-630`. |
| Contract: default ON for bootstrap, OFF interactive | **SATISFIED** | `test_runner_main.spl:192` reads `SIMPLE_BOOTSTRAP == "1"`; resolution `:194-200` (explicit flag wins either direction); announced `:203`. |
| Contract: error-text prefixes | **PARTIAL** | `CRASHED:` / `TERMINATED:` / `TIMEOUT:` are produced by the classifier and consumed at `test_runner_output.spl:196-204`. `NOT EXECUTED:` is set at `test_runner_main.spl:949`. Verified as *emitted and counted*; **not** verified end-to-end on a real crashing child by this lane. |
| **Unstable mode changes behaviour** | **SATISFIED against the REDEFINED scope** (redefined 2026-08-18, Lane REDEFINE; was "NOT SATISFIED — headline gap") | Exhaustive grep of `unstable_mode` over all of `src/**` (`.spl`+`.rs`), re-run by this lane: the only behavioural effect anywhere is `fail_fast = false` at `test_runner_main.spl:205-207`. Every other hit is a field decl (`test_runner_types.spl:94,95`), arg parsing (`test_runner_args.spl:156,225-226,328-332,629-630`), the effective-value resolution (`test_runner_main.spl:194-200`), a printed banner (`:201,204`), a Rust help unit test (`help.rs:351`), a comment (`test_runner_execute.spl:85-95`), or the UNRELATED same-named `ParallelBuildConfig.unstable_mode()` (`driver_build/parallel.spl:121`) whose consumer `build_supervised()` has zero callers. Under the redefined scope — classification + run-to-end + bootstrap default — that is the whole intended surface, not a gap. Isolation is deliberately not gated (see § *Unstable mode — the frozen contract*). |
| BUILD-side per-unit isolation | **BLOCKED (genuine, and now honest)** | `parallel.spl:402-406` prints that unstable mode is REQUESTED but NOT ACTIVE, with the reason: `build()` is in-process because MIR capsules cannot cross a process boundary. `build_supervised()` is implemented and unit-verified but has **zero callers in `src/`** — `doc/08_tracking/bug/supervised_builder_unwired_and_no_peak_rss_2026-08-17.md` Gap 1. Blocked on a capsule-crossing design, not on effort. |
| Acceptance: five-fixture run | **UNDER TEST BY LANE ACCEPT** | Fixtures exist: `test/fixtures/unstable_mode/{crash,timeout,fail,pass_a,pass_b}_spec.spl` (commit `af0f05f08c5c`). The one-run acceptance execution is owned by another lane; this lane did **not** run it and asserts nothing about its outcome. |
| Acceptance: negative control | **NOT SATISFIED** | No reverted-change control run has been performed or recorded anywhere. |
| Defect 1 (silent green) closed? | **OPEN** | `doc/08_tracking/bug/test_runner_emits_no_result_summary_silent_exit0_2026-08-17.md` remains OPEN. R3's machinery is the intended fix, but the originating defect has not been re-measured as closed. |

### Honest overall verdict

The **classification and verdict-accounting half of this request is real and
landed** (R2, R3, R6-minus-RSS), and with the mode redefined as *classification +
run-to-end + bootstrap default* the test side is delivered as specified. The
**isolation half is not something this work delivers**: on the test side it
already existed, unconditionally and correctly, and is deliberately not gated on
the flag; on the **build side it is BLOCKED, and that is the real outstanding
gap** — `build_supervised()` is written but has zero callers, and `build()`
stays in-process because MIR capsules cannot cross a process boundary. Still
genuinely outstanding besides that: **peak RSS (NOT SATISFIED)**, the
**negative control (NOT SATISFIED)**, defect 1 (**OPEN**), and the five-fixture
acceptance run, which another lane is executing and whose outcome this doc
asserts in neither direction.

**Corrections applied 2026-08-18 (Lane AUDITFIX).** Two of the three "wrong in
detail" items in the first pass of this table were themselves wrong:

1. **R2a was a misreading of a docstring.** `is_outside_kill` excludes SIGKILL
   on purpose; 137 *is* CRASHED. The contract and the code agree. Nothing to
   reconcile. (Rule for future audits of this file: `test_runner_fork.spl`
   carries long `"""…"""` docstrings that enumerate signal numbers in prose —
   confirm a line is code before asserting what it does.)
2. **R2b was a mischaracterisation.** The two lanes use two mechanisms because
   they have two different amounts of information, not because they disagree.

The third item, **two different unverified exit codes**, is now DECIDED (5) —
see below.

### Unverified exit code: DECIDED — standardise on 5

- `test_run_outcome_exit_code` (`test_runner_types.spl`) maps
  `Unverified ⇒ 5`, `UsageError ⇒ 2`, `InternalError ⇒ 3`,
  `EmptySelection ⇒ 4`, `TimeoutResourceFailure ⇒ 124`. This is the suite lane.
- `test_runner_single.spl` returns a bare `2` for a verdict-less single-spec
  run, with a comment asking only for "a distinct exit code".

**Recommendation: 5.** Not a coin flip — **2 is already taken by `UsageError`
in the very same runner's own enum**, so today `bin/simple test <spec>` exiting
2 is ambiguous between "you passed a bad flag" and "the host killed your spec",
which is precisely the confusion this classification exists to remove. 5 has no
other meaning anywhere in the runner. A survey of `scripts/**` found **no**
script branching on either value for unverifiedness (callers currently test
only `rc == 0`), so the change breaks no known consumer and the migration cost
is one literal.

**DECIDED 2026-08-18: 5.** The reasoning is not a preference — `2` is already
taken by `UsageError` in `test_run_outcome_exit_code`
(`src/lib/nogc_sync_mut/test_runner/test_runner_types.spl:242`, `Unverified ⇒ 5`
at `:246`), so a bare `2` makes "you passed a bad flag" and "the host killed
your spec" the same code in the same runner.

**Code change is another lane's, and is NOT claimed done.** Location (corrected
2026-08-18 — the earlier `:1226-1231` citation was off by a few lines):
`src/app/test_runner_new/test_runner_single.spl:1226-1238`. Lane REDEFINE read
that file and found it now `return 5` at `:1238` with a comment giving exactly
this reasoning — but `git status` reports the file as ` M` (uncommitted, live
lane). So: **present in the working tree, NOT verified as committed or landed on
`main`, and not executed.** Verify with `git log -1 --oneline -- <path>` plus a
re-read before treating it as delivered.

### Other flagged items, re-verified by Lane AUDITFIX

- **Peak RSS NOT SATISFIED — confirmed.** `grep -l 'peak_rss|max_rss|\brss\b'`
  over `src/lib/*/test_runner/` and `src/app/test_runner_new/` returns nothing.
  The row stands as written.
- **R1 "unconditional, not gated on unstable mode" — wording is defensible.**
  `unstable_mode` appears 3× in `test_runner_execute.spl` and **0×** in
  `test_runner_single.spl`, while `process_run_bounded` is called on both paths
  regardless. A second lane is checking this independently; no code was touched
  for it here.

## Related

- `doc/02_requirements/compiler/supervised_builder.md` — the build-side twin.
- `.claude/rules/testing.md` § "Silent green: exit 0 is not a pass".
- `doc/08_tracking/bug/run_vs_test_harness_divergence_2026-07-28.md` — `test` is
  the tree-walk interpreter, `run` is the Cranelift JIT; 711 of 23,958 spec files
  call a divergent method and would stay green through any JIT regression. A
  supervised runner does not fix this, but R6's attribution makes it visible.
