# Lane: unstable_test_mode

**Goal.** Unstable mode = per-unit SEPARATE PROCESS for build and for test,
run to the END of the source list and the END of the test list, with
CLASSIFIED outcomes. Default ON for the bootstrap path only; explicit flag
either way.

## Research / D1 findings (established by reading code, 2026-08-17)

`run_all` is NOT a keep-going flag. It is file SELECTION.

- Set by `--all` / `--whole` (`test_runner_args.spl:299,301`), and by `--ci`
  (`:383`). Consumers: `test_runner_files.spl:328,468` (`only_slow and not
  run_all`) and `:407` (`needs_content`). Nothing else reads it.
- The keep-going control is `fail_fast`, default **false**
  (`test_runner_args.spl:184`). Only break in the file loop is
  `test_runner_main.spl:448`, guarded by `fail_fast`.

Answers to the three D1 questions:

| question | answer | evidence |
|---|---|---|
| (a) continues past a FAILING spec | YES | `fail_fast=false` default; sole break at `test_runner_main.spl:448` |
| (b) continues past a CRASHING spec | YES | each spec already a subprocess: `test_runner_execute.spl:172` `process_run_bounded(binary, child_args, timeout_ms, …)` |
| (c) ON by default on bootstrap | YES | nothing sets `fail_fast=true` on that path |

So "run to the end of the TEST list" was already true for the interpreter lane.
The gaps are elsewhere — see below.

## Gaps (what this lane actually builds)

1. **No explicit flag.** Keep-going is an emergent property of a default, not a
   mode a human can force on or off. -> `--unstable` / `--no-unstable`.
2. **Outcome classes collapse.** `exit_code == -1` is the runtime's single
   sentinel for BOTH timeout and death-by-signal, so SIGSEGV, SIGABRT and an
   **earlyoom SIGTERM (143)** land in one bucket. Required classes:
   `OK / ERROR / CRASHED / TERMINATED / TIMEOUT / NOT_RUN`, where **TERMINATED
   and TIMEOUT are UNVERIFIED and never failures**.
3. **Build side is unaddressed.** Run-to-end applies to the SOURCE list too;
   only the test list is covered today.
4. **No crash fixture.** Nothing proves any of it.

## Decisions

- Session daemon is NOT the problem and stays. Daemon-served execution remains
  valid for ordinary interactive use.
- Unstable mode default: **ON for bootstrap, OFF for interactive.** Explicit
  flag overrides in both directions.
- earlyoom disambiguation: fixture writes a sentinel file immediately before
  self-crashing. Sentinel present + died by signal = CRASHED; sentinel absent =
  TERMINATED/UNVERIFIED. No runtime change, no `bin/simple` rebuild.

## Field/flag contract (frozen — lanes depend on these exact names)

- `TestOptions.unstable_mode: bool` (`test_runner_types.spl`)
- `--unstable` sets true; `--no-unstable` sets false; unset = path default
- outcome text prefixes on `TestFileResult.error`: `CRASHED:` / `TERMINATED:` /
  `TIMEOUT:` / `NOT EXECUTED:`

## Runtime facts that corrupt evidence here

- earlyoom is SIGTERMing `simple` (fires at 10% mem, host has zero swap).
  rc=143/144 is UNVERIFIED, never failed.
- Silent green is an OPEN defect: `bin/simple test <spec>` has printed ~1897
  warning lines with ZERO result lines and exited 0
  (`doc/08_tracking/bug/test_runner_emits_no_result_summary_silent_exit0_2026-08-17.md`).
  Never accept exit 0 as a pass; require an explicit `Results:` line.
- `bin/simple` is a stale seed. Do NOT rebuild or redeploy it.
- Do NOT parallelise test runs — parallel `simple test <dir>` corrupts the
  shared test database.

## Lane partition (no two lanes touch the same file)

| lane | owns | status |
|---|---|---|
| A | `test_runner_args.spl`, `test_runner_types.spl` | DONE `a3738dd8d0c` |
| B | `test_executor_parsing.spl`, `test_runner_output.spl` | DONE `882fb6e31ea` |
| C | `test/fixtures/unstable_mode/**` (new files only) | pending |
| D | `test_runner_main.spl` | pending |
| E | requirement doc + LLM wiki | DONE `32a5d018082` |

## Log

- 2026-08-17 — D1 established by code reading; `run_all` misattribution
  corrected. Lane A/B WIP in `test_executor_parsing.spl` +
  `test_runner_output.spl` is uncommitted and at risk.
- 2026-08-17 — Lane A landed `a3738dd8d0c`: `unstable_mode` +
  `unstable_mode_set` on `TestOptions`, `--unstable` / `--no-unstable` parsed.
  Two useful side findings:
  - **Partial struct literals are legal here** — `execution_strategy.spl:245`
    builds `TestOptions` with ~30 of 81 fields. Adding a field does NOT break
    other construction sites, so field additions are safe across lanes.
  - `test_runner_args.spl` contains **no help/usage text at all**. The
    user-visible flag help lives in some other file and is still UNDOCUMENTED
    for `--unstable`. Open follow-up.
- 2026-08-17 — Lane E landed `32a5d018082`: requirement doc + both wiki
  entries. Feature slug chosen was `mission_critical_robustness` (no
  test-runner feature_expert slug exists; `modern_sspec` is scoped to spec
  AUTHORING, not runner execution — no new slug created). Side finding worth
  keeping: the layer_expert/test_runner doc's "Owned source" points at
  `src/app/test_runner_new/`, but the files this lane actually changes live
  under `src/lib/nogc_sync_mut/test_runner/`. That mismatch is a real trap for
  the next agent and is now noted in the layer doc.
- 2026-08-17 — **The Lane A/B WIP recorded above was DESTROYED, not landed.**
  It was read directly from the working copy earlier this session (CRASHED
  classification at `test_executor_parsing.spl:397-401`, the `ponytail:`
  summary derivation at `test_runner_output.spl:150-167`, both showing ` M` in
  `git status`). By the time Lane B started, both files were CLEAN — empty
  `git diff`, empty `git status --porcelain`, and `git log -S "CRASHED:" --all`
  finds nothing on those paths. Lost to the tree wipe repaired by
  `ae55a7467197 fix(vcs): restore tree wiped by 6f86ff32a7d`.
  **Lesson: uncommitted work in this shared tree does not survive. Commit on
  write.**
- 2026-08-17 — Lane B landed `882fb6e31ea` (rewritten from scratch). Verified
  by CONTENT, not commit success: the three prefixes are present in
  `test_executor_parsing.spl`, INCONCLUSIVE verdict at
  `test_runner_output.spl:199`.
  - **rc 143 never reaches Simple as a plain exit code from a directly
    signalled child.** `finish_child_output_bounded` (`env_process.rs:508`)
    does `status.code().unwrap_or(-1)`; the timeout branch (`:535`) returns a
    hard-coded `-1` too — so signal-death and timeout are genuinely
    indistinguishable at that boundary. 143 CAN arrive as a plain code via the
    shell guard wrapper's `die(){ exit 143; }` (`:806`). Both forms handled;
    the sentinel file covers the rest.
  - Unverified classes carry `failed: 0` (kept out of the failed count) but a
    non-empty `error` (so `is_ok()` stays false) — they cannot collapse into
    exit 0.
  - Sentinel path `<spec_path>.crashed`, deleted on read so a stale sentinel
    cannot mislabel a later run.
  - **`total_timed_out` aggregation in `test_runner_modes.spl:261-374` is
    COMMENTED OUT**, so those totals are unreliable — an independent reason the
    error-prefix derivation is right here rather than merely lazy.
