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
| D | `test_runner_main.spl` | DONE `e37cc015713` |
| E | requirement doc + LLM wiki | DONE `32a5d018082` |
| F | `test_runner_execute.spl` | DONE `530fa623afa` — UNVERIFIED post-change run |

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
- 2026-08-17 — Lane D landed `e37cc015713`. A/D integration VERIFIED by
  content: `unstable_mode` + `unstable_mode_set` exist in
  `test_runner_types.spl:88-89` and are consumed at
  `test_runner_main.spl:194-198`. (Lane D reported the fields as missing; that
  was a stale read taken before Lane A committed. No action needed.)
  - **Bootstrap detection = `env_get("SIMPLE_BOOTSTRAP") == "1"`** — an
    EXISTING signal, not invented. Exported by
    `scripts/bootstrap/bootstrap-from-scratch.sh:1569` (+ ~10 per-invocation
    sites), `resume-stage3-from-admitted.sh`, and two
    `scripts/check/lib/bootstrap-stage3/*.shs`; already consumed inside the
    compiler at `module_lowering.spl:362,941,1536,1890,1966,2489`,
    `declaration_lowering.spl:206,274`, and `spec/env_detect.spl:120`.
    `ci_mode` was REJECTED as the signal: `--ci` is a user flag that also
    fires on non-bootstrap CI runs, so it would turn unstable mode on for
    ordinary interactive CI — exactly what the user ruled out.
  - Mode line: `Unstable mode: {ON|OFF} ({--unstable|--no-unstable|bootstrap
    default|interactive default})`. When ON, `fail_fast = false` is set
    EXPLICITLY rather than left as an emergent default.
  - Per-spec process isolation audit — interpreter, smf, native, compile and
    safe all spawn a real process per spec (`process_run_*` /
    `process_run_with_limits_bounded`). **`fork` mode is the one real gap:**
    `test_runner_fork.spl:43` `rt_fork_child_setup()` gives a child per spec
    (so a crash IS contained) but it is COW-forked from the parent's
    already-loaded interpreter image, so accumulated in-process state is
    INHERITED, not reset. That is not a fresh-process-per-unit guarantee.
    OPEN — `test_runner_fork.spl` was outside every lane's ownership.
- 2026-08-17 — Lane C proved D4 by ABLATION (post-change vs `882fb6e31ea~1`
  swapped into an isolated worktree `/mnt/data/wt-ablate`):
  - post-change: `Results: 5 total, 2 passed, 3 failed, 1 timed out, 1 crashed`
    with `Error: CRASHED: child died by signal after writing its crash sentinel`
  - ablated: both `, 1 crashed` and the `CRASHED:` line VANISH; the crash
    degrades to `Error: Process exited with code -1`
  - restored and re-verified by grep. Causation established.
  Corrected attribution: Lane C reported B's `(unverified)`/`INCONCLUSIVE` code
  as absent from the tree. It is NOT — 7 matches in both WT and HEAD. The
  observation was right, the diagnosis wrong.
- 2026-08-17 — Lane F landed `530fa623afa`. The real cause of TIMEOUT counting
  as a failure: the three `if result.limit_exceeded:` early returns in
  `test_runner_execute.spl` hardcode `failed: 1` and return BEFORE
  `make_result_from_output`, so B's classification was unreachable on that path.
  `limit_type` values are `memory|procs|cpu|fds|timeout`. Now
  timeout/memory/cpu -> `failed: 0` + `TIMEOUT:`/`TERMINATED:` prefix
  (outside-kills, unverified); fds/procs stay `failed: 1` (the test itself
  exhausted them). Error string always non-empty so `is_ok()` stays false.
  **NOT YET RE-MEASURED — no post-change run, no ablation.** Lane F died to a
  session limit before its BEFORE measurement; the edit is mine, unverified.
- OPEN, carried forward:
  - **The single-spec path bypasses classification entirely.**
    `bin/simple test <one_file.spl>` and any `--no-session-daemon` run route to
    `test_runner_single.spl`, which never calls `make_result_from_output`. That
    is the path humans use interactively, so none of this lane's classification
    applies there. Largest remaining gap.
  - `--no-session-daemon` cannot run a directory (`expected .spl test file`),
    so the acceptance run is only reachable THROUGH the daemon.
  - `fork` mode COW-inherits the parent interpreter image — crash contained but
    not fresh-process-per-unit.
  - `--unstable` still has no user-visible help text.
  - BUILD-side run-to-end (the source list) is still entirely unaddressed.
  - `/mnt/data/wt-ablate` needs `git worktree remove`.
  - `rc` is unusable for this suite: correct summary at ~63s, then ~55min hang
    in post-run work. The `Results:` line is the only authoritative verdict.
- 2026-08-17 — Lane C closed out. Ablation worktree `/mnt/data/wt-ablate`
  REMOVED and confirmed gone (`ls` ENOENT, 0 rows in `git worktree list`);
  main tree's copy of `test_executor_parsing.spl` verified untouched.
  Housekeeping item closed.
  - Fixture discovery requires BOTH markers: `--only-skipped` selects on the
    literal `tag: "skip"`, NOT on `# @skip`. With `# @skip` alone the run
    reports `Results: 0 total`, exit 4 — a vacuous run that reads like a clean
    one. Both markers are now in each fixture header.
  - Lane C's finding 3 ("`(unverified)`/`INCONCLUSIVE` absent from the tree")
    is REFUTED — 7 matches in both WT and HEAD. Its underlying observation
    (TIMEOUT counted as a failure) was correct and is what Lane F's
    `530fa623afa` addresses; that fix is still UNMEASURED.

## 2026-08-17 — build-side lane (bdeaf726232)

**Correction to this file's own Gap 3.** "Build side is unaddressed" was WRONG.
Most of it exists and is wired to nothing:
- The build ALREADY runs to the end of the source list. `parallel.spl:455-462`
  records failures into `errors` and falls through — no `break`, no `return`;
  a failed dependency is a `continue` (`:414-421`); the only `break` is
  work-exhaustion (`:472`). Caller iterates all errors
  (`driver_aot_native_output.spl:690-693`). Full census today.
- **No process isolation:** `parallel.spl:424` calls `compile_fn(...)`
  IN-PROCESS. One SIGSEGV/OOM kills the whole build.
- **`build_supervised()` already exists** at `parallel.spl:680` with a verified
  signal-preserving wrapper (`:72-73`, SEGV->139 / TERM->143 / KILL->137) and
  has **ZERO callers**.
- **The six outcome classes already exist build-side**: `BuildOutcomeKind` /
  `BuildUnitOutcome` / `BuildOutcomeSet` in `driver_build/build_outcome.spl`
  (`e89f0c6f94a`), TERMINATED already never-a-failure (`:75-79`, `:106-108`).
  Do NOT invent a second vocabulary.
- earlyoom mid-build: the build simply dies UNCLASSIFIED — the classifier is
  only reachable from the unwired path.
- CLAUDE.md's claims re-verified TRUE: `needs_recompile` and
  `interface_digest_of` (`cache/action_key.spl:199`) both have zero call sites.

**Real blocker, not papered over:** `build()` closes over in-memory frozen MIR
capsules (`driver_types.spl:908`); a child process cannot receive one. Process
isolation needs capsule serialization + a one-module CLI, or it is genuinely
blocked. Unknown whether capsules serialize cheaply.

Suspected P0 raised by that lane, LIKELY A FALSE ALARM: `ParallelBuildConfig`
built with 4 fields at `driver_aot_native_output.spl:667-672` while the struct
has 6. Lane A established partial struct literals ARE legal here
(`execution_strategy.spl` builds `TestOptions` with ~30 of 81 fields). Confirm
before acting.

## 2026-08-17 — help-text lane (df0b2ca8747, c7584b189f1)

`--unstable` help text added, but **the rendered proof is OWED and BLOCKED.**
- The LIVE renderer is `src/compiler_rust/driver/src/cli/help.rs` — **compiled
  into the Rust seed**. No `src/lib` or `src/app` edit can ever change
  user-visible CLI help without a seed rebuild, which is forbidden here.
- The help text is TRIPLICATED: `help.rs` (live),
  `src/compiler_rust/lib/std/src/tooling/help.spl` (orphan, zero importers),
  `src/app/cli/cli_helpers.spl` (stale). Two of three are dead.
- Established by ABLATION, not grep: editing `cli_helpers.spl` alone changed
  nothing in real output.
- **`bin/simple test --help` does not exist** (`Error: unknown option: --help`).
  The working form is `bin/simple help test`.
- TO CLOSE: after the next redeploy run `bin/simple help test | grep unstable`.

## 2026-08-17 — BLOCKER: shared tree is unparseable (another lane, uncommitted)

`src/lib/nogc_sync_mut/test_runner/test_runner_types.spl` line 64 carries
`paths: [text] = []` — a struct FIELD DEFAULT INITIALIZER, which the grammar
does not accept:

    compile failed: parse: in test_runner_types.spl:
    Unexpected token: expected name, found Eq

It is part of **28 uncommitted insertions from a concurrent lane**. Effect: every
`bin/simple test` run in this working tree fails at parse, so NO lane can take a
measurement right now. Two verification lanes were blocked by it.

NOT FIXED HERE — it is another lane's in-flight edit and clobbering it would
destroy their work. The owning lane must either commit a parseable version or
back it out. If it is still broken and unclaimed later, the minimal repair is to
drop the ` = []` and give the field an explicit value at each construction site.

## 2026-08-17 — fork lane (cafcc59ccef): a real classification hole, now closed

Fork mode was ALREADY calling `make_result_from_output` (`test_runner_fork.spl:85`)
— it never bypassed it like the single-spec path. The defect was downstream:

**`make_result_from_output` only tests `-1 || 143 || 144`
(`test_executor_parsing.spl:441,444`).** Fork mode delivers real signal numbers
via `waitpid` (`runtime_fork.c:463-465` returns `128 + WTERMSIG`), so SIGSEGV
arrives as **139**, SIGABRT as **134**, SIGKILL as **137** — none of which were
tested. All fell through unclassified. **A segfault in fork mode was NOT reported
as CRASHED.**

**Fork mode is the ONLY path with the real signal number.** The subprocess path
collapses signal-death and timeout into `-1` (`env_process.rs:508,535`), which is
why the sentinel-file heuristic exists at all. Two predicates were already
exported and unused: `rt_fork_parent_signaled()` (`runtime_fork.c:527`) and
`rt_fork_parent_timed_out()` (`:523`). This genuinely resolves the
SIGSEGV-vs-earlyoom ambiguity that no other mode can.

Reachable from the CLI: `--fork` / `--fork-mode` (`test_runner_args.spl:450`),
`--no-fork` (`:452`), default false (`:253`). The gap was real, not theoretical.

Chose (b) — classify from the signal number — over (a) refuse-to-combine, because
refusing the one mode that is BEST at what unstable mode needs would be wrong.
Fault signals -> CRASHED/failed:1; outside kills (TERM/INT/KILL/HUP) ->
TERMINATED/failed:0; timeout predicate -> TIMEOUT/failed:0. COW-inheritance
limitation documented in the header per (c).

AFTER-measurement UNVERIFIED — blocked by the parse breakage above, not by
anything in the fork lane's own file.
