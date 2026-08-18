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

## 2026-08-17 — D4 PROVEN. Timeout fix verified by ablation.

| arm | verbatim `Results:` |
|---|---|
| pre-fix | `5 total, 2 passed, 3 failed, 1 timed out, 1 crashed` |
| post-fix | `4 total, 2 passed, 2 failed, 1 crashed, 1 timed out (unverified)` |
| ablated (`530fa623afa~1`) | `5 total, 2 passed, 3 failed, 1 crashed, 1 timed out (unverified)` |

2+2=4 post-fix — the timeout contributes to neither bucket. Ablated returns
byte-identical counts to pre-fix. The `TIMEOUT:` prefix VANISHES when ablated,
so the classification path is what was restored, not merely a counter.
`CRASHED:` and the real assertion failure are unchanged in both arms — the
ablation is correctly scoped to the limit-exceeded path.

Method note worth keeping: the ablation worktree got a BYTE-IDENTICAL COPY of
the binary, not a symlink — a symlink resolves back into the main tree's
`src/lib` and would have silently defeated the ablation.

**Startup cost was ~10x the recorded figure today:** `discover` 269s +
`Session setup` ~286s ~= 550s before the test loop even starts. A run at
`timeout 400` died after one spec with ZERO `Results:` lines — an INCONCLUSIVE
that reads as a failure if rc is trusted. **Budget >= 1200s for this suite.**

### OPEN — second accounting path still contradicts the summary
`SPEC FILE VERDICT: ... timeout_spec.spl ... passed=0 failed=1 ... timeout=1
reason=aggregate-lane-timeout` — `failed=1` there while the summary says
`failed: 0`, same run. Any consumer parsing `SPEC FILE VERDICT` still sees a
timeout as a failure. Emitter is OUTSIDE `test_runner_execute.spl`. Needs a
follow-up lane.

### OPEN — push still blocked, cause now identified
`check-native-trailing-default-param.shs` blocks the pre-push hook. Two distinct
causes were conflated:
1. A fresh `git worktree` has NO `bin/simple` (gitignored symlink), so the guard
   failed closed with ZERO output. Fixed by symlinking the existing binary — no
   rebuild. **A fail-closed gate that prints nothing is itself a defect**: it
   should report `ERROR — nothing was checked` per repo convention.
2. With a binary present the guard reports a REAL failure on committed content:
   `parse: in src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl:
   Unexpected token: ...` (guard truncates its own stderr; a direct
   `simple check` on the 4483-line file hit rc=124 before printing). No trailing
   `|` and no field-default in that file, so it is a THIRD pattern — not the
   `verification_semantic_coverage.spl` cause named in the fence notice, which
   is fixed and at origin (`010c878e208`).

## 2026-08-17 — single-spec path FIXED and proven (d03b800c7d6)

The largest gap is closed. `test_runner_single.spl` now calls the SHARED
classifier — `use std.test_runner.test_executor_parsing.{make_result_from_output}`
(line 37). No import cycle; zero classification logic duplicated (a second copy
would have drifted, as the duplicated composite-grammar parsers already did).
The old `code == -1 and stderr.contains("TIMEOUT")` branch became
`if code == 143 or code == 144 or code == -1:` handing off to the shared path.

Ablation bites exactly on the axis under test:
- with the change:  `reason=child-died-by-signal` + `error: test-runner: CRASHED: child died by signal after writing its crash sentinel`
- ablated:          `reason=zero-examples` + `error: test-runner: no examples executed`

A crash that read as "ran nothing" now reads as CRASHED.

**Exit-code design worth keeping:** TERMINATED/TIMEOUT return `failed: 0`, which
would have fallen into the existing `failed == 0 -> return 0` and produced a
SILENT GREEN on a killed spec. That lane added `unverified_error` returning
**exit 2** — not a failure, never a green. `print_summary`'s `Results:` line is
untouched and still emitted on every path.

**Blast radius confirmed:** every `bin/simple test <one_file.spl>` and every
`--no-session-daemon` run — the interactive path AND the path agents use to
verify their own fixes — previously had NO abnormal-termination classification
at all.

**Confounded-run discipline worth copying:** that lane's FIRST ablation attempt
died on the concurrent `test_runner_types.spl` parse breakage with no `Results:`
line, and it DISCARDED the attempt rather than concluding from it. The clean
retry is what is reported above.

## 2026-08-17 — `SPEC FILE VERDICT` contradiction is BLOCKED, not merely open

Emitter located: **`src/compiler_rust/driver/src/cli/basic.rs:169`** (doc
comment at `:126`). It is in the **Rust seed**, compiled into `bin/simple`.

Consequence: the `failed=1` it prints for a timed-out spec — contradicting the
summary's `failed: 0` from the same run — **cannot be fixed by any `.spl` edit**.
It needs a seed rebuild, which is forbidden here (clobbers ~15 concurrent lanes).
This is the SAME structural problem as the CLI help text
(`driver/src/cli/help.rs`): user-visible test-runner output lives in the seed,
so pure-Simple work cannot reach it.

Both are blocked on the same event — the next seed rebuild/redeploy. To close
them together, after that redeploy:
  - `bin/simple help test | grep unstable`   (help text)
  - re-run the five fixtures and check the `SPEC FILE VERDICT` line for the
    timeout spec reports the timeout as unverified, not `failed=1`

Until then a consumer parsing `SPEC FILE VERDICT` still sees a timeout as a
failure, and this lane's contract holds only for the `Results:` summary line.

## 2026-08-17 — ROOT CAUSE of the repo-wide push block (do NOT "fix" by reverting)

**Every push is blocked**, and the cause is now pinned:

- `origin/main`'s `src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl`
  **does not parse**: `Unexpected token: expected Fn, found Assign` — an
  assignment sitting where the `impl MirLowering:` block expects a method.
- The **main tree's committed copy PARSES** (`bin/simple run <file>` rc=0). It
  differs from origin by **-88/+19**: it lacks the 88-line addition that arrived
  with `251a75f5355 chore(sync): merge origin/main` (the B5b Phase 2
  scalar-literal dispatch / flat-if-chain work).
- So the defect is INSIDE that 88-line addition as it exists at origin.

**Why it blocks everything:** `check-native-trailing-default-param.shs` runs a
real `native-build`, which reads `src/` as SOURCE from the tree it runs in. The
broken file makes the guard's own **--selftest** fail, so the guard exits before
any scan and the pre-push hook blocks the push. Chain:
broken source -> selftest fails -> guard errors -> hook blocks -> no lane can push.

**Diagnosis trap that cost time here — do not repeat:**
- Truncating the file (`head -N`) to bisect is INVALID: cutting mid-block
  manufactures its own parse error, so every prefix "BREAKS" and the bisect is
  meaningless.
- `bin/simple check <file>` pulls the whole module graph and exceeds 100s.
  **`bin/simple run <file>` parses in seconds** — a clean module reports
  ``no `main` function``, a broken one reports the parse error. That is the cheap
  parse oracle.
- The parse error carries **NO line/column**, which is a real diagnostic-quality
  defect of its own.
- The guard emits ZERO output when its selftest fails this way, despite having a
  correct `no-compiler -> ERROR/exit 2` path (verified working from the main
  tree: rc=2, 3 lines). Guard is fine; the SOURCE is broken.

**NOT FIXED HERE, deliberately.** The 88 lines are another lane's feature work.
Reverting them at origin to unblock a push would destroy it — exactly the
clobber pattern this repo keeps suffering. The main tree's parsing copy is NOT a
fix: it simply predates the addition.

### CORRECTION 2026-08-17 (later) — the 88 lines are VALID; the BINARY is stale

The observations above are reproducible, but the attribution is wrong. The
addition does not contain an "assignment at impl level". It declares a local
`var literal` and reassigns it in three `match` arms, and `literal` lexes to
`TokenKind::Literal`, which the statement dispatcher routed unconditionally to
`parse_literal_function` (which `expect`s `Fn`). Four-line repro:
`fn main():` / `var literal = 1` / `literal = 2` — same
`expected Fn, found Assign`.

That parser defect was **already fixed** at `d7213eb61742` (2026-08-17 07:36Z),
and the separate `Use angle brackets: X<...>` false positive — which is a
**warning**, not an error; `bin/simple run` on the file exits 0 — at
`17d3496f3f3` (2026-08-17 12:14Z). The deployed `bin/simple` was built
**2026-08-16 22:59Z**, so it predates both. The repo-wide parse block is a
STALE-SEED artifact; the correct action is to rebuild and redeploy the seed, not
to edit any `.spl`.

Also corrected: `check-native-trailing-default-param.shs` does NOT fail its
selftest. From the main tree it reaches its real scan and reports
`FAIL — native-build failed to compile the fixture (exit 1, ...)`, exit 1, caused
by `llc-20: invalid redefinition of function '__simple_main'` — an unrelated LLVM
lane defect.

Full record: `doc/08_tracking/bug/deployed_seed_predates_landed_parser_fixes_blocks_repo_2026-08-17.md`.

## 2026-08-17 — sync status, and a guard-integrity finding

**Landed at origin (verified BY CONTENT, not by commit success):**

| lane | probe at `origin/main` | hits |
|---|---|---|
| A flags | `unstable_mode` in `test_runner_types.spl` | 3 |
| B classification | `CRASHED:` in `test_executor_parsing.spl` | 2 |
| F timeout | `limit_is_unverified` in `test_runner_execute.spl` | 4 |
| C fixtures | `test/fixtures/unstable_mode/` | 5 files |

These reached origin via OTHER lanes' pushes sweeping them out of the shared
tree — not via any push of mine.

**LANDED — corrected 2026-08-18.** This block previously read "**NOT landed:**
the single-spec fix `d03b800c7d6` (`make_result_from_output` in
`test_runner_single.spl` = **0** at origin)". That is no longer true and the
stale claim is corrected here rather than left standing.

Re-verified BY CONTENT at `origin/main` (`923c5690ccd`), the same way the table
above is verified:

| probe at `origin/main` | hits |
|---|---|
| `make_result_from_output` in `src/app/test_runner_new/test_runner_single.spl` | **2** |

Both hits are live, not incidental: the import at line 37
(`use std.test_runner.test_executor_parsing.{make_result_from_output}`) and the
call at line 1070 (`val outcome = make_result_from_output(run.path, ...)`), with
the OK/ERROR/CRASHED/TERMINATED/TIMEOUT/NOT_RUN contract described in the file
header at line 30. So `bin/simple test <one_file.spl>` DOES have
abnormal-termination classification at origin today.

It reached origin via `0f5b67b79b4e` ("fix(guards): remove three guard
fail-opens; revive 15 dead env_get fallbacks") — again another lane sweeping the
shared tree, not a push of this lane. `d03b800c7d6` itself was never pushed as a
commit; only its content landed. The pre-push-hook blockage recorded below was
real at the time and is left as written — it is history, not a live claim.

Note the four `test_runner_single.spl` copies under `src/lib/*/test_runner/`
still have **0** hits; the classification lives only in the `src/app` copy. That
is a separate, unclosed divergence, not evidence against the above.


### Guard-integrity finding: the verdict depends on the WORKING TREE, not on what is pushed

`check-native-trailing-default-param.shs` runs a real `native-build`, which reads
`src/` as SOURCE **from the tree it is invoked in**. Consequences, both observed:

- From a clean worktree checked out at `origin/main`: the broken
  `expr_dispatch.spl` fails the guard's own selftest -> push BLOCKED.
- From `/mnt/data/worktrees/simple-main`, whose working copy holds a *parsing*
  version of that file: the guard proceeds -> push ALLOWED.

**Same commits, opposite verdicts.** That is how other lanes are landing while a
clean checkout of origin cannot. It also means the guard can green a push while
origin itself is unbuildable — the precise failure class the guards exist to
prevent.

**Deliberately NOT worked around.** Dropping the main tree's parsing copy into
the landing worktree would let the guard run and the push succeed, but the
verdict would describe a tree nobody is pushing. That is `--no-verify` wearing a
disguise, and the standing instruction forbids it. Blocked and reported instead.
clobber pattern this repo keeps suffering. The owning lane must repair the
assignment-at-impl-level inside that addition. The main tree's parsing copy is
the reference for what a working version looks like.

## 2026-08-17 — sync status, and a guard-integrity finding

**Landed at origin (verified BY CONTENT, not by commit success):**

| lane | probe at `origin/main` | hits |
|---|---|---|
| A flags | `unstable_mode` in `test_runner_types.spl` | 3 |
| B classification | `CRASHED:` in `test_executor_parsing.spl` | 2 |
| F timeout | `limit_is_unverified` in `test_runner_execute.spl` | 4 |
| C fixtures | `test/fixtures/unstable_mode/` | 5 files |

These reached origin via OTHER lanes' pushes sweeping them out of the shared
tree — not via any push of mine.

**LANDED — corrected 2026-08-18.** This block previously read "**NOT landed:**
the single-spec fix `d03b800c7d6` (`make_result_from_output` in
`test_runner_single.spl` = **0** at origin)". That is no longer true and the
stale claim is corrected here rather than left standing.

Re-verified BY CONTENT at `origin/main` (`923c5690ccd`), the same way the table
above is verified:

| probe at `origin/main` | hits |
|---|---|
| `make_result_from_output` in `src/app/test_runner_new/test_runner_single.spl` | **2** |

Both hits are live, not incidental: the import at line 37
(`use std.test_runner.test_executor_parsing.{make_result_from_output}`) and the
call at line 1070 (`val outcome = make_result_from_output(run.path, ...)`), with
the OK/ERROR/CRASHED/TERMINATED/TIMEOUT/NOT_RUN contract described in the file
header at line 30. So `bin/simple test <one_file.spl>` DOES have
abnormal-termination classification at origin today.

It reached origin via `0f5b67b79b4e` ("fix(guards): remove three guard
fail-opens; revive 15 dead env_get fallbacks") — again another lane sweeping the
shared tree, not a push of this lane. `d03b800c7d6` itself was never pushed as a
commit; only its content landed. The pre-push-hook blockage recorded below was
real at the time and is left as written — it is history, not a live claim.

Note the four `test_runner_single.spl` copies under `src/lib/*/test_runner/`
still have **0** hits; the classification lives only in the `src/app` copy. That
is a separate, unclosed divergence, not evidence against the above.


### Guard-integrity finding: the verdict depends on the WORKING TREE, not on what is pushed

`check-native-trailing-default-param.shs` runs a real `native-build`, which reads
`src/` as SOURCE **from the tree it is invoked in**. Consequences, both observed:

- From a clean worktree checked out at `origin/main`: the broken
  `expr_dispatch.spl` fails the guard's own selftest -> push BLOCKED.
- From `/mnt/data/worktrees/simple-main`, whose working copy holds a *parsing*
  version of that file: the guard proceeds -> push ALLOWED.

**Same commits, opposite verdicts.** That is how other lanes are landing while a
clean checkout of origin cannot. It also means the guard can green a push while
origin itself is unbuildable — the precise failure class the guards exist to
prevent.

**Deliberately NOT worked around.** Dropping the main tree's parsing copy into
the landing worktree would let the guard run and the push succeed, but the
verdict would describe a tree nobody is pushing. That is `--no-verify` wearing a
disguise, and the standing instruction forbids it. Blocked and reported instead.

## 2026-08-17 — BUILD-SIDE PROCESS ISOLATION IS GENUINELY BLOCKED (082200ce8af)

Answered by reading code, with file:line evidence. **A child process CANNOT
compile one module from its source path alone.** Field offsets in a module's MIR
are a function of the WHOLE PROGRAM:

- One `MirLowering` instance is shared across all modules
  (`driver_pipeline_lowering.spl:202,255`), and a whole-program PREPASS registers
  every module's HIR struct layout before any module lowers (`:209-215,262-263`).
  The comment at `:203-208` records why: without it an imported struct's field
  order is unknown and `resolve_field_index` defaulted to 0 — a cross-module
  SEGV. Consumed at `module_lowering.spl:896,905-926`.
  **A source-only child would emit objects with WRONG FIELD OFFSETS, silently.**
- Two whole-program passes mutate `mir_modules` AFTER lowering: async state
  machines (`driver_pipeline_passes.spl:27`), AOP rewrites
  (`driver_pipeline_aop.spl:94-126`).
- `_compile_frozen_module_capsule` fails `capsule-registry-mismatch` unless the
  storage registry identity matches — a hash over ALL modules' rows plus
  `mir_modules.keys()` (`driver_types.spl:806-839,786-789`), unreproducible from
  one closure; re-registration is refused once frozen (`:618,641`).
- Existing single-file entries (`driver_api_compile_single.spl:12-55`,
  `driver_api_native_single.spl:11,24`) take one path but load the ENTIRE import
  closure and lower it together — recompiling the closure N times, the opposite
  of the goal.

**MIR serialization does not exist.** `grep -rn deserialize | grep -i mir` = 0
hits (control `serialize_mir_module` = 3, so the scan works).
`mir_serialization.spl:13` is explicitly a lossy functions-only compatibility
shape that drops statics/constants/types; `mir_json.spl` is emit-only.
`FrozenStorageModuleSnapshotV1` has no serializer at all.

**Shortcut explicitly REJECTED (record this so nobody retries it):** the parent
could pass `capsule_identity` on argv so a child writes a conforming
`.capsule-receipt` (`driver_aot_native_output.spl:186-196`). That would let
`driver_native_collect_capsule_result_v1` (`:198`) promote a WRONG-OFFSET object
into the cache as AUTHENTICATED — a green build producing a miscompiled program.
Strictly worse than today's loud SIGSEGV.

**Precondition to unblock — one of:**
1. a round-trippable MIR + storage-snapshot format WITH a reader, gated by a
   `serialize -> deserialize -> native_capsule_mir_identity_v1` identity test;
   then the one-module CLI really is small; or
2. source-derivable stable field ordering for imported structs — i.e. the
   still-zero-caller `interface_digest_of` (`cache/action_key.spl:199`).

**Scope of what is actually missing:** run-to-end and outcome classification
ALREADY work in-process on the build side. Only crash CONTAINMENT is blocked.

## 2026-08-17 — build-side outcome contract now SPECCED (91f4147088a, 4213a69da10, f927cb0d4de)

`test/01_unit/compiler/driver/build_unit_outcome_from_status_contract_spec.spl`
— 19 examples, `Results: 19 total, 19 passed, 0 failed`, rc=0.
Sabotage green->red->green: 19/0 -> sabotage SIGTERM(143) class to CRASHED ->
`19 total, 18 passed, 1 failed` (`expected TERMINATED to equal CRASHED`) ->
restored -> 19/0. **The spec bites.**

### CORRECTION TO THIS LANE'S OWN BRIEF — 137 is NOT TERMINATED

My spec brief asserted SIGKILL(137) -> TERMINATED/not-a-failure. **That was
wrong and the code is right.** `build_outcome.spl` classifies ONLY SIGTERM(15)
as TERMINATED; an unbudgeted SIGKILL(137) is **CRASHED, a failure**. The lane
caught it honestly on first run (`19 total, 18 passed, 1 failed`) and pinned the
IMPLEMENTATION rather than the brief.

The reasoning is sound and worth preserving: **earlyoom sends SIGTERM**, which is
the never-a-failure path. A raw SIGKILL is indistinguishable from the compiler
dying, so treating it as unverified would suppress real crashes. A
budget-killed 137 is TIMEOUT via the `timed_out` flag, not via the signal.

### The artifact rule lives in the SUPERVISOR, not the classifier
`from_status` sees only a wait status. `build_supervised` (parallel.spl
~816-828) does the `artifact_fn` + `rt_file_exists` join and substitutes status 1
with `"exit 0 but declared artifact is missing"`. Both halves pinned.

### No duplication
`build_outcome_classification_spec.spl` already covers the free function
`build_outcome_classify_status` + summary determinism. This spec covers the
record constructor callers actually use, the aggregate arithmetic, and the
artifact join.

### NEW TREE HAZARD — history rewrite under running lanes
Commit `73b8d9005b3` was silently DROPPED from the file's history by a
concurrent lane's history rewrite between two runs; `git checkout --` then
restored PRE-correction content. Recovered from the orphaned blob, re-landed as
`4213a69da10`. **This tree rewrites HISTORY under running lanes, not just wipes
uncommitted work.** Verify a landed commit is still an ancestor before trusting
it.

## 2026-08-18 — parallel fan-out round: THREE stale problem statements, TWO false defects

Ten lanes, file-disjoint. The headline is not what was fixed — it is how much
of this document was **already wrong**.

### Three lanes found their problem statement STALE

| lane | recorded as | actual |
|---|---|---|
| TYPES | `paths: [text] = []` uncommitted and unparseable, blocking measurement | COMMITTED; parses `rc=0`, zero diagnostics. Struct field defaults ARE supported — proven semantically (field omissible from the constructor, initialises to the default), with a no-default control. No bug filed. |
| SINGLE | "single-spec path bypasses classification entirely — largest remaining gap" | CLOSED by `d03b800c7d6`. `test_runner_single.spl:37,1057,1070`. |
| HELP | `--unstable` has no user-visible help text | Already committed in `c7584b189f1` across THREE renderers. |

Lesson: brief lanes as VERIFY-OR-REFUTE, never assume-and-fix. Two of the three
then found a REAL defect underneath the stale one.

### TWO false defects were generated BY MISREADING A DOCSTRING AS CODE

The requirements audit (`1d3a3a7ee2a`) reported two contract violations. Both
are wrong, and the orchestrator RELAYED them before checking — including
sending one to the FORK lane as a fix instruction (it arrived after that lane
finished; no damage, by luck not care).

- **R2a WRONG.** Claimed `test_runner_fork.spl:72` puts SIGKILL(9) in
  `is_outside_kill`. The predicate is `signo == 1 or signo == 2 or signo == 15`
  — SIGKILL deliberately excluded, with a docstring that already states the
  reasoning AND the earlyoom-escalation tension. Line 72 is INSIDE that
  docstring. The code was correct all along.
- **R2b MISCHARACTERISED.** Claimed `test_executor_parsing.spl:444` "handles
  only -1/143/144, lanes disagree". The subprocess path CANNOT SEE 137 — the
  Rust boundary collapses every signal AND timeout into one `-1`
  (`env_process.rs:508,535`). It disambiguates by crash SENTINEL FILE then
  fault-diagnostic evidence. Two mechanisms for two lanes with different
  information, not a disagreement.

**Rule for this lane going forward: distinguish docstring/comment from code
before asserting what a line does.** Still genuinely open from that audit: two
lanes return different unverified exit codes (2 vs 5).

### THE SCOPE FINDING — what `unstable_mode` actually does

Exhaustive read-site grep (lane ISOLATION, `unstable_mode` across all `src/**`
`.spl`+`.rs`) proves the mode has **exactly ONE behavioural effect**:
`test_runner_main.spl:205-207`, `fail_fast = false`. Everything else is field
decls, arg parsing, a banner, a Rust help test, and an unrelated same-named
`ParallelBuildConfig.unstable_mode()` whose consumer `build_supervised()` has
zero callers. `test_runner_execute.spl` never reads it (its one textual hit is
a comment).

Per-spec process isolation is REAL but **UNCONDITIONAL** — every path
(`:186`, `:288`, `:807`) spawns a child regardless of the flag, and predates
this work.

**Recommendation (b), accepted: keep isolation unconditional and redefine the
mode as "classification + run-to-end".** Isolation is a PRECONDITION of the
outcome contract, not a feature of the mode: CRASHED/TERMINATED/TIMEOUT are all
derived from a child's exit code, so gating it would make ordinary runs
strictly less able to report the truth, for an unmeasured speed gain via an
in-process path that does not exist. The real gap is the BUILD half, which the
old framing hid.

No `unstable_mode_effect_*` spec was written, deliberately: it could only
assert a visible one-line assignment and cannot observe isolation (no contrast
case, because it is unconditional). That would be theatre.

### Build side: STAY BLOCKED (design note `c6d36085d60`)

Verified blockers: (1) shared `MirLowering` + whole-program HIR struct-layout
prescan (`driver_pipeline_lowering.spl:202,209-215`) — field indices are a
function of the WHOLE program, so a child re-deriving from a source path emits
wrong offsets; (2) `capsule-registry-mismatch` hard-fail
(`driver_aot_native_output.spl:906`), identity hashed over all modules; (3) NO
MIR deserializer (0 hits; the serializer that exists is explicitly lossy).
Every shortcut converts a loud SIGSEGV into a silently miscompiled,
cache-authenticated object. Cheapest partial win, UNVERIFIED: supervise the
LINK step only.

### Fork mode: classification is good, but it has NEVER RUN

`fork()` WITHOUT `exec` (`runtime_fork.c`, no `exec*` anywhere). Its
`classify_fork_exit` is strictly BETTER than the subprocess path — it reads
`128+WTERMSIG` instead of the `-1` sentinel. But **the fork SFFI bridge is
absent from the deployed seed**: `strings | grep -c rt_fork` = 0 against
non-empty controls. So that classifier has never once executed. COW-inherit is
NOT fresh-process-per-unit; adding `exec` would destroy fork mode's only
advantage. Filed, not half-fixed.

### Incidental compiler defect, wide blast radius

A function-local binding written WITHOUT `val`/`var` (`o = 5`) resolves as a
GLOBAL in HIR, takes the global arm in MIR (`lowering_stmt.rs:795-809` vs the
local arm at `:812`), and makes Cranelift fail closed — **the entire enclosing
function body loses native codegen** and silently falls back to the
interpreter at exit 0. Under `SIMPLE_ALLOW_STUB_FALLBACK` those functions get
empty stubs, i.e. silently WRONG results. Minimised by ablation; struct
defaults, constructors, interpolation and `.len()` are all innocent. Filed
`0a1b18836d2`, not fixed (resolver name-binding change, collides with genuine
module-global assignment). Census of the blast radius in progress.

### Push blocker: root cause is NOT fixable in a guard

Both remedies the compiler's own error text names are DEAD, measured: a
**2-file** `--source` dir times out identically to the full tree (the worker
loads the whole compiler+LLVM graph regardless of input size), and `--timeout`
is already at the 2-hour default. Guard diagnostics fixed instead (tail-based,
selftest 4 -> 10 assertions, fail-closedness re-proven by mutation). The
blocker correctly still blocks.
