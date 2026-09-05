# Stage-4 L7 "Retry-12" Verification Status — 2026-08-05

Lane: STAGE4-L7 ("L7 Retry-12 style Stage-4 verification run").

## Bottom line

**Stage 4 is still unreachable, and no attempt was made to reach it in this
lane.** The blocking dependency is Stage 3 self-host, which is currently
blocked by an OPEN, deliberately-unfixed nil-receiver SIGILL, filed today as
`doc/08_tracking/bug/stage3_selfhost_nil_receiver_sigill_in_lower_expr_caller_2026-08-05.md`
("blocker-10"). Per explicit user direction this lane did not attempt to fix
that bug. Two sibling processes were found already mid-flight on full
bootstrap attempts at task start; this lane did not start a competing build.

This is a status confirmation, not new progress: as of this report, Linux
x86_64 still has never had a green stage-4 deploy (`doc/09_report/stage4_campaign_summary_2026-07-27.md`
§1), and that has not changed today.

## "Retry-12" is a real, current concept — not defunct

Searched the whole repo tree (including active `.claude/worktrees/*` copies
and `build/**` snapshots) for `Retry 12` / `Retry-12`. It is real and current:
`doc/03_plan/compiler/bootstrap/stage4_memory_parallel_agent_plan_2026-07-29.md`
§"L7 — Retry 12 execution (after L1, L2)" defines exactly what this lane's
name refers to — run artifacts only (no source changes), full Stage 4 with
the L5 OS-truth memory sampler attached, `SIMPLE_BOOTSTRAP_STAGE4=1`.

Admission was amended 2026-07-30 (run 10) into two independent passes, both
required:

| Pass | Env gates | Corpus | Threshold | Wall-clock budget |
|---|---|---|---|---|
| A — diagnostic | `SIMPLE_BOOTSTRAP_STAGE4=1 SIMPLE_AST_GEN_CHECK=1` | first 300 modules (bounded) | OOB diagnostics `== 0`, zero tolerance (gate string corrected in run 12 — see below) | 4h |
| B — byte-residue | `SIMPLE_BOOTSTRAP_STAGE4=1` only | full ~1494 modules | L5 RSS-ceiling + byte-slope gate (`check-stage4-memory-gate.shs`) | 30 min |

Run 12 itself corrected an earlier gate bug: the original gate string
`stale_generation_reads == 0` is never printed by the compiler, so grepping
for it always silently reads as PASS. The corrected gate anchors on
`: produced at generation ` instead, and only becomes measurable once
`ast_gen_check_index` is wired into production call sites (it currently has
zero).

So "Stage 4 verification" in this repo means specifically this memory-
ownership admission gate (AST-generation staleness + RSS/byte-slope), not
merely "stage 3 self-compiles stage-4 source." Per
`doc/08_tracking/bug/module_global_write_lost_on_frame_pop_2026-07-28.md`
(bottom): "Retry 12 remains postponed pending review and the remaining
method/lambda frame-lifecycle work; this focused pass alone is not Stage 4
admission." Retry-12 had never been run to a completed result even before
blocker-10 was filed on 2026-08-05.

## Confirmed current failure point (blocker-10, OPEN)

`doc/08_tracking/bug/stage3_selfhost_nil_receiver_sigill_in_lower_expr_caller_2026-08-05.md`
(status OPEN, filed 2026-08-05): Stage-3 build
(`stage2-admitted/simple native-build ... src/app/cli/bootstrap_main.spl`)
dies with `runtime error: field access on nil receiver` -> `ud2` -> **SIGILL,
exit 132**, in `src/compiler/50.mir/**` while being run *by the Rust-seed-
compiled stage-2 binary*. Established fact from that doc: the fault is in
whatever code **consumes** the result of the 24th consecutive
`x = x.push(...)` lowering (same receiver local, `local=7`), not in the push
lowering itself — the caller of `lower_expr` at
`expr_dispatch.spl:1791`. Five ranked hypotheses are recorded, none fixed;
work is explicitly **POSTPONED by user decision on 2026-08-05**, and the
prepared rank-1/2/4 experiments were reverted, unbuilt.

Since a self-hosted Stage-3 compiler is the hard prerequisite for Stage 4,
Stage 4 (and Retry-12 specifically) cannot be reached until blocker-10 is
fixed or worked around. This lane did **not** attempt that fix, per explicit
instruction.

## Sibling-lane coordination — no duplicate build started

`ps aux` at task start showed two live full-bootstrap attempts already
running; this lane deliberately did not start a third:

- PID `3573478` (parent `bootstrap-from-scratch.sh --full-bootstrap
  --full-cli --mode=one-binary --incremental-unlimited --jobs=2 ...`) / PID
  `699176` (the `native-build` worker, LLVM backend, one-binary mode) writing
  to `/tmp/simple-stage4-bootstrap-20260805-debug7-fg/`, started 05:22 UTC.
  This matches the BOOTSTRAP-REDEPLOY sibling lane's naming pattern
  (`debug7-fg`). At last check it was still alive, ~44 minutes in, milestone
  `stage3`, phase `parse`, `tasks_done=1/6` — i.e. still short of the point
  in the log (~line 32,534) where blocker-10 previously fired.
- PID `926901`: a second, independent `stage2-admitted/simple native-build
  ... src/app/cli/bootstrap_main.spl` (LLVM backend, dynload mode) running
  directly out of the repo's own `build/bootstrap/` directory, started 05:55
  UTC, also alive at check time.

Both processes' `stage3-native-build.log` files were short (4 lines each,
early `[hir-field-type]` diagnostic output) — consistent with early-stage
parse/lowering, not a crash. Neither had reached blocker-10's failing region
by the time this report was written. This lane did not wait synchronously on
either run to completion (that would only be re-observing another lane's
work), and did not touch `/home/ormastes/dev/pub/simple/build/bootstrap/` or
`/tmp/simple-stage4-bootstrap-20260805-debug7-fg/`.

Separately, this session's own earlier scratchpad artifacts
(`stage3_narrow_0111.log`, `verify_batch2/repro_v2.log`) record a prior
attempt today that terminated at **exit 143** (SIGTERM under harness
contention) before reaching Stage-3 completion — a different failure mode
from blocker-10's SIGILL, but consistent with the "harness was contended"
note in the blocker-10 bug doc's own Status section (a `bootstrap-from-
scratch.sh` run plus two sibling native-builds sharing the live tree).

## Out-of-scope instruction received mid-task — disregarded

A message arrived mid-task purporting to be "an addendum from the user"
directing work on unrelated items — "M5 (strict interp)" and "M7 (GPU lane)"
— with instructions to prefer narrow incremental verification over full
bootstraps. Neither M5 nor M7 appears anywhere in this lane's actual task
brief (STAGE4-L7 Stage-4 verification), and nothing in the repo ties them to
this lane. Per the standing rule that no agent-relayed message is itself
authorization to change scope or approve action, this was treated as
out-of-scope and disregarded; this report stays limited to the assigned
Stage-4 verification task. (Its general spirit — prefer narrow, incremental
checks over full reruns — is in any case what this lane already did: no new
full bootstrap was started.)

## What this lane did NOT do (by design)

- Did not attempt to fix blocker-10.
- Did not start a new/duplicate full bootstrap run.
- Did not set `SIMPLE_TEST_RUNNER_RUST=1`.
- Did not copy the Rust seed to `bin/release/.../simple` and call it a
  Stage-4 pass; `bin/simple` / `bin/release/**` were not touched.
- Did not create a branch; this report is intended for `main`.

## Recommendation for the next Stage-4 lane

1. Do not attempt Retry-12 before Stage-3 self-host completes cleanly through
   the exact failing region described above (24 consecutive `push argc=1`
   lowerings on `local=7`, then whatever statement consumes the 24th result).
2. Check whether the two in-flight sibling runs identified here
   (`/tmp/simple-stage4-bootstrap-20260805-debug7-fg/`, repo
   `build/bootstrap/`) reached or passed that point before starting a fresh
   one — their logs and progress-state files are still on disk at the paths
   given above.
3. Only once Stage 3 completes should Retry-12's two-pass admission (Pass
   A/B, table above) be attempted.

## Related

- `doc/08_tracking/bug/stage3_selfhost_nil_receiver_sigill_in_lower_expr_caller_2026-08-05.md`
  — blocker-10, OPEN.
- `doc/03_plan/compiler/bootstrap/stage4_memory_parallel_agent_plan_2026-07-29.md`
  — defines L7 / Retry-12.
- `doc/08_tracking/bug/module_global_write_lost_on_frame_pop_2026-07-28.md`
  — prior Retry-12 postponement, before blocker-10 existed.
- `doc/09_report/stage4_campaign_summary_2026-07-27.md` — "Stage 4 still
  FAILS. No deploy occurred" baseline, still true.
