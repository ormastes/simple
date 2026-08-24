# goal-r8 Stage 3 aborted: frozen runtime-authority BEFORE-snapshot deleted mid-run

Date: 2026-08-24
Worktree: /mnt/data/worktrees/goal-bootstrap-frozen (the "frozen" bootstrap worktree)
Log: /mnt/data/tmp/claude-1000/goal-r8-stage4.log

## What happened

A `//bootstrap:stage4` run (adhoc, cranelift, dynload, --jobs=full) was admitted
with a validly minted planner-admission-v2 receipt:

    bootstrap-admission: produced .../build/bootstrap/goal-r8/stage4-admission.env
    bootstrap-policy: receipt-valid target=//bootstrap:stage4 \
        reason=self-host-convergence-check execution=not-attempted

Stage 2 completed and was admitted (~140s, warm cranelift cache):

    Stage 2: seed -> bootstrap_main.spl
    preserved: .../phase_snapshots/phase1_1787575665/simple
    preserved: .../phase_snapshots/phase1_1787575665_phase2_1787575806/simple
    Stage 3: stage2 -> bootstrap_main.spl (self-host)
    Segmentation fault (core dumped)
    error: frozen runtime authority changed during Stage 3

## Diagnosis — the guard message is misleading

The Stage 3 guard (`bootstrap-from-scratch.sh:6465-6472`) is:

    bootstrap_stage3_directory_snapshot "${stage3_provenance_dir}/runtime-after-stage3.txt" ...
    cmp -s "${runtime_admitted_snapshot}" ".../runtime-after-stage3.txt" || {
      echo "error: frozen runtime authority changed during Stage 3" >&2

with `runtime_admitted_snapshot="${stage3_provenance_dir}/runtime-admitted.txt"`
(`:5799`). Post-mortem of the tree shows **only** `runtime-after-stage3.txt`
exists; `runtime-admitted.txt` is GONE. `cmp -s` against a nonexistent file
returns non-zero, so the guard reports "changed" when the real condition is
"the BEFORE snapshot was deleted". The guard cannot distinguish the two.

Corroborating deletions, all while the run was still live:
  - `build/bootstrap/goal-r8/stage2/` — deleted (the admitted Stage 2 binary,
    the very artifact the receipt pins by sha256)
  - `build/bootstrap/goal-r8/logs/` — deleted (so `stage3-native-build.log`,
    the primary evidence for the SEGV, is unrecoverable)
  - free space on /mnt/data jumped 121 GB -> 219 GB at the moment of failure

Something outside this run deleted ~98 GB of build tree mid-bootstrap. That is
exactly the hazard `.claude/memory` records as "never remove trees mid-bootstrap".
`scripts/check/reap-orphan-resource-hogs.shs` was ruled OUT as the culprit: it
reaps PROCESSES only and never deletes trees.

The worktree also carries `DO-NOT-TOUCH.md` asserting "nothing else runs in it",
yet a second lane (`build/bootstrap/goal-r11/`) built there the same morning and
minted its own admission (`build/bootstrap/admission/bd3ee73c...`, 12:57).

## The SEGV is NOT established as a compiler defect

Stage 3 is a dynload build that loads its runtime from the shared
`src/compiler_rust/target/bootstrap` generation symlink. A SEGV is the expected
outcome when that runtime is mutated or removed under a running process. With
`stage3-native-build.log` deleted there is no evidence either way. Do not file
this as a Stage 3 self-host crash without a clean-room reproduction.

## Defects worth fixing (independent of the retry)

1. The Stage 3 guard conflates "snapshot content differs" with "snapshot file
   missing". It should stat the BEFORE file first and emit a distinct typed
   error (e.g. `error: frozen runtime authority snapshot missing during Stage 3`),
   because the two have completely different causes and remedies.
2. Bootstrap output trees under `build/bootstrap/<lane>/` have no liveness
   marker, so a space-reclaiming cleanup cannot tell a live lane from a dead
   one. A lock/heartbeat file that cleanups must honour would have prevented
   the loss.

## DECISIVE UPDATE — the "frozen" worktree is not frozen

A retry was attempted. A trust-root Stage 2 into a fresh lane `goal-r12`
succeeded (exit 0, "Stage 2 admitted; stopping before Stage 3 as requested").
Before minting the stage4 receipt, the bootstrap script was re-read and its
line numbers had MOVED between two greps minutes apart
(`runtime_admitted_snapshot=` 5799 -> 5833; the Stage 3 guard 6470 -> 6498).

Cause, confirmed:

    $ git log -1 --format='%h %ad %s' --date=iso -- scripts/bootstrap/bootstrap-from-scratch.sh
    7a60b69c014 2026-08-24 13:09:08 +0000 fix(bootstrap): reject Stage2 MIR loss
    $ git status --porcelain scripts/bootstrap/bootstrap-from-scratch.sh
    M  scripts/bootstrap/bootstrap-from-scratch.sh
    $ stat -c '%y' scripts/bootstrap/bootstrap-from-scratch.sh
    2026-08-24 13:10:23

Another lane is committing to HEAD and editing `bootstrap-from-scratch.sh`
inside the worktree whose own `DO-NOT-TOUCH.md` states "it is pinned detached
and nothing else runs in it". This is the exact failure mode that file was
created to prevent, recurring one level up: last time it was a `git rebase`
during Stage 2, this time it is edits + a commit to the bootstrap driver itself
during Stage 3.

Consequence: no stage-4 bootstrap can be honestly completed here. Any run is
built from a tree that changes under it, and the admission machinery is
correctly designed to refuse exactly that. The `goal-r12` Stage 2 just admitted
is already provenance-stale, so minting a stage4 receipt against it would pin a
parent whose source tree no longer exists.

STOPPING rather than thrashing. Resolving this requires coordination — halting
the other lane's edits in this worktree, or giving each lane its own worktree —
and stopping another lane's work is explicitly out of scope for this session.

Status: STEP 1 (receipt) proven working. STEP 2 blocked by worktree contention.
