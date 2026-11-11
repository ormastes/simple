# seed-builds guard selftest commits into the REAL repo and corrupts the index

Status: FIXED 2026-11-11 (lane p3-comp10) — isolation in source since cf188f01f884; isolation guard PASS (0 changed caller HEAD/index/config/status)

## What happened
Running `sh scripts/check/check-seed-builds-push.shs <range>` from a worktree
(/mnt/data/worktrees/render-harden, branch land-rendering) at 15:44 UTC:
- committed TWO commits into the real branch, authored `guard <guard@selftest>`:
  "seed (already broken) + docs" and "docs(tracking): docs-only tip, touches
  no seed file" — these are its SELFTEST fixture commits, which must live in a
  scratch fixture repo, never the repo under test;
- leaked `git config user.email=guard@selftest` / `user.name=guard` into the
  real repo config (worktree-scoped), so every later commit carried the
  selftest identity;
- left the index in a state where subsequent targeted `git add <paths>` +
  commit produced WIPED trees (tip fell from 116,204 to 45 files across 11
  commits). check-tree-size-push caught it pre-push (11 structurally wrong,
  runtime-api "2789 removed", seed-builds E0432 on its own wiped tree).

## Recovery (done this session)
Rebuilt the branch as land3 by replaying each real commit's blobs onto the
last healthy tree with read-tree/update-index/commit-tree, skipping the two
selftest strays; tree-size and runtime-api guards PASS on the rebuilt range;
repo user identity restored.

## Fix needed
The selftest must create its fixture repo under a temp dir (mktemp -d),
export GIT_DIR/GIT_WORK_TREE (or cd) to it for every git call, and set its
author via `-c user.email=...` per-invocation — never `git config` in the
caller's repo. A selftest that cannot guarantee isolation must refuse to run
from a non-fixture repo. Add a fixture asserting the caller's repo is
byte-identical (HEAD, index, config) after --selftest completes.

## Triage 2026-11-11 (lane p3-comp10)

Verdict: FIXED. Fresh re-verification at lane base 79d5af6723f6:

- Root-cause fix: cf188f01f884 ("fix(check,std): guard-selftest repo isolation +
  std.spec last-expect-wins closure (bugdb batch D)", 2026-09-02) IS an ancestor
  of the lane base. It verified the selftest isolation and added the class-level
  regression guard scripts/check/check-guard-selftest-repo-isolation.shs.
- Source at tip (fresh inspection): every selftest fixture lives under
  TMPROOT=$(mktemp -d) (scripts/check/check-seed-builds-push.shs:776); every git
  call targets a fixture repo through git_in_repo(), which strips ambient
  GIT_DIR/GIT_WORK_TREE/GIT_INDEX_FILE/GIT_COMMON_DIR then runs
  `git -C <fixture>` (:197-203); the `guard@selftest` identity is set with
  `git_in_repo "$st_repo" config ...` on the FIXTURE repo only (:583-584). The
  selftest also replays the 2026-08-18 incident shape (fixture repo under
  TMPROOT, docs-only range over a broken untouched seed, :559-597). The doc's
  fix requirements (temp-dir fixture repo, per-invocation identity, no
  `git config` in the caller's repo) are all met; the "fixture asserting the
  caller's repo is byte-identical after --selftest" requirement is met by the
  class-level guard's snapshot_repo comparison (head-commit, HEAD, index,
  config, config.worktree, status).
- Behavioral (fresh, tracked-seed-era host): the class-level guard
  (check-guard-selftest-repo-isolation.shs), scoped to
  GUARD_ISOLATION_GUARDS="scripts/check/check-seed-builds-push.shs", ran to
  completion in 348s: "check-seed-builds-push: selftest 7/7 fixtures correct ...
  PASS — 1 guard(s) checked in scratch clones with hook-style Git exports, 0
  changed caller HEAD, index, config, or status", GUARD_RC=0. Log at
  build/review/comp10-probes/guard-seedbuilds-only.log.
- Environment note: the guard's DEFAULT_GUARDS set (which prepends
  check-ghdl-gate-rc-swallow.shs) could not complete on this Windows host — the
  ghdl guard's selftest stalls (no ghdl toolchain; two attempts timed out at
  541s/570s without reaching any FAIL). That is an unrelated host/toolchain gap,
  not a defect in the seed-builds guard; the scoped run above is the direct
  evidence for this row.
