# seed-builds guard selftest commits into the REAL repo and corrupts the index

Status: OPEN P1. Filed 2026-08-19.

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
