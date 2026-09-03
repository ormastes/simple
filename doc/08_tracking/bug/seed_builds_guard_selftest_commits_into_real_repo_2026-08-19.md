# seed-builds guard selftest commits into the REAL repo and corrupts the index

Status: RESOLVED (2026-09-02). Filed 2026-08-19.

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

## RESOLVED 2026-09-02

`scripts/check/check-seed-builds-push.shs` now implements exactly the fix
requested above:

- Every git-touching fixture (including the incident-replay fixture at
  `st_repo="$TMPROOT/selftest-incident-repo"`, `TMPROOT=$(mktemp -d)`) lives
  under a private temp dir, never the caller's repo.
- A `git_in_repo()` helper wraps every git invocation with
  `env -u GIT_DIR -u GIT_WORK_TREE -u GIT_INDEX_FILE -u GIT_COMMON_DIR git -C
  "$gir_repo" "$@"`, with a comment explicitly naming the ambient-env-leak
  mechanism this bug hit ("an inherited GIT_DIR overrides -C and can make a
  fixture's `git init` and `git commit` operate on the repository whose push
  invoked this guard").
- The fixture's author identity is set per-invocation via
  `git_in_repo "$st_repo" config user.email guard@selftest` — scoped to the
  fixture repo path via `-C`, never the caller's repo's config.

**Verified live** (not just read): captured `git rev-parse HEAD` and
`git status --short` immediately before and after running
`sh scripts/check/check-seed-builds-push.shs --selftest` in the real
worktree. Both were byte-identical before and after:
```
check-seed-builds-push: selftest 7/7 fixtures correct (...)
check-seed-builds-push: PASS — 7 fixture(s) checked (selftest only, scan skipped)
```
HEAD unchanged (`1b76db1d6c3`), `git status --short` unchanged (5 lines,
same 5 lines) across the run. This demonstrates the "after" (fixed) direction
directly; the "before" (broken) direction is demonstrated by a from-scratch
disposable git repo running a deliberately incident-shaped fake guard (commits
into `$PWD` with no `mktemp -d`/`-C` isolation), which the new class-level
regression guard below correctly reports as FAIL.

Regression guard added:
`scripts/check/check-guard-selftest-repo-isolation.shs` — runs a list of
guard scripts' `--selftest` and asserts the invoking repo's HEAD and
`git status --porcelain` are unchanged before/after, for both
`check-ghdl-gate-rc-swallow.shs` (see
`doc/08_tracking/bug/pre_push_hook_selftest_commits_fixtures_into_invoking_repo_2026-08-21.md`,
same defect class) and this guard, `check-seed-builds-push.shs`. Verified
BOTH directions: PASS on the two real (fixed) guards; FAIL, naming the
guard and the exact HEAD-move, against a deliberately broken fixture guard
built in a disposable throwaway repo replaying this incident's exact shape
(commits straight into the caller's `$PWD`).

Not fixed by this change: whether `check-seed-builds-push.shs --selftest`
itself is invoked from a genuinely isolated worktree/CWD by every caller
(the pre-push hook, an interactive session) is outside this record's scope —
see
`doc/08_tracking/bug/pre_push_hook_selftest_commits_fixtures_into_invoking_repo_2026-08-21.md`
for the broader, still-open push-gate-wiring gap around this defect class.
