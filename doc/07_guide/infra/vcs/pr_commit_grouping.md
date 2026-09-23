# PR Commit Grouping

**Group commits into a few logical, single-concern commits before opening a PR,
and again before every push to an open PR.** A PR whose history is a raw agent
session log (wip, fix typo, address review, retry, reseal, sync, revert-then-
redo pairs) is slower to review, slower to land, and risks re-landing content
already on `main`. This is a hygiene rule, not a rewrite-history-for-its-own-
sake rule: functional commits with real standalone value can stay separate.

## What to drop or squash

- `wip`, `fix typo`, `address review`, `retry`, `reseal`, `sync` commits — fold
  into the commit they fix.
- Revert-then-redo pairs — squash to the final state; the revert adds no signal.
- Commits whose change is already on `main` — check before squashing:
  ```bash
  git cherry origin/main HEAD          # '-' prefix = equivalent patch already upstream
  # or compare patch-ids directly (match the left column of both):
  git log -p origin/main..HEAD | git patch-id
  git log -p HEAD..origin/main | git patch-id
  ```

## Non-interactive recipes

There is no interactive editor in this environment, so `-i` only works with the
sequence editor stubbed out (`GIT_SEQUENCE_EDITOR=:`), as in recipe 1 below.
Use one of:

```bash
# 1. Fold a fixup into an earlier commit, no editor
git commit --fixup=<sha>
GIT_SEQUENCE_EDITOR=: git rebase -i --autosquash origin/main

# 2. Reset to the merge-base and re-commit by concern, staging explicit paths
git reset --soft $(git merge-base origin/main HEAD)
git add <paths-for-concern-1> && git commit -m "..."
git add <paths-for-concern-2> && git commit -m "..."

# jj
jj squash --from <rev> --into <rev>
```

## One PR = one concern

- Target under ~60 changed files per PR; never bundle unrelated scopes in one
  branch.
- Evidence from 2026-09-23: PR #1228 (39 commits, 9 of them already on `main`
  or superseded by later commits in the same branch) took hours and 4 agents
  to untangle and had to be split into 2 PRs. PR #1375 (100 commits / 525
  files) also had to be split. Both costs were entirely avoidable by grouping
  before the first push.
- Stacked PRs are risky: if the carrier PR gets closed, its stacked children's
  content is stranded (#1344/#1360 both hit this). Prefer independent, small
  PRs over a stack unless the stack is short-lived and actively landed.

## Keep the branch fresh

A branch more than 64 commits behind `main` cannot be updated through the
pre-push hook (it is range-bound and refuses to scan a range that large).
Rebuild: take `origin/main` plus only your own commits (`git cherry`/patch-id
to confirm which are yours and not already upstream) onto a fresh branch, and
supersede the old PR rather than fighting the rebase.

## Tracking-DB commits (`doc/08_tracking/**/*.sdn`)

Keep tracking-DB edits (`bug_db`, `todo_db`, `test_db`) in **one small commit
per PR**. Before that commit: `git merge origin/main`, take `main`'s copy of
the file, re-apply only the PR's own row changes on top, and reseal **last**
with `scripts/check/reseal-sdn-crc32.shs` (header CRC must match body, rows
must be `>=` what's on `main`). PRs touching these files land serially, one at
a time — do not batch several such PRs' pushes together.

## Before you push — checklist

1. `git log origin/main..HEAD --oneline` — does every commit read as a
   distinct, reviewable concern? If you see "wip"/"fix"/"retry" text, squash.
2. `git cherry origin/main HEAD` — any `-` lines? Drop those commits.
3. File count: `git diff --stat origin/main..HEAD | tail -1` — over ~60 files
   for one concern? Split the PR.
4. Tracking-DB files touched? Confirm they are resealed last, in their own
   commit.
5. Branch depth: `git rev-list --count origin/main..HEAD` — over 64? Rebuild
   on a fresh branch instead of rebasing.

See also: `.claude/rules/vcs.md` (push/land mechanics),
`doc/07_guide/infra/vcs/pr_landing_timing_race.md` (timing/admission race).
