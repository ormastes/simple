# Push-guard selftest escaped into the SHARED repo (identity, core.bare, objects)

- **Date:** 2026-08-01
- **Status:** FIXED — `scripts/check/check-tree-size-push.shs`
- **Severity:** HIGH. One of the three symptoms silently DISABLED all three push
  guards for every lane in the clone.

## Symptoms, all three from one cause

1. **Wrong author on `main`.** Commit `30743ecd6749aa0d5ac59148dc010efe2ac370f7`
   is a legitimate backend fix authored and committed by
   `selftest <selftest@local>`.
2. **`core.bare = true` written to the shared `.git/config`,** repeatedly, and
   repaired at least three times in one day. While it is true,
   `git rev-parse --is-inside-work-tree` is false in EVERY worktree, so
   `check-tree-size-push.shs`, `check-no-conflict-tree-push.shs` and
   `check-no-conflict-markers-push.shs` all exit 2 with
   `ERROR — nothing was checked`, and every push in that window went UNGUARDED.
3. **`too many unreachable loose objects` on fetch.**

## Root cause (PROVED)

`check-tree-size-push.shs` built its 14 selftest fixtures with

    git init -q "$st_dir"
    git -C "$st_dir" config user.email selftest@local
    git -C "$st_dir" config user.name  selftest
    ... git -C "$st_dir" hash-object -w / update-index / write-tree / mktree / commit-tree

`git -C <dir>` only changes the working directory. It does **not** override an
inherited `GIT_DIR`, and this repo's mandated plumbing landing flow exports
`GIT_DIR` and `GIT_INDEX_FILE`. So a lane that ran the guard from such a shell
had every fixture operation redirected at the SHARED repository:

- `git config user.*` wrote the fixture identity into the shared `.git/config`,
  poisoning every subsequent commit made in that clone → symptom 1.
- `git init <path>` with `GIT_DIR` set re-initialises the repo `GIT_DIR` names.
  When `GIT_DIR` carries a **trailing slash** (`.../.git/`) or ends in `/.`, git
  cannot infer the adjacent work tree and writes `core.bare = true` → symptom 2.
  Measured matrix (`git init -q <tmpdir>` against a stand-in repo):

      GIT_DIR unset                      core.bare=false   fixture got own .git
      GIT_DIR=<abs>/.git                 core.bare=false   fixture got NO .git
      GIT_DIR=<abs>/.git/   (slash)      core.bare=TRUE    fixture got NO .git
      GIT_DIR=<abs>/.git/.               core.bare=TRUE    fixture got NO .git
      GIT_DIR=<abs>/.git + GIT_WORK_TREE core.bare=false   fixture got NO .git

- `hash-object -w` / `commit-tree` / `mktree` wrote every throwaway fixture
  object into the shared store, referenced by nothing → symptom 3.

### Single-run reproduction of all three (shipped guard, stand-in repo)

    guard --selftest, with GIT_DIR='<standin>/.git/' exported
    core.bare   false            -> true
    user.email  real@example.com -> selftest@local
    user.name   Real Person      -> selftest
    loose objs  3                -> 30
    guard verdict: PASS — 14 fixture(s) checked   (exit 0)

The guard reported PASS while corrupting the repo it was meant to protect.

### Independent confirmation in the live shared store

The fixture TREES are content-addressed and deterministic. Rebuilding them in an
isolated repo and asking the shared repo for them, all six are `PRESENT`:

    healthy        21f3d2c0a9fdf71e620935ac99a838460959dc2c
    truncated      56bf6d5971dc606c502baf4aeedf1f1f9e510a87
    missing-rt     3275a73b6b0fe68592c51f0e782fedc7c13ad0b2
    src-shrunk     50900a1cd9f6d28fe92cab16beba661d2a904381
    small-shapely  40960415cbda4930958fd80f589e044aa90540fe
    oversize       6f2a816f4b59635b1e3082127e6e16428b94a4cc

A tree of `src/hardware/f0.txt .. f49.txt` all pointing at the blob `x\n` cannot
arise from real repo content. The guard wrote them.

### Onset correlation

66 of the 8,234 commits on `main` are authored `selftest <selftest@local>`, all
dated 2026-08-01, four of them among the last six. The first is `b2d42b02ecc` at
**11:37:21**. `check-tree-size-push.shs` was added by `76c30c1063d` at
**11:12:09** the same morning — 25 minutes earlier. Nothing authored `selftest`
exists before the guard landed.

## Family enumerated

Of the four push guards, only `check-tree-size-push.shs` has a selftest and only
it runs repo-mutating git commands. `check-no-conflict-tree-push.shs`,
`check-no-conflict-markers-push.shs` and `pre-push-conflict-tree-guard.shs`
contain no `git init` / `config` / `hash-object` / `commit-tree` / `mktree` /
`update-index` at all — they only `mktemp` scratch FILES. Nothing to fix there.

## Fix

All fixture git calls now go through `st_env` / `st_git` / `st_git_init`, which
`env -u` every `GIT_*` variable that can relocate a read or a write and pass the
fixture identity **per process** (`GIT_AUTHOR_*` / `GIT_COMMITTER_*`) so no
config file is ever written. `selftest` additionally runs inside a subshell with
those variables unset, which also stops the fixture `CFG_*` thresholds from
surviving into the real scan. The guard snapshots the real repo's `core.bare`
and `user.*` around the selftest and exits 2 if they moved.

## Non-vacuity (RED before GREEN)

New fixture 15, `env-isolation`, builds a decoy repo, exports the hostile
`GIT_DIR=<decoy>/.git/` (the proven `core.bare` trigger), builds a fixture, and
fails if the decoy's `core.bare`, config bytes or loose-object count moves, or if
the fixture repo did not get its own `.git`.

Sabotaging the IMPLEMENTATION — dropping `GIT_DIR` from `ST_ENV_STRIP` and
restoring the bare `git init -q "$1"` — turns it RED with all four signals:

    - fixture repo got NO .git of its own: writes were redirected
    - decoy core.bare changed: 'false' -> 'true'
    - decoy .git/config was MODIFIED by the fixture build
    - decoy object store grew: 0 -> 5 loose object(s)
    SELFTEST FAIL: fixture 'env-isolation' — fixture writes ESCAPED
    check-tree-size-push: ERROR — nothing was checked (exit 2)

Unsabotaged, under the same hostile environment: `PASS — 15 fixture(s) checked`,
stand-in repo untouched on every axis.

## Not done deliberately

- History was NOT rewritten; `30743ecd6749` keeps its wrong author. Force-push is
  forbidden here.
- No `git prune` / `git gc` on the shared repo — ~39 lanes have in-flight
  objects. The leak is stopped at the source; reclaiming the ~160,770 existing
  unreachable loose objects needs a quiet window and is left open.
- The guard leaked ~27 loose objects per invocation. That is a PROVED
  contributor to the unreachable-object count, but it is not proved to be the
  only one at the observed scale.
