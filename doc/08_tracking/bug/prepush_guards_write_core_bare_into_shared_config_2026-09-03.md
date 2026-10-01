# The pre-push guards were writing `core.bare` into the shared `.git/config` (2026-09-03)

Status: FIXED (`scripts/hooks/pre-push-worktree-launcher`)

Closes the open question in
`shared_git_config_core_worktree_misdirects_prepush_guards_2026-08-08.md` and in
the header of `scripts/check/check-core-bare-sanity.shs`, both of which record
the damage and neither of which names the writer.

## Symptom

`git push` from a linked worktree aborted part-way through the mandatory gate
list:

```
check-guard-wiring: ERROR — nothing was checked: not inside a git repository.
push-must-check: BLOCKING gate push-guard-wiring failed (exit 2)
```

`git config --unset-all core.bare` fixed it. The next push put it back. Repeat.
Because the key reappeared "on its own", it looked like a background writer —
another agent session, or jj. It is neither.

## Root cause

Git runs a hook with `GIT_DIR` exported, and chdirs to the working-tree root
first. **Nothing in this repo's hook chain cleared it.** `grep -n 'GIT_DIR'` over
`scripts/hooks/pre-push-worktree-launcher`, `scripts/hooks/pre-push`,
`scripts/check/pre-push-conflict-tree-guard.shs` and
`scripts/check/check-push-must-pass.shs` returned nothing at all.

From a LINKED worktree the inherited `GIT_DIR` is
`<main>/.git/worktrees/<name>` — a gitdir with **no adjacent working tree**. So
for every guard in the chain:

- `git rev-parse --show-toplevel` fails with *"this operation must be run in a
  work tree"*, and `--is-inside-work-tree` is false. That is the
  `check-guard-wiring` abort above, on a completely healthy repository.
- a git command that (re)initialises config from that gitdir **writes
  `core.bare` into the SHARED config**, which every worktree then reads.

## Reproduction (measured, this host, git 2.50.1 Apple Git-155)

```
$ git config --unset-all core.bare
$ git config --get core.bare
                                   # '' — key absent
$ GIT_DIR=/Users/ormastes/simple/.git/worktrees/cleanup-wt \
    sh scripts/check/check-guard-wiring.shs --selftest-only
$ git config --get core.bare
false                              # the key was WRITTEN
```

The value here is `false`; when git cannot infer any adjacent work tree it writes
`true`, which is the destructive form the 2026-08-08 record describes.

**So the guards corrupted the config on every push, and then refused on the next
push because of the corruption they had caused.**

## Retired hypothesis

`check-core-bare-sanity.shs` proves a trailing-slash `GIT_DIR`
(`<repo>/.git/` or `<repo>/.git/.`) flips `core.bare` on git 2.43.0. Its own
selftest reports that this does **not** reproduce on git 2.50.1 (Apple
Git-155) — `'ok-nonbare' -> 'ok-nonbare'`. The inherited-GIT_DIR-in-a-hook path
above reproduces here with a plain absolute `GIT_DIR`, no trailing slash. Both
are the same family (an inherited `GIT_DIR` changing what a git command means);
only the second explains today.

## Fix

`unset GIT_DIR GIT_WORK_TREE GIT_INDEX_FILE GIT_PREFIX` at the top of
`scripts/hooks/pre-push-worktree-launcher`, before it resolves anything. Git has
already chdir'd to the working-tree root, so each guard resolves the repo from
cwd — which is what all of them already assume. One edit covers the whole chain.

Two related fixes landed with it:

- `scripts/check/check-core-bare-sanity.shs` existed for exactly this failure and
  was wired to **nothing** (line 83 of
  `scripts/check/guard_wiring_unwired_baseline.txt`). It is now called from
  `check-hook-installation.shs`, which the pre-push dispatcher runs first.
- That call must itself clear `GIT_DIR`: the sanity guard's selftest builds
  throwaway repos, and an inherited `GIT_DIR` makes its "non-repository
  directory" fixture resolve as a repo, so it reports
  `FAIL — guard selftest did not pass` on a healthy config.

## Not fixed here

Guards that resolve their root with `--show-toplevel` are still individually
fragile if ever invoked with `GIT_DIR` set by some other path. Eight push-tier
guards do this; seven tolerate an empty result. They are deliberately left alone:
the correct place to clear the environment is the entry point, and adding
per-guard fallbacks turns fail-closed refusals into fail-open ones (attempted and
reverted in this branch — see the revert commit).
