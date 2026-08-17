# `core.bare = true` appears spontaneously on the shared `.git/config`, blocking every lane

**Filed** 2026-08-17. **Status** MITIGATED (self-healing in the pre-push hook);
**root cause OPEN** — the writer is unidentified.

## Symptom

`/mnt/data/worktrees/simple-main/.git/config` acquires `bare = true` while the
repo plainly has a working tree and ~150 linked worktrees. Observed twice in one
session: corrected to `false`, and found back at `true` within minutes.

While it is set:

- `git rebase` fails with `fatal: this operation must be run in a work tree`
- `git rev-parse --show-toplevel` fails
- the pre-push hook aborts before any guard runs:
  `pre-push: a stray core.bare in .git/config misdirects every guard — refusing to push blind`

So a single stray line blocks **every** push and rebase on the host, for every
lane, with an error that does not name the cause.

## What is NOT the cause

- Nothing in the repo writes it: `grep -rn 'core\.bare\|core_bare' scripts/ src/ tools/ .claude/` returns zero hits.
- Not jj colocation in this tree: there is no `.jj` directory at
  `/mnt/data/worktrees/simple-main` (jj 0.32.0 is installed and is the project's
  primary VCS, so a jj path elsewhere is still a candidate).
- Not a stray *global* setting: `~/.gitconfig` has no `bare` entry. (One was
  briefly introduced by this session's own retry loop and has been removed —
  `core.bare` is a per-repo property and must never be global, since it would
  break every genuinely bare repo on the account.)

A 10-minute polling watcher did not catch a flip, so it is intermittent rather
than periodic.

## Mitigation (landed)

`scripts/check/pre-push-conflict-tree-guard.shs` now self-heals before the bare
check, but ONLY on a provable contradiction: the common git dir basename is
`.git` AND its parent holds a checked-out tree (`$parent/.git/HEAD` exists). A
genuinely bare repository — config at `foo.git/` or at the repo root — fails
that test and is left untouched, so the repair cannot corrupt a real bare repo.

Verified with two fixtures, both directions:

| fixture | before | after |
|---|---|---|
| non-bare repo poisoned with `core.bare=true` | `is-bare=true`, `show-toplevel` fails | `REPAIRED`, `is-bare=false`, rebase-capable |
| `git init --bare` repo | `is-bare=true` | untouched, `core.bare` still `true` |

## Known limit

The self-heal runs at **push** time. A `git rebase` issued while the flag is
flipped still fails until something triggers the repair. The durable fix is to
find the writer — candidates worth checking are jj/`sj` invocations from other
worktrees, and any tooling that runs `git config` against this repo's
`.git` from outside it.
