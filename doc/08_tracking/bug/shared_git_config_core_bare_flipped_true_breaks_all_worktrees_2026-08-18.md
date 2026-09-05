# Shared `.git/config` had `core.bare = true` set, breaking `git status` in every worktree

- **Status:** REPAIRED 2026-08-18 09:56 UTC; ROOT CAUSE NOT ESTABLISHED
- **Date:** 2026-08-18
- **Area:** `/mnt/data/worktrees/simple-main/.git/config` (the SHARED config for
  simple-main and ~100 linked worktrees under `/mnt/data/worktrees/`)
- **Severity:** High while active — every lane on this repo loses `git status`,
  `git add`, and `git commit` simultaneously.

## What was observed

At 09:56:22 UTC, in `/mnt/data/worktrees/lane-rt-bitstream`:

```
$ git status --porcelain
fatal: this operation must be run in a work tree
$ git rev-parse --is-inside-work-tree
false
$ git config --get core.bare
true
$ grep -n bare /mnt/data/worktrees/simple-main/.git/config
10:     bare = true
```

`git log` still worked, which is what makes this confusing to diagnose: the
repository is readable, only working-tree operations fail.

The file's mtime was **09:52:54**, roughly two minutes after this session
launched four parallel subagents, and no such failure had occurred at any point
earlier in the session despite many `git status` calls.

This is a linked worktree: `.git` is a FILE pointing at
`/mnt/data/worktrees/simple-main/.git/worktrees/lane-rt-bitstream`. Every
worktree's `config.worktree` was inspected and all are byte-identical
(`core.sparseCheckout=true`, `core.sparseCheckoutCone=true`) — none of them
override `core.bare`, so a single `bare = true` in the shared config disables
working-tree operations for **all** of them at once. `simple-main` itself has a
populated working tree, so `bare = true` is simply wrong for it.

## Repair

```
git config --file /mnt/data/worktrees/simple-main/.git/config core.bare false
```

Verified afterwards: `git rev-parse --is-inside-work-tree` -> `true` in both
`lane-rt-bitstream` and `simple-main`; `git status --porcelain` works in both;
`simple-main` HEAD (`47411747677`) and this lane's HEAD (`7ab0e2997f1`)
unchanged. No commit, ref, or file content was touched — this was a config-only
repair.

## What is NOT established

**Attribution.** The timing points at one of this session's four concurrently
running subagents, but that is circumstantial, not proof: the config is shared
with every other lane and any process on this machine could have written it.
No agent was instructed to touch git config, and none reported doing so.

**A clean before-image.** The backup taken during the repair
(`scratchpad/git-config.bak`) reads `bare = false`, i.e. it captured
post-repair state rather than pre-repair — so it cannot serve as evidence of
what the file looked like when broken. The only pre-repair evidence is the
`grep`/`git config --get` output quoted above. Recorded here rather than
quietly omitted, because it is exactly the kind of gap that makes a later
recurrence hard to diagnose.

## Why it matters beyond the immediate fix

Any agent, in any lane, can write the shared config and instantly break every
other lane's ability to commit. There is no guard for this. The existing
pre-push guards all check tree CONTENT (conflict trees, marker text, tree size,
symbol sets, compilability) — none of them looks at repository configuration,
and none would fire here because nothing was ever pushed.

Suggested follow-up, not done here:

- Treat `core.bare` on a repo with linked worktrees as an invariant, and check
  it in the same family as `watch-origin-tree-health.shs` (a standalone
  watchdog, since this failure blocks the push path itself rather than
  travelling through it).
- Agent instructions in this repo should state explicitly that
  `/mnt/data/worktrees/simple-main/.git/` is shared state and must never be
  written, in the same way `bin/simple` is already called out as a shared
  binary that must not be rebuilt or replaced.

## CORRECTION 2026-08-19 — attribution above is WRONG

The "What is NOT established" section speculates that one of a session's
subagents wrote `core.bare = true`. That is incorrect and is corrected here.

**The push path itself does it.** Reproduced repeatedly: `core.bare` is `false`,
a `git push` is run, and immediately afterwards `core.bare` is `true` again.
This happened on every push attempt of the session — via `land.shs` and via
plain `git push` alike — with no subagent running at all.

Mechanism, already documented by this repo's own
`scripts/check/check-core-bare-sanity.shs`: a `git` invocation with `GIT_DIR`
set to a **relative** path, unable to infer an adjacent work tree, writes
`core.bare = true`. The pre-push hook runs guard scripts under exactly that
condition in a linked worktree.

**Consequence — the hook sabotages its own guards.** Once `core.bare` flips
mid-run, every subsequent guard sees no work tree and correctly fail-closes with
`ERROR — nothing was checked` (exit 2). Observed blocking, in sequence across
attempts: `check-no-conflict-markers-push`, `check-seed-builds-push`,
`check-runtime-api-regression-push`, `check-implicit-self-field-assignment`.
Every block was status 2 (ERROR / environmental), never status 1 (FAIL /
content). The guards are behaving correctly; the environment they run in is
corrupted by the push that invoked them.

This makes `git push` effectively impossible from a linked worktree without
either resetting `core.bare` between guards or bypassing the hook — which is a
far more serious finding than a stray agent write, because it blocks every lane
that works from a worktree rather than the primary clone.
