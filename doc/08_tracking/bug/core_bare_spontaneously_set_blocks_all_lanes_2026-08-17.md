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

## Investigation 2026-08-17 — ruled out BY TEST, not by reading

Each of these was executed against a throwaway fixture repo, not assumed:

| hypothesis | test | result |
|---|---|---|
| `jj git init --git-repo=<repo>` marks the backing repo bare | ran it against a fresh non-bare repo | `core.bare` stayed `false` — **ruled out** |
| routine jj ops flip it | `jj status`, `jj git export`, `jj git import`, `jj log -r @` | all left `false` — **ruled out** |
| `git sparse-checkout init` (which enables `extensions.worktreeConfig`) writes it | fresh repo + worktree + `sparse-checkout init --cone` | `bare` stayed `false`, extension enabled — **ruled out** |
| jj colocation in this tree | `ls .jj` | absent — **ruled out** |
| repo tooling sets it | `grep -rn 'core\.bare' scripts/ src/ tools/ .claude/` | zero hits (only vendored VS Code completion data elsewhere) — **ruled out** |
| a stray global setting | `~/.gitconfig` | no `bare` entry — **ruled out** |
| shell history | `.bash_history`, `.zsh_history` | no hits — **ruled out** |

### Relevant discovery

`extensions.worktreeConfig = true` IS enabled on this repo (389 of 401
worktrees carry a `config.worktree`, all from sparse-checkout). This matters:
with that extension, git treats `core.bare` as a **per-worktree** setting and
its `init_worktree_config()` path will MOVE an existing `core.bare = true` out
of `.git/config` into a `config.worktree`. That explains how the value can
appear to migrate between files, but it does not create a `true` — git only
relocates one that already exists.

### Leading hypothesis (not yet proven)

An **interrupted operation** that sets `core.bare true`, does work, and restores
`false` — killed before the restore. Two facts support it: earlyoom is actively
SIGTERM-killing processes on this host (`-r 3600 --prefer ^(simple|rustc|...)`),
and this exact failure mode was reproduced *accidentally* during this
investigation — a `pkill -f` pattern matched its own shell and killed it midway
between `git config core.bare true` and the restoring `git config core.bare
false`, leaving the flag stranded exactly as observed in the wild.

### Detector armed

A polling detector is running (50 ms, rolling `ps` buffer of git/jj/sj
processes, dumped on any change to the `bare = true` count). **Self-tested in
both directions and confirmed to fire.** Known limit, stated rather than
assumed: at 50 ms it will NOT attribute a ~5 ms `git config` invocation — it
missed the self-test's own writer — so it reliably DETECTS a flip and only
attributes a longer-running writer. Anyone continuing this should reach for
root-level `fanotify`/`auditd` on `.git/config`, which is the only thing that
attributes a write that fast; `ptrace`-based attach is blocked on this host
(`ptrace_scope=1`).

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
