# Shared `.git/config` `core.worktree` + `core.bare` misdirected every path-anchored guard (2026-08-08)

Status: FIXED (local repo state only — nothing landable in git except this record)

## Symptom

A legitimate push was blocked by the pre-push hook:

```
check-jit-closure-blockers: ERROR — nothing was checked (selftest failed: 8)
```

The guard's 8 fixtures under `test/fixtures/repro/compiler/jit_closure/` were
absent from the tree it scanned, even though they are present on `origin/main`
and in the real checkout. A parallel session "fixed" it by copying the fixtures
into `/tmp/simple-stage4-codex.QM6dqU` — a symptom fix that would have to be
repeated forever.

By the time this was investigated the damage had escalated: **every** git
operation in **every** worktree failed:

```
$ git rev-parse --show-toplevel
warning: core.bare and core.worktree do not make sense
fatal: this operation must be run in a work tree

$ git -C /tmp/simple-stage4-codex.QM6dqU status
fatal: unable to set up work tree using invalid config
```

The 100+ linked worktrees were all unusable, not just the main checkout.

## Root cause

The **shared** `.git/config` of the main checkout (`file:.git/config`, confirmed
via `git config --show-origin`) had acquired two mutually contradictory
`[core]` keys:

```
[core]
	bare = true
	worktree = /tmp/simple-stage4-codex.QM6dqU
```

Neither belongs there:

- `/home/ormastes/dev/pub/simple` is a normal non-bare checkout: it has
  `.git/index` (14.9 MB), a full working tree, and `core.sparseCheckout`
  settings. `bare = true` is simply false.
- `/tmp/simple-stage4-codex.QM6dqU` is a **linked worktree**. It carries its own
  pointer pair and needs nothing in the main config:
  - `/tmp/simple-stage4-codex.QM6dqU/.git` (a file) →
    `gitdir: /home/ormastes/dev/pub/simple/.git/worktrees/simple-stage4-codex.QM6dqU`
  - `.git/worktrees/simple-stage4-codex.QM6dqU/gitdir` →
    `/tmp/simple-stage4-codex.QM6dqU/.git`
  - `.git/worktrees/simple-stage4-codex.QM6dqU/commondir` → `../..`

  A linked worktree resolves its root through that pair, never through the main
  repo's `core.worktree`.

`.git/config` mtime was `2026-08-08 07:13`, minutes before the investigation, so
both keys were written by a recent stray command (something along the lines of
`git config core.bare true` / a `--work-tree`-carrying `git config` write from a
script). They are **not** longstanding intentional configuration. Note the repo
uses `extensions.worktreeConfig = true`, but the bad keys were in the shared
`.git/config`, not in `.git/config.worktree` (which only holds sparse-checkout
settings), so they leaked to all worktrees.

Because git reads `core.bare` during repository discovery, `git -c
core.bare=false ...` on the command line does **not** repair it — a parallel
session was already burning cycles on
`git -c core.bare=false --work-tree=... status` workarounds.

## Blast radius — everything anchored on `git rev-parse --show-toplevel`

`.git/hooks/pre-push:50` computes `repo_root=$(git rev-parse --show-toplevel)`
and then invokes four guards from `$repo_root/scripts/check/`:

| line | guard |
|------|-------|
| 56 | `check-no-conflict-tree-push.shs` |
| 57 | `check-no-conflict-markers-push.shs` |
| 58 | `check-tree-size-push.shs` |
| 59 | `check-jit-closure-blockers.shs` |

All four were scanning the temp worktree (or, once `core.bare` landed, getting
an empty `repo_root` and hitting the hook's own fail-closed branch). The
tree-size guard is the one that gates against tree wipes, so this defect
directly degraded the repo's strongest integrity gate.

15 scripts anchor themselves the same way and were equally misdirected when run
from the main checkout:

```
scripts/check/check-tree-size-push.shs
scripts/check/check-no-conflict-tree-push.shs
scripts/check/check-no-conflict-markers-push.shs
scripts/check/pre-push-conflict-tree-guard.shs
scripts/check/check-guard-wiring.shs
scripts/check/check-dangling-references.shs
scripts/check/check-test-tree-divergence.shs
scripts/check/check-rendering-source-coupling.shs
scripts/check/check-render2d-coverage.shs
scripts/check/check-lexer-radix-literal-suffix.shs
scripts/check/check-nvme-rv32-minimal-live.shs
scripts/check/check-simpleos-wm-aqua-glyph-ovmf-evidence.shs
scripts/check/build-macos-es-history-collector.shs
scripts/check/lib/qemu-frozen-source-admission.shs
scripts/setup/setup.shs
```

Severity is not "one push was blocked". It is that guards can **silently pass**
against a tree nobody is pushing: a fail-closed guard like the jit-closure one
turns loud, but a guard whose findings depend on file *content* just reports
clean on the wrong files.

## Fix

Backup taken first: `/tmp/gitconfig_backup_1786288530.bak` (13254 bytes, exact
pre-change copy of `.git/config`).

```bash
git config --local --unset core.worktree
git config --local core.bare false
```

Observed result: git 2.43 did not keep a literal `bare = false` line — after the
write both `bare` and `worktree` are simply absent from the `[core]` section of
`.git/config`, and `git config --get core.bare` exits 1. Absent is the correct
state: a repository whose `.git` has a parent working tree defaults to non-bare,
which `git rev-parse --is-bare-repository` now confirms as `false`.

### Verification (after)

| check | result |
|-------|--------|
| `git rev-parse --show-toplevel` | `/home/ormastes/dev/pub/simple` |
| `git rev-parse --is-bare-repository` | `false` |
| `git worktree list` path set, before vs after | **identical, 108 entries** |
| `git -C /tmp/simple-stage4-codex.QM6dqU rev-parse --show-toplevel` | `/tmp/simple-stage4-codex.QM6dqU` |
| `git -C /tmp/simple-stage4-codex.QM6dqU status --porcelain` | works, 26 lines (was `fatal:`) |
| `sh scripts/check/check-jit-closure-blockers.shs` | `PASS — 615 file(s) scanned, 0 closure blockers` |

No worktree was removed, pruned, moved, or modified. The temp worktree is
strictly better off than before the change (it was fatally broken; it now
works).

## Detecting a recurrence

One line, from the real checkout — non-empty output means the repo is
misconfigured again:

```bash
[ "$(git rev-parse --show-toplevel 2>/dev/null)" = "$(pwd -P)" ] || echo "BROKEN: git toplevel is '$(git rev-parse --show-toplevel 2>&1)' not $(pwd -P)"
```

Or, checking the config directly:

```bash
git config --local --get core.worktree && echo "BROKEN: core.worktree set in shared .git/config"
```

Worth wiring into `.git/hooks/pre-push` ahead of the `repo_root=` line, and into
`scripts/check/check-guard-wiring.shs`, so a mis-anchored guard run is refused
rather than trusted. Filed as follow-up; not done in this change, which was kept
to the minimum provably-safe repair.
