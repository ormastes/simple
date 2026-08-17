# `core.worktree` in the shared `.git/config` silently disables ALL THREE pre-push guards

- **Filed:** 2026-08-08
- **Severity:** Critical — the repo's only automated protection against a `main`
  tree wipe is currently **off for every lane**, and fails in a way that looks
  like a tooling hiccup rather than a disabled gate.
- Status: FIXED
- Status re-verified 2026-08-17 by source inspection (triage shard 00).
  repaired here*).

## Symptom

Run any pre-push guard from the repo root:

```
$ sh scripts/check/check-tree-size-push.shs origin/main..<sha>
  This script lives in the git repo at: /home/ormastes/dev/pub/simple
  but cwd resolves to the git repo at:  /tmp/simple-stage4-codex.QM6dqU
  Refusing to report on a different repository than the one being guarded.
check-tree-size-push: ERROR — nothing was checked (exit 2)
```

All three guards do this:
`check-no-conflict-tree-push.shs`, `check-no-conflict-markers-push.shs`,
`check-tree-size-push.shs`.

Per `.claude/rules/vcs.md`, `ERROR — nothing was checked` (exit 2) is **not a
pass** — but it is easy to read as an environment quirk and push anyway. The
guards are fail-closed, which is correct; the problem is that they are
*permanently* closed, so the safe behaviour is indistinguishable from a broken
script and invites being ignored.

## Cause

`/home/ormastes/dev/pub/simple/.git/config` contains:

```
[core]
    worktree = /tmp/simple-stage4-codex.QM6dqU
```

set by some `stage4-codex` lane (the temp dir was created 2026-08-08 05:02 and
still exists). `.git` itself is a normal directory; the redirection is purely
this config key.

Consequence — from the repo root:

```
$ pwd -P
/home/ormastes/dev/pub/simple
$ git rev-parse --show-toplevel
/tmp/simple-stage4-codex.QM6dqU        # <-- not where you are
```

The guards compare their own script location against
`git rev-parse --show-toplevel` and correctly refuse. But this affects **every**
git command in the repo, not just the guards.

`core.worktree` is set in the **shared** config, so it also poisons every linked
`git worktree` created from this repo. A freshly created
`git worktree add` checkout reports the same `/tmp/...` toplevel — so "run it
from a clean worktree" does **not** work around it.

## Why this is likely also today's "silent WC reverts"

Multiple lanes today reported working-copy files being silently reverted to
their `origin/main` content by an unidentified parallel session. This config is
a strong candidate mechanism: with `core.worktree` pointed at `/tmp/...`, any
`git checkout -- <path>`, `git restore`, `git stash`, or `git reset --hard` run
from `/home/ormastes/dev/pub/simple` operates against a **different working
tree** than the operator believes.

Observed directly in this lane: two edits to
`src/compiler_rust/compiler/src/{memory_guard.rs,interpreter_module/module_loader.rs}`
were reverted to byte-identical `origin/main` blobs while this config was in
place. Both files compared exactly equal to `git rev-parse origin/main:<path>`
afterwards — a clean revert, not a competing edit. This is consistent with, but
does not by itself prove, the `core.worktree` mechanism.

## One-command detector

```bash
[ "$(git rev-parse --show-toplevel)" = "$(pwd -P)" ] || echo "BROKEN: core.worktree redirect"
```

Worth adding to the guards themselves as a named, self-explaining failure
("`core.worktree` is set; the guards cannot run") instead of the current generic
repository-mismatch message, which does not name the cause or the fix.

## Workaround (proven — restores all three guards)

Override the config with the environment, which takes precedence over
`core.worktree`:

```bash
export GIT_DIR=/home/ormastes/dev/pub/simple/.git
export GIT_WORK_TREE=/home/ormastes/dev/pub/simple
sh scripts/check/check-no-conflict-tree-push.shs   origin/main..<sha>
sh scripts/check/check-no-conflict-markers-push.shs origin/main..<sha>
sh scripts/check/check-tree-size-push.shs           origin/main..<sha>
```

Verified 2026-08-08: with these two variables set, all three report
`PASS — 1 commit(s) checked ...` (and `check-tree-size-push` runs its
`selftest 16/16 fixtures correct` first). Without them, all three report
`ERROR — nothing was checked`.

## Repair

```bash
git config --unset core.worktree
```

`core.worktree` is explicitly unsupported by git in a repository that has linked
worktrees, and this repo has many (`git worktree list` shows 5+). Setting it in
the shared config to serve one lane's private temp checkout is the defect.

## Why not repaired here

Not run unilaterally: a `stage4-codex` lane may be mid-flight against
`/tmp/simple-stage4-codex.QM6dqU`, and unsetting the key changes what every one
of its git commands resolves to. That is the same class of cross-lane clobber
this doc is about. **Someone with visibility into that lane should run the
unset**; until then the `GIT_WORK_TREE` workaround above is mandatory before
every push.

## Related

- `.claude/rules/vcs.md` § Pre-push guards — the guards, their verdict lines,
  and the two occasions `main` was wiped to near-zero files in 24 hours with
  every other check green. `check-tree-size-push.shs` was the only thing that
  ever caught that class of corruption, and it is the gate currently disabled.
- `doc/08_tracking/bug/no_automated_tree_size_gate_2026-08-01.md`
- `doc/08_tracking/bug/pre_push_guards_fail_open_on_cwd_2026-08-01.md` — the
  guards were hardened to fail *closed* on cwd; this is the first observed case
  of that hardening firing repo-wide and permanently.

## Unrelated observation, same file family

`src/compiler_rust/compiler/src/interpreter_module/module_loader.rs` at
`origin/main` carries a live marker:

```
// SABOTAGE-TEMP: reverted to prove the FP guard goes RED. RESTORE.
```

It is present in `origin/main` (not introduced by this lane) and says RESTORE.
Whichever lane left it should restore it or delete it.
