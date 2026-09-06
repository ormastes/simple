# Fourth tree wipe (`6f86ff32a7d`) — every guard was sound, none was invoked

- **Date:** 2026-08-11
- **Severity:** BLOCKER (repo integrity; whole-tree loss)
- Status: FIXED
- Status re-verified 2026-08-17 by source inspection (triage shard 01).
- **Wipe number:** 4 (prior: 2026-08-01 ENOSPC, 2026-08-01 API `base_tree`, `2313821fd77` stale-WC revert)

## What happened

Commit `6f86ff32a7d` "docs(todo): track remaining Stage 4 gates" pushed a tree of
**3 files**, wiping **113,027** tracked files including all of `src/`.

| commit | tracked files |
|---|---|
| `a2a33b4592c` (parent, healthy) | 113,030 |
| `6f86ff32a7d` (wipe) | **3** |

Repaired by a fast-forward restore commit built from the parent tree plus the 3
legitimate doc files (verified live: 113,030 files, `src` = 16 entries,
`src/runtime` = 210). Origin has since advanced to `276c61ed464`
(113,034 files, `src` = 16, `src/runtime` = 210) — healthy.

## The guards were NOT defective

`.claude/rules/vcs.md` documents an absolute floor of 90,000 files in
`check-tree-size-push.shs`, "the only check that fires when the BASE is itself
already wiped". 113,030 → 3 is four orders of magnitude below it. The obvious
hypothesis was a guard defect. **It is not.** Replayed against the real incident
range, verbatim last line of stdout:

```
$ sh scripts/check/check-tree-size-push.shs a2a33b4592c..6f86ff32a7d
check-tree-size-push: FAIL — 1 commit(s) checked in a2a33b4592c..6f86ff32a7d, 1 structurally wrong
EXIT=1
```

The two newest guards were checked for vacuous-PASS on a 3-file tree — a wipe
must never read as "no compiler changes in range, PASS". Neither does:

```
check-seed-builds-push: FAIL — cargo check failed in 6f86ff32a7d: see stderr above          (exit 1)
check-runtime-api-regression-push: FAIL — 2675 symbol(s) checked in a2a33b4592c..6f86ff32a7d,
  2675 symbol(s) removed: rt_actor_death_reason rt_actor_id ...                             (exit 1)
```

All three content guards correctly reject the wipe. The wipe landed anyway
because **nothing invoked them**.

## Bypass mechanism: two independent, silent, fail-OPEN wiring defects

### Defect 1 — `core.hooksPath` pointed at a deleted temp directory

```
$ git config --show-origin --get core.hooksPath
file:.git/config        /tmp/simple-stage4-push.85KIAn/.git-hooks
$ ls -la /tmp/simple-stage4-push.85KIAn/.git-hooks/
ls: cannot access ...: No such file or directory
```

A leftover from some earlier stage-4 push scratch dir. When `core.hooksPath`
points at a missing directory git **does not warn** — it runs no hooks at all,
and `.git/hooks/pre-push` (a correct symlink to
`scripts/check/pre-push-conflict-tree-guard.shs`) is bypassed entirely.

### Defect 2 — the hook target was not executable

Even with `hooksPath` corrected, the push still ran no guards. Git's only signal
is a hint buried in push output, and it proceeds:

```
hint: The '.git/hooks/pre-push' hook was ignored because it's not set as executable.
```

`scripts/check/pre-push-conflict-tree-guard.shs` was mode `0664`. File mode is
tracked by git, so this defect was shared by every clone.

Either defect alone silently downgrades **every** guard in the repo to advisory.
Neither is visible in `git status`, in any guard verdict, or in a normal push.

## Plumbing pushes do NOT bypass hooks

The leading hypothesis was that `git push <sha>:refs/heads/main` — how every
agent in this session lands — skips hooks for a raw SHA. **It does not.**
Measured against a local bare repo after fixing both defects: the push hung for
10 minutes running the guard battery, then blocked. Partial transcript:

```
check-tree-size-push: selftest 16/16 fixtures correct (12 must-fail, 3 must-pass, 1 env-isolation)
pre-push: BLOCKED by check-tree-size-push.shs (status 2) for range new ref 6f86ff32a7d... (not on origin)
pre-push: BLOCKED by check-no-conflict-tree-push.shs (status 2) ...
```

The wiped commit was rejected. Plumbing SHA pushes are fully hook-covered; the
repo-wide advisory-only concern is **not** confirmed. The blast radius is the
two wiring defects, which are now fixed and fenced.

(Note the guards report ERROR exit 2 rather than FAIL here, because
`<sha> --not --remotes=origin` resolves to 0 commits for a ref with no shared
origin history. The non-vacuity rule converts that to a block, which is the
correct outcome — but it means the *reason* printed is "nothing was checked",
not "tree too small". Both block the push.)

## Root-cause summary

A guard that is never **invoked** cannot report that it was never invoked. The
repo had ~40 content guards and **zero** checks on the wiring that runs them.
Every wipe post-mortem so far has hardened content checking; none had hardened
invocation.

## Mitigation landed

**Chosen: a wiring guard.** Evaluated three options:

| option | verdict |
|---|---|
| (a) `pre-push-all.shs` aggregator | Rejected — redundant. Measured above, plumbing pushes DO run the hook; the driver already sequences every guard. The gap was never "no aggregator", it was "the aggregator wasn't reachable". |
| (b) GitHub branch protection / required check | Rejected as primary — GitHub cannot express "tree must have ≥90,000 files". Required status checks gate PR merges, not direct pushes to `main`, and this repo lands by direct push by design. Would not have stopped this. |
| (c) post-push watchdog + auto-restore | Rejected for now — heaviest option, and *reactive*: it repairs after `main` is already wiped and every puller has a broken clone. Worth revisiting as defence in depth, but it does not close the hole. |

Implemented:

1. **`scripts/check/check-hook-installation.shs`** (new) — fences the wiring, not
   the content. 10 checks: `core.hooksPath` unset or pointing at a real directory
   containing a `pre-push` hook (and *not* at volatile `/tmp`, `/run`,
   `/dev/shm` storage, which is exactly how defect 1 arose); hook exists; hook is
   **executable**; hook resolves to the repo guard driver or at least invokes
   `check-tree-size-push`; driver executable; the four mandatory content guards
   present; `core.verify` not `false`. Same verdict convention as the other
   guards — `PASS — <n> check(s) performed` / `FAIL` exit 1 / `ERROR — nothing
   was checked` exit 2, with 0 checks an ERROR. No object walks, so it is fast
   enough that there is no incentive to skip it.

   Verified against both real defects replayed as fixtures:

   ```
   healthy:              PASS — 10 check(s) performed, hook wiring intact         (exit 0)
   defect 1 replayed:    FAIL — 10 check(s) performed, 1 defect(s) in hook wiring (exit 1)
   defect 2 replayed:    FAIL — 10 check(s) performed, 2 defect(s) in hook wiring (exit 1)
   restored:             PASS — 10 check(s) performed, hook wiring intact         (exit 0)
   ```

2. **Wired into `pre-push-conflict-tree-guard.shs`** as the first check, run
   unconditionally before any range is derived; a missing wiring guard is itself
   a block.

3. **`chmod +x scripts/check/pre-push-conflict-tree-guard.shs`** — the mode is
   tracked, so this repairs defect 2 for every clone on pull.

4. `git config --unset core.hooksPath` — repairs defect 1 in this working copy.
   Not tracked (it is local config), which is precisely why check 1 exists.

## Follow-ups (not done here)

- Several content guards are still mode `0664`
  (`check-no-conflict-tree-push.shs`, `check-no-new-symlinks-push.shs`,
  `check-c-runtime-compiles-push.shs`). The driver invokes them via `sh <path>`
  so they work today, but a human running one directly gets permission denied.
- Option (c), the post-push watchdog, remains an open defence-in-depth item
  given four wipes to date.
- `setup.shs` installs the hook symlink but never asserts `core.hooksPath` is
  clean; it should call the new guard at the end.
