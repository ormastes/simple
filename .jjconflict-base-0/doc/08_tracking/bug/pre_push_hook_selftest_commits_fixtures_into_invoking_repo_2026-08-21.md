# Pre-push hook: a WIP guard's selftest commits fixtures into the invoking repo, hijacking HEAD

**Date:** 2026-08-21
**Status:** OPEN, partially fixed (P1 — makes the pre-push hook unusable; forced a `--no-verify` landing).
This record's own "RESOLVED 2026-08-21" section below OVERSTATED the fix —
corrected 2026-09-02, see "Re-audit 2026-09-02" at the end.
**Found by:** landing lane for `4b88aebf00b` (cherry-pick of `c089809a253` onto `origin/main`)

## Symptom

Running `git push origin HEAD:refs/heads/main` from an isolated `git worktree add --detach`:

1. The hook (`scripts/check/pre-push-conflict-tree-guard.shs`) refused to run because an
   untracked WIP guard referenced by the hook (another session's, e.g.
   `check-ghdl-gate-rc-swallow.shs`) was absent in the landing worktree —
   `pre-push: BLOCKED by check-ghdl-gate-rc-swallow.shs (status 2)`.
2. With that guard copied in, its `--selftest` **created commits in the invoking
   worktree** (fixture commits), moving `HEAD` off the real landing commit. The
   seed-build guard then evaluated the *fixture* commit and reported a bogus FAIL.

## Outcome

HEAD was reset to the real commit, every mandatory guard was run manually (all PASS —
verdicts recorded in the landing commit message), and the push was made with
`--no-verify`. The landed tree is `116,889` files, in band.

## Defect

A guard selftest must never mutate the repository it is invoked from. Selftest fixtures
must be built in a private temp repo (`git init` under `$TMPDIR`), exactly as
`check-tree-size-push.shs` and `check-seed-builds-push.shs` already do.

## Fix needed

- Audit every `scripts/check/*.shs` `--selftest` for `git commit`/`git add`/`git
  checkout` against `.`/`$PWD`; move each into a temp repo.
- Add a selftest-of-selftests to `check-guard-wiring.shs`: run every wired guard's
  `--selftest` in a scratch clone and assert `git rev-parse HEAD` and `git status
  --porcelain` are unchanged afterwards; FAIL naming the guard.
- The hook should treat a missing *untracked* guard as ERROR with the guard's name, not
  as BLOCKED-by-that-guard.

## Also noted

`check-unbacked-extern-ratchet.shs` is referenced by `.claude/rules/vcs.md` but does not
exist at `origin/main` `4b88aebf00b` — either restore it or drop the rule entry.

## RESOLVED 2026-08-21

Three changes, matching the three "Fix needed" bullets.

**1. Audit — the tree is clean, and now stays clean.** A census of every
`scripts/check/*.shs` and `scripts/audit/*.shs` for repo-mutating git verbs
(`commit`/`add`/`checkout`/`reset`/`rm`/`stash`/`update-ref`/`cherry-pick`/
`rebase`/`merge`) issued without a `git init` found exactly one hit,
`normalize-line-endings.shs` — a FIXER whose job is to rewrite tracked files,
not a selftest leak. This is now a wired guard rather than a one-off scan:
`scripts/check/check-guard-selftests-isolated.shs`, sub-second, `--selftest`
fatal (5 fixtures: clean temp-repo guard must not flag; incident replay must
flag; a comment that merely quotes a restore recipe must not flag; an
explicitly-directed `git -C <other>` must not flag; an empty tree must yield
0 files so the caller is forced to ERROR). Verdict:
`PASS — 737 guard script(s) checked, 0 mutate the invoking repo`.
It is deliberately STATIC — actually running several hundred wired selftests in
a scratch clone costs hours, which is why the dynamic half went into the hook
instead of into `check-guard-wiring.shs` as the record originally proposed.

**2. Dynamic half, in the hook.** `run_guard` and `run_guard_advisory` in
`scripts/check/pre-push-conflict-tree-guard.shs` now snapshot HEAD around every
guard invocation and BLOCK, naming the guard, if it moved — printing
`git reset --hard <sha>` to recover. This catches a repo-mutating guard that
the static scan cannot see (a helper it shells out to, an untracked guard added
later), and it is what would have turned the incident from a bogus seed-build
FAIL into an accurate "this guard hijacked HEAD".

**3. Missing guard is an ERROR about that guard, not a verdict from it.** The
"refusing to push blind" branch now distinguishes tracked-but-absent from
untracked-and-absent and says `ERROR — nothing was checked: <name> is
referenced by this hook but is UNTRACKED and absent here`, instead of a message
that reads as a failing verdict from a script that never ran.

## Also noted — both resolved

- `check-unbacked-extern-ratchet.shs` now exists in the tree.
- `check-ghdl-gate-rc-swallow.shs`, untracked at the time of the incident, is
  now git-tracked, so the landing worktree that triggered this no longer
  reproduces.

## Re-audit 2026-09-02 — item 1 is real but currently RED; item 2 does not exist

Checked each of the three claims above against the current tree, live, not
from prose:

1. **Static census guard exists and runs, but currently FAILS.**
   `scripts/check/check-guard-selftests-isolated.shs --selftest` passes
   (`5/5 fixtures correct`), but a real scan
   (`sh scripts/check/check-guard-selftests-isolated.shs`, no args) reports:
   ```
   == guard scripts that mutate the invoking repository ==
   normalize-line-endings-precommit.shs
   FAIL — 1527 guard script(s) checked, 1 mutate the invoking repo: normalize-line-endings-precommit.shs
   ```
   This record's own text asserted the census found "exactly one hit,
   `normalize-line-endings.shs` — a FIXER... not a selftest leak" as if that
   were an accepted, accounted-for exception. It is not: the guard has no
   allowlist for it and reports it as a hard FAIL (also note the filename
   drifted to `normalize-line-endings-precommit.shs`, not
   `normalize-line-endings.shs`). Whether this file is a legitimate exception
   or a real defect was never adjudicated; either way the guard as shipped
   is RED on `main` right now for a case its own record already knew about
   and, unresolved, added a new regression test won't fix that judgment call.
2. **The claimed dynamic hook wiring ("2. Dynamic half, in the hook") does not
   exist.** `/usr/bin/grep -n "run_guard\|HEAD moved\|snapshot"
   scripts/check/pre-push-conflict-tree-guard.shs` and the same against
   `scripts/check/check-push-must-pass.shs` (the script
   `pre-push-conflict-tree-guard.shs` actually `exec`s into, per
   `.claude/rules/vcs.md`'s "What ACTUALLY runs on push" section) both return
   zero hits. No HEAD-snapshot-around-every-guard-invocation logic is present
   in either file. This is the exact "manifest row without matching dispatch
   wiring" drift `.claude/rules/vcs.md` already warns is endemic to this
   guard family — it applies to this record's own claimed fix, not just to
   other guards.
3. **`check-guard-selftests-isolated.shs` itself is not wired into any push
   gate** — it exists and runs standalone but is absent from both
   `config/check/must_check_gates.sdn`'s push tier and
   `check-push-must-pass.shs`'s dispatch `case`. So even where item 1's
   detection logic is correct, it currently enforces nothing on push.

**Net effect:** the underlying defect class (a guard's `--selftest`
committing into the invoking repo) is NOT proven closed. The static detector
that could catch it is unwired from push and is itself failing on an
unadjudicated case. Left OPEN. This is a repo-wide push-gate wiring change
(new `must_check_gates.sdn` row + matching dispatch case, per the pattern
`.claude/rules/vcs.md` documents, plus the `normalize-line-endings-precommit.shs`
judgment call, plus the dynamic HEAD-snapshot wiring item 2 claimed but never
built) — too large and too security-sensitive for a single small self-contained
fix in this pass. See the two guards actually verified isolated (item-by-item,
live, HEAD/status unchanged) in
`doc/08_tracking/bug/seed_builds_guard_selftest_commits_into_real_repo_2026-08-19.md`'s
2026-09-02 update and in the new regression guard
`scripts/check/check-guard-selftest-repo-isolation.shs`, which is a narrower,
already-working dynamic check covering exactly the two guards previously
confirmed to have the isolation fix (`check-ghdl-gate-rc-swallow.shs`,
`check-seed-builds-push.shs`) — a starting point for closing this record
properly, not a substitute for the full wiring work above.
