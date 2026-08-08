# BUG: the two pre-push guards failed open — three distinct ways

- **Date:** 2026-08-01
- **Severity:** critical — these are the last line of defence against a
  truncated-tree wipe of `main`, which has happened twice in 24 hours
- **Files:**
  - `scripts/check/check-no-conflict-tree-push.shs`
  - `scripts/check/check-no-conflict-markers-push.shs`
  - `scripts/check/pre-push-conflict-tree-guard.shs` (the git pre-push hook)
- **Status:** FIXED (all three), with fixture-based non-vacuity proofs below
- **Base for all evidence:** origin `main` = `ceee960ca8e0b142033b1908f9879a67e3677daf`

## Summary

All three scripts reported **success without checking anything** under
conditions that occur in the normal landing workflow. Each failure mode
produced output that reads like a legitimate clean result.

| # | Defect | Old behaviour | New behaviour |
|---|--------|---------------|---------------|
| 1 | cwd fail-open | `nothing to push` + **exit 0** from any non-repo cwd | `ERROR` + **exit 2** |
| 2 | filename word-splitting | a marker file whose name contains a **space** was silently skipped — **exit 0 from the repo root** | detected, **exit 1** |
| 3 | hook negated its own range | new-ref push walked **0 commits** → `nothing to push` → **exit 0** | walks the real set, **exit 1** |

## Defect 1 — cwd fail-open (PROVED)

Every `git` call was written `git ... 2>/dev/null` with its exit status
discarded. Outside a git repository they all failed into empty strings,
`revs` came out empty, and both scripts took the "nothing to push" branch:

```
cwd                                    output                          exit
-------------------------------------- ------------------------------- ----
/run/user/1000/.../repo (repo root)    ... OK — no conflict trees ...   0
/run/user/1000/.../archived_wt         ... nothing to push in <range>   0
/ (non-repo)                           ... nothing to push in <range>   0
```

**Why this is acute:** the standard landing workflow has every agent build in
an isolated `/dev/shm` or `/run/user/1000` worktree created by `git archive` —
a tree with **no `.git`**. Running the guards from there is the natural thing
to do and silently voids them.

**Non-vacuity proof.** Fixture commit `ee6ac5c6683f5f8b0a158da5a1dd54d5f5fd65d6`
is a real jj conflict tree — `git ls-tree --name-only` on it returns exactly
`.jjconflict-base-0 .jjconflict-side-0 .jjconflict-side-1`. Against the range
`ceee960ca8e..ee6ac5c6683`:

- old guard, cwd = repo root ......... exit **1** (correct)
- old guard, cwd = archived worktree .. exit **0** — a clean PASS on a commit
  that would have wiped `main`

Same result for the markers guard with fixture `432498ffa918276d6b59da03b8604623bc08dc5c`
(a file containing a matched `<<<<<<< conflict 1 of 1` / `>>>>>>> conflict 1 of 1 ends` pair).

## Defect 2 — filename word-splitting (PROVED, previously unknown)

The markers guard collected paths into one string and iterated
`for f in $changed_paths`. Word-splitting broke any path containing a **space**
into fragments; each fragment's `git show` failed, and the loop body was
`content=$(git show "$tip:$f" 2>/dev/null) || continue` — a **silent skip**.

Fixture commit `1071e9630ca0286204ac167ed3c37af039dad20c` adds
`scripts/check/FIXTURE marked space.txt` with a matched marker pair. The old
guard, run **from the repo root** with a correct range, exited **0**.

This one needed no unusual cwd. It was a live miss in the intended
configuration.

Fixed by reading `git diff --name-status --no-renames` line-by-line (path = rest
of line after the tab, so spaces survive), `-c core.quotePath=false` so non-ASCII
names are not octal-escaped, and turning an unreadable **non-deleted** path into
a hard ERROR instead of a skip.

## Defect 3 — the pre-push hook negated its own range (PROVED)

For a brand-new ref the hook built:

    range="--not --remotes=origin $local_sha"

`$local_sha` lands **after** `--not`, so `git rev-list` **excludes** it:

    git rev-list --not --remotes=origin <sha>   ->      0 commits
    git rev-list <sha> --not --remotes=origin   ->  23850 commits

Zero commits then hit the old "nothing to push → exit 0" branch. Verified: the
old guard exited **0** on `--not --remotes=origin ee6ac5c6683...`, a range whose
only commit is the conflict-tree fixture. **Every new-ref push was waved through
completely unchecked.**

Fixed by putting the positive rev first and passing it through an explicit
`--rev-list-args` flag.

## Full enumerated family (audit)

Fixed:

1. `git rev-list` status discarded → empty → pass. (both guards)
2. `git ls-tree | grep -q` — pipeline status is `grep`'s, so an `ls-tree`
   failure read as "no conflict entries". (tree guard)
3. `git diff --name-only` status discarded → empty path list → `found=0` → pass.
   (markers guard)
4. `git show ... || continue` — unreadable path silently skipped. (markers guard)
5. `for f in $changed_paths` — word-splitting and glob expansion on paths.
   (markers guard) — **defect 2**
6. Explicit non-empty range resolving to 0 commits reported as a pass.
   (both guards)
7. No check that cwd is inside a git repository. (both guards) — **defect 1**
8. No check that the range endpoints exist as commits in *this* clone; a stale
   or wrong clone silently produced an empty range.
9. A bare rev (no `..`) was accepted: for the tree guard it means "all history";
   for the markers guard `git diff <rev>` compares against the **working tree**.
   Silently reinterpreted, never rejected.
10. `grep` unpinned — the interactive default on this machine is ugrep.
11. Hook: `repo_root=$(git rev-parse --show-toplevel) || exit 0` — allowed the
    push when it could not locate the repo.
12. Hook: ran **only** the tree guard, so conflict-marker text in file content
    was never checked on push at all.
13. Hook: `--not --remotes=origin $sha` argument order. — **defect 3**
14. Success message `OK` was indistinguishable from a vacuous run.

Fixed by: checking every git exit status; requiring cwd to be inside a git repo
and cross-checking it against the repo the script itself ships in; verifying both
range endpoints exist; rejecting bare revs; pinning `/usr/bin/grep`; running both
guards from the hook; and making the verdict line always start with `PASS:`,
`FAIL:` or `ERROR:` and state **how many commits/files were actually examined** —
a vacuous run can no longer be mistaken for a real one.

## New contract

- exit **0** = `PASS — <n> commit(s)/file(s) checked ...` (n is always > 0)
- exit **1** = `FAIL — ...` do not push
- exit **2** = `ERROR — nothing was checked` — could not determine; do not push

The one remaining exit-0-without-checking path is the **no-argument** form when
`main@origin..@-` is genuinely empty. It prints
`NOTHING TO PUSH — ... ; NO COMMITS WERE CHECKED`, which cannot be read as a
clean bill of health.

## Deliberate strictness (not fail-opens, but behaviour changes)

- Pushing a **new ref** whose tip origin already has now resolves to 0 commits
  and is **blocked**. The repo rule is "NEVER create branches", so this is
  acceptable. Use `--no-verify` only after checking by hand.
- A range with commits but **0 changed paths** (e.g. empty commits) is an ERROR
  for the markers guard: nothing could be scanned, so nothing can be vouched for.

## Still open (follow-up, not fixed here)

- The **revert-detection** half of the anti-clobber protocol in
  `.claude/rules/vcs.md` remains manual — there is no script that fails when the
  outgoing range rewinds a product file the committer did not author.
- There is no **tree-size gate** in either guard. The landing protocol requires
  `git ls-tree -r --name-only $COMMIT | wc -l` to be ~109,548 by hand. Both wipes
  would have been caught by an automated size gate; consider adding one as a
  third guard.

## Reproduction

Fixtures are built with plumbing only, in a throwaway clone — see the transcript
of this lane. In short:

```sh
# conflict tree
sub=$(printf '100644 blob %s\tx\n' "$(printf 'c\n' | git hash-object -w --stdin)" | git mktree)
tree=$(printf '040000 tree %s\t.jjconflict-base-0\n040000 tree %s\t.jjconflict-side-0\n040000 tree %s\t.jjconflict-side-1\n' $sub $sub $sub | git mktree)
git commit-tree "$tree" -p <base> -m 'FIXTURE conflict tree'

# marker content (also try a filename containing a space)
printf 'a\n<<<<<<< conflict 1 of 1\nx\n>>>>>>> conflict 1 of 1 ends\nb\n' > f
```

## Pipes still swallow the exit status

A piped exit status is the **last** command's, so `guard | tail` discards the
guard's status entirely. The scripts cannot prevent this. Mitigation shipped: the
verdict line always goes to **stdout** and always begins with `PASS:`, `FAIL:` or
`ERROR:`, so even a truncated `| tail` shows the verdict. The protocol rule
stands: **redirect to a FILE and read the file.**
