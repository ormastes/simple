# Windows MSVC bootstrap depends on an UNTRACKED env script

- **Date:** 2026-09-02
- **Status:** OPEN
- **Severity:** blocker for any fresh clone / worktree / CI on Windows MSVC

## Symptom

The sanctioned Windows MSVC bootstrap route cannot be run from a clean
checkout of any commit. Sourcing the documented env script fails:

```
/usr/bin/bash: line 7: scripts/setup/windows-msvc-bootstrap-env.shs: No such file or directory
```

## Root cause

`scripts/setup/windows-msvc-bootstrap-env.shs` has **never been committed**.
It exists only as an untracked file in one developer working copy.

Measured 2026-09-02 in `C:\Users\ormas\dev\simple`:

```
$ git ls-files --error-unmatch scripts/setup/windows-msvc-bootstrap-env.shs
error: pathspec '...' did not match any file(s) known to git

$ git status --porcelain scripts/setup/windows-msvc-bootstrap-env.shs
?? scripts/setup/windows-msvc-bootstrap-env.shs
```

Confirmed absent from the tracked tree of the session lane commit
`6e9660e36719c9775c742b7e7c331c8b55068184` (134,490 files):

```
$ git ls-tree --name-only 6e9660e3671 scripts/setup/ | grep -i msvc
(no output)
```

The sibling `scripts/setup/llvm-toolchain-env.shs` IS tracked, which is why
the gap is easy to miss — the directory looks populated.

Local copy for reference: 5,050 bytes, md5 `687134754cc3803d035eaf1b41c8edbd`.
It puts LLVM 18 on PATH (`llvm-config` 18.1.8), which `llvm-sys 180` requires;
CLAUDE.md's LLVM-23 script is explicitly NOT a substitute, and the two must not
be sourced into one shell.

## Why the other guards miss it

Every pre-push guard checks tree structure, symbol sets, or source that is
present. None asserts that a file the documented build path SOURCES is
tracked. An untracked file is invisible to all of them.

## Impact

- Any fresh clone, `git worktree add`, or CI runner on Windows MSVC cannot
  bootstrap: the env script is simply not there.
- The dependency is silent — the failure surfaces as a missing-file error from
  the shell, far from the cause.
- Bootstrap receipts record `git rev-parse HEAD` and `git status --porcelain`
  (`produce-bootstrap-planner-admission-v2.shs:179-181`), so working around it
  by copying the file INTO the tree dirties the tree the receipt attests to.

## Unblock condition

Commit `scripts/setup/windows-msvc-bootstrap-env.shs`. Then add a guard
asserting that every script sourced or executed by `scripts/bootstrap/**` is
tracked, so this class cannot recur.

## Cross-platform impact

None. The file is Windows-MSVC-only and is not referenced by any Unix lane;
committing it changes no Unix behaviour.
