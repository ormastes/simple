# Pre-push conflict-marker guard: "Argument list too long" on Windows (2026-10-27)

**Status:** FIXED
**Severity:** P2. The push guard fails with ERROR ("nothing was checked"), and the push is rejected.

## Symptom
On Windows (Git Bash / MSYS2), pushing a branch whose outgoing range touches many files fails inside
`scripts/check/check-no-conflict-markers-push.shs`:

    check-no-conflict-markers-push: ERROR — git grep (open-marker pattern) failed:
      .../check-no-conflict-markers-push.shs: line 513: /mingw64/libexec/git-core/git: Argument list too long
    check-no-conflict-markers-push: ERROR — nothing was checked (exit 2)

It was seen on the first push of PR #4948 while `refs/remotes/origin/main` was stale, so the
computed range was large. It went away after `git fetch origin main` shrank the range to one commit.

## Cause
`run_grep_chunked` batches changed paths into `git grep ... -- <paths>` calls of `CHUNK=500` paths.
Windows limits a whole command line to 32,767 characters. 500 paths averaging more than about 64 characters
exceed it. Linux's ARG_MAX (about 2 MB) never does, so the bound looked safe there.

## Fix
The chunk is now also bounded by the summed path length: `CHUNK_BYTES=20000`. A batch flushes at 500 paths or
at 20,000 bytes, whichever comes first.

## Evidence
Fixture repo with 600 files at about 108-character paths:
- old script: `ERROR — ... Argument list too long`
- fixed: `PASS — 600 file(s) scanned ... 0 conflict markers`
- fixed, with a marker in file 599 (second chunk): `FAIL — conflict markers found`
- `--selftest`: 3 fixtures passed. A real range of 2,076 files reports the same PASS verdict before and after the fix.
