# Bug — `simple check` reports "no admitted cached self-hosted check worker artifact" outside the repo root

Date: 2026-09-28. Status: FIXED (source-only; no build or redeploy needed —
`src/app/**` is read as source on every run).

## Symptom

From any directory other than the checkout root:

```
$ cd /tmp && /home/yoon/dev/simple/bin/simple check h.spl
ERROR: no admitted cached self-hosted check worker artifact is available
```

exit 1, while the same command from the repo root passes. The release worker
`bin/release/aarch64-unknown-linux-gnu/simple` was present the whole time.

## Root cause

`src/app/cli/check_entry.spl` resolved the worker binary
(`bin/release/<triple>/simple`), the worker source entry
(`src/app/check/main.spl`) and the `bin/simple` retry fallback as
cwd-relative paths. No artifact is "admitted" or cached anywhere: the
message only means `file_exists("bin/release/<triple>/simple")` was false
relative to the caller's cwd (or `SIMPLE_BINARY`/`SIMPLE_BIN` were unset).
Fresh worktrees also lack `bin/release/` because it is untracked.

## Fix

The three paths are anchored on the install root derived from the running
executable (`cli_current_exe_path()`, i.e. `/proc/self/exe`): the prefix
before `/bin/release/`. A binary outside a release tree keeps the old
cwd-relative behaviour, and the error now names the root it searched.

Proof: `test/01_unit/app/cli/check_entry_install_root_spec.spl` red (3/3 fail)
-> green (3/3); from `/tmp`, a clean file passes (rc 0) and a type error is
reported with rc 1.

## Deploy requirement (unchanged)

A worker binary must exist at `<root>/bin/release/<triple>/simple`, or be named
by `SIMPLE_BINARY`. A fresh worktree has none; point `SIMPLE_BINARY` at a
deployed release binary.
