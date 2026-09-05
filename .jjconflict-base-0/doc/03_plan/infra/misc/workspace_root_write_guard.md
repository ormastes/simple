<!-- codex-research -->

# Workspace Root Write Guard - Detailed Implementation Plan

Status: **Complete — all 6 phases implemented and verified** (updated 2026-05-29)

## Phase 1 - Policy and Audit — ✅ Complete

`scripts/check-workspace-root-guard.shs` reads `FILE.md` Quick Reference and
Root Files tables via awk, derives allowed root entries and declared child paths.
Supports `audit`, `--staged`, `--path-file`, `--strict`, `--dry-run`, and
`--self-test` modes. Self-test creates a synthetic workspace and verifies WRG001
and WRG002 detection.

## Phase 2 - Fix/Quarantine — ✅ Complete

`fix` mode moves violations to `build/workspace_quarantine/<timestamp>/` with a
manifest. Never deletes files by default.

## Phase 3 - Lint Integration — ✅ Complete

`src/app/io/cli_ops.spl` defines `_cli_run_workspace_root_guard()` which shells
out to the guard script with `audit --staged`. Both `cli_lint_commands.spl` and
`lint_entry.spl` call it before normal lint. `scripts/check/check-repo-hygiene.shs`
also delegates to `audit --staged`.

## Phase 4 - Commit Hook — ✅ Complete

`scripts/hooks/pre-commit` exists and delegates to
`sh scripts/check-workspace-root-guard.shs audit --staged`. Install via
`git config core.hooksPath scripts/hooks`.

## Phase 5 - Lock/Unlock — ✅ Complete

`lock` mode prints platform-specific commands (Unix chmod / Windows icacls) by
default. `--apply` mutates permissions with a restore manifest saved to
`build/workspace_quarantine/`. `unlock --apply` restores from manifest.

## Phase 6 - Tool-Server Protection — ✅ Complete

`src/lib/nogc_async_mut/mcp/fileio_protection.spl` implements rule-based file
I/O access control with Deny/Protect/Redirect/Atomic/Allow actions, glob/regex
pattern matching, and read/write/delete/rename operation types.

## Bug Fixes (2026-05-29)

- Fixed `policy_tmp_dir()`: replaced manual `mkdir -p` with `mktemp -d` to
  handle non-existent `$TMPDIR` parent directories.
- Fixed 30s+ hang: eliminated unconditional `find -maxdepth 2 | git check-ignore
  --stdin` pipeline (53K+ paths from `.tmp*` worktree dirs). Now only runs
  `git check-ignore` for `--path-file` mode; `--staged` and full audit modes use
  empty ignored list since `git ls-files --others --exclude-standard` already
  excludes ignored paths.
