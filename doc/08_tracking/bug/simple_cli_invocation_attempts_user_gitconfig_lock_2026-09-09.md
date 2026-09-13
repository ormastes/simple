# Simple CLI invocation attempts to lock the user's `.gitconfig`

- **ID:** `simple_cli_invocation_attempts_user_gitconfig_lock_2026-09-09`
- **Date:** 2026-09-09
- **Status:** OPEN
- **Severity:** P1
- **Component:** `src/compiler_rust/driver/src/main.rs`

## Symptom

During the 2026-09-09 Windows CLI smoke, an otherwise read-only Simple command
attempted to acquire a lock for the user's `.gitconfig`. A help, version, or
tool-dispatch probe has no authority to mutate or lock user-global Git
configuration.

## Impact

This is a host-state and portability failure independent of compiler output.
It can interfere with concurrent Git operations and makes Phase 1 tooling
verification fail even when the invoked command later returns successfully.

## Required evidence and closure oracle

Retain the exact invoking argv, executable digest, resolved HOME/Git config
paths, diagnostic text, and pre/post existence and hashes for `.gitconfig` and
its lock file. Closure requires the same invocation to leave both paths and
hashes unchanged and to create no lock. Configuration writes, if intentional,
must use an explicit repository-local owner and opt-in boundary; silently
redirecting the global lock is not a fix.

This is not `shared_git_config_core_worktree_misdirects_prepush_guards`, which
concerns an already-present `core.worktree` value rather than a Simple process
attempting the user-global config lock.

## Triage 2026-09-13 (BUGFIX-7 lane)

Cannot reproduce on this host: the original symptom is scoped to a "2026-09-09
Windows CLI smoke" and this lane runs on Linux aarch64
(`/home/yoon/dev/simple-bugfix-7`, base `a6450c9d6f5`) with no Windows machine
available — a Windows-specific Git-for-Windows / MSYS interaction cannot be
exercised here, so this is a diagnosis, not a close.

Source search for the mechanism turned up nothing in this crate:
- `src/compiler_rust/driver/src/main.rs` and the rest of
  `src/compiler_rust/driver/src/`: no `gitconfig`/`git2::`/`.gitconfig` text.
- `src/compiler_rust/Cargo.lock`: no `git2`, `gix`, or similarly named crate at
  all — so this is not a transitive Rust dependency opening
  `~/.gitconfig` directly (e.g. via `git2::Config::open_default`).
- No shelled-out `"git"` subprocess invocation found under `src/app/cli/` or
  `src/compiler_rust/driver/src/`.

Working hypothesis (unconfirmed): the lock attempt is not compiler-source code
touching Git at all, but an environment-level side effect specific to Windows —
e.g. a Git-for-Windows/MSYS shell profile or `HOME`-resolution step invoked when
the CLI wrapper script (not this Rust binary) starts a subshell, or a
Rust-toolchain/build-time step (`cargo`/`rustc` invoking its own VCS-ignore
probing) rather than the deployed `simple` binary itself. This cannot be
distinguished from the record's own required evidence (argv, executable
digest, resolved HOME/Git config paths) without a Windows host and a
`Process Monitor`/strace-equivalent capture, which this lane does not have.
Left OPEN; recommend the closure-oracle repro be run by a session with Windows
access, capturing the exact argv per the record's own evidence bar.
