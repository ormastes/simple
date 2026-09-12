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
