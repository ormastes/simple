# atomic-write providers were non-atomic

**Status:** CLOSED-STALE (2026-09-12: not re-verifiable from the record; reopen with a fresh repro against the current seed)
**Severity:** P1 — interrupted lint, formatter, runner, or doc writes could lose data

## Root cause

Canonical `std.io.file_atomic_write` delegated to delete-first `file_write`.
The interpreter used a shared deterministic `<target>.tmp` path, and native-all
used plain `std::fs::write`. Concurrent writers could collide, and interrupted
writes could expose a missing or partial destination.

## Solution

The canonical Simple facade now calls `rt_file_atomic_write`. Interpreter,
native-all, and core-C providers create a unique temporary file in the
destination directory, write and sync it, then persist it atomically. The
core-C owner decodes the real tagged-text ABI and preserves embedded NUL bytes.
Failure leaves the existing destination intact and cleans the temporary file.
Replacement also copies existing destination permissions to the temporary file
before the atomic rename, so formatting a source file does not silently chmod it.

## Evidence

- interpreter replacement, relative-parent, and fail-closed regression: PASS
- native-all replacement, relative-parent, directory fail-closed, and temp-cleanup regression: PASS
- expanded core-C stale-temp collision, embedded-NUL, truncation,
  parent-creation, rename-cleanup, collision-preservation, and mode-preservation
  regression: PASS
- formatter `--write` routes through the canonical atomic provider in source:
  PASS
- admitted Stage 4 lint/formatter integration: pending

## Triage 2026-09-12
Rule C: record predates 2026-07-29 (>=45 days) and carries no repro that ran conclusively within the triage budget; closed stale per the standing 'too old -> close' decision. Binary (unused, no run needed): /home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple, 50,093,192 B, 2026-09-06 09:59.
