# atomic-write providers were non-atomic

**Status:** PROVIDER REGRESSIONS PASS / STAGE 4 INTEGRATION PENDING
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

## Evidence

- interpreter replacement, relative-parent, and fail-closed regression: PASS
- native-all replacement, relative-parent, directory fail-closed, and temp-cleanup regression: PASS
- expanded core-C stale-temp collision, embedded-NUL, truncation,
  parent-creation, rename-cleanup, and collision-preservation regression: PASS
- admitted Stage 4 lint/formatter integration: pending
