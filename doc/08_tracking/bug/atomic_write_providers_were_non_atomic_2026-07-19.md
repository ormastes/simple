# atomic-write providers were non-atomic

**Status:** SOURCE FIXED / NATIVE-ALL EXECUTION PENDING  
**Severity:** P1 — interrupted lint, formatter, runner, or doc writes could lose data

## Root cause

Canonical `std.io.file_atomic_write` delegated to delete-first `file_write`.
The interpreter used a shared deterministic `<target>.tmp` path, and native-all
used plain `std::fs::write`. Concurrent writers could collide, and interrupted
writes could expose a missing or partial destination.

## Solution

The canonical Simple facade now calls `rt_file_atomic_write`. Interpreter and
native-all providers create a unique temporary file in the destination
directory, write and sync it, then persist it atomically. Failure leaves the
existing destination and directory intact and cleans the temporary file.

## Evidence

- interpreter replacement, relative-parent, and fail-closed regression: PASS
- equivalent native-all regression: authored; execution remains pending after
  the native-all lane reached its bounded-attempt cap
- admitted Stage 4 lint/formatter integration: pending
