# atomic-write providers were non-atomic
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

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


## Verification 2026-11-25 (P3 fleet, release/1.0.0)

Status header "Open — needs owner triage" was stale: the Solution/Evidence
sections above already record the provider fix. Re-verified on Windows with the
tracked self-hosted binary (`bin/simple.exe`, SIMPLE_LIB=src):

- `bin/simple.exe test test/01_unit/lib/atomic_write/unique_tmp_atomic_write_spec.spl --mode=interpreter`
  → `outcome=OK declared>=4 executed=4 passed=4 failed=0` (4/4 PASS).

The unique-tmp + atomic-persist provider behavior is green in the interpreter
lane. The remaining "Stage 4 integration pending" line is a release-admission
pipeline item, not an open code defect in the atomic-write providers.

**Status:** RESOLVED (provider regressions verified green 2026-11-25; stage-4
admission tracked separately as pipeline work).

Verification base note: runs above executed at tree fcd95d41d60 (release/1.0.0
at session start) with its matching tracked bin/simple.exe. Later same-day
merges (notably cfd89933699, the 940-annotation `@representation_boundary`
autofix) moved src/ ahead of the pinned binary, which then rejects the new
decorator; the verified behavior is unchanged by that source-only annotation
wave.
