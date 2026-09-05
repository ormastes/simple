# Bootstrap diagnostic sweep batch barrier and unbounded workers

**Status:** Fixed
**Area:** bootstrap diagnostics / scheduler / process isolation

## Measured symptom

The corrected canonical sweep reached only about 23 of 11,291 files after
roughly 3–4 minutes with `--jobs=32`, implying an approximately 24-hour run at
the observed rate. The first batch retained several ~283-second stragglers at
about 0.5% CPU (`build_simpleos_toolchain`, `main_and_help`,
`symbol_resolution`, `arch_check`, and `query_commands`). Fast slots remained
idle because the next file was not dispatched until every process in the
32-file batch exited.

## Root cause

Each file intentionally uses a separate compiler process and stable private
cache. This correctly isolates parser/semantic globals and concurrent cache
writers, but repeats full compiler startup and import-closure work. The runner
then amplified that unavoidable first-step cost with two scheduler defects:

1. fixed-size batch barriers prevented completed slots from accepting work;
2. workers had no deadline or process-group cleanup, so a stalled compiler or
   delegated `bin/simple` descendant could retain a slot indefinitely.

Sharing writable caches or reusing a compiler process was rejected: neither
cache concurrency nor complete parser-global reset has been proven safe.

## Resolution

- Replace batch barriers with a continuously refilled bounded job queue.
- Keep deterministic, sorted indexing and emit grouped diagnostics only after
  every selected file has produced a terminal status.
- Retain stable per-file caches, so writers remain isolated and later sweeps
  can reuse the same file's cache.
- Run every compiler in a new process group. A configurable per-file timeout
  sends TERM, waits a configurable grace period, then sends KILL to the entire
  group. The generous defaults are 600 seconds plus a 5-second grace; a faster
  continuation can select a lower `--timeout` explicitly.
- Count timeouts as failures, identify them separately, continue filling the
  queue, return nonzero, and retain no artifact/deployment path.

## Evidence contract

The integration test covers all-file execution after timeouts, exact timeout
diagnostics, nonzero status, descendant cleanup, deterministic ordering of
mixed timeout/compiler-failure groups, invalid timeout rejection, ordinary
success/failure aggregation, cache isolation, and cache preservation.

A bounded nine-file fixture with three 1.2-second stragglers and `--jobs=3`
measures the old batch scheduler and the new dynamic scheduler with identical
inputs. The batch scheduler took 3,845 ms; the final dynamic scheduler took
2,074 ms, saving 1,771 ms and completing 1.85x faster.

## Remaining bottleneck

Per-file compiler startup and import-closure work remains dominant. A future
persistent-worker mode requires evidence that all parser, semantic, driver, and
runtime globals reset completely between files. A shared-cache mode requires a
read-only seed format or explicit single-writer publication protocol. Neither
unsafe optimization is part of this fix.
