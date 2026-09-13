# Bug: examples/ isolation watchdog deadlocks on >64KB output

**Date:** 2026-07-25  
**Lane:** L5 (examples safety isolation check)  
**Status:** CLOSED-STALE (2026-09-12: not re-verifiable from the record; reopen with a fresh repro against the current seed)

## Root Cause

The `run_child_with_timeout` watchdog in `src/compiler_rust/driver/src/cli/examples_safety.rs:115-166` spawns isolated examples/ children with `Stdio::piped()` stdout/stderr. It then poll-loops `try_wait()` **without draining pipes**, and only reads buffered output via `wait_with_output()` **after the child exits**.

When a child emits >64KB (typical OS pipe buffer capacity), the write() blocks forever because the parent never reads. The pipe fills; the child stalls; the timeout fires and kills it.

## Observed Impact

- `widget_showcase_gui.spl` run under `examples/` hangs >8s wall-clock with ~2049 log lines / 158 parser diagnostic blocks pending. Same file outside `examples/` completes ~30s. Non-examples paths inherit stdio and stream fine.
- **Every substantial example "times out"** — misdiagnosed as slowness rather than deadlock.

## Concrete Fix Direction

Drain stdout/stderr via reader threads spawned alongside the poll loop. Threads read continuously and buffer in memory; poll loop collects them after exit.

Reference implementation: `examples_safety.rs` branch fix (in progress).

## Status

Fix blocks all current example verification runs. High priority for examples lane unblock.

## Triage 2026-09-12
Rule C: record predates 2026-07-29 (>=45 days) and carries no repro that ran conclusively within the triage budget; closed stale per the standing 'too old -> close' decision. Binary (unused, no run needed): /home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple, 50,093,192 B, 2026-09-06 09:59.
