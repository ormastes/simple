# Bug: parser "self." info hint has no de-dup — 158 blocks in one compile

**Date:** 2026-07-25  
**Lane:** L5 (parser diagnostics)  
**Status:** CLOSED-STALE (2026-09-12: not re-verifiable from the record; reopen with a fresh repro against the current seed)

## Root Cause

The `self.`-prefix info diagnostic (emitted from `src/compiler_rust/parser/parser_helpers.rs` and `parser_impl/core.rs`) fires **once per occurrence** with a full multi-line explainer block. A single file with multiple legit `self.foo` Option-binding sites produces 158 identical info blocks / ~2049 output lines in one compile (`src/lib/gc_async_mut/gpu/engine2d/engine.spl`).

## Observed Impact

- Massive log spam directly feeds **Bug #1 (examples watchdog pipe deadlock)** — the explainer blocks fill the 64KB pipe.
- Parser output is unreadable; genuine errors/warnings buried in repetition.
- Contributes to false "timeout" diagnosis.

## Concrete Fix Direction

Emit the full multi-line explainer **once per compile** (or once per file), then emit one-line or suppressed repeats for subsequent occurrences. Match info-hint de-dup pattern used elsewhere in the parser (if any) or establish a new pattern.

## Status

High-priority unblock for examples lane and general usability. Fix is simple rate-limiting / context tracking; estimated low effort.

## Triage 2026-09-12
Rule C: record predates 2026-07-29 (>=45 days) and carries no short (<=3 min) repro; closed stale per the standing triage decision. Binary identity (not run, no repro to verify): /home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple, 50,093,192 B, 2026-09-06 09:59.
