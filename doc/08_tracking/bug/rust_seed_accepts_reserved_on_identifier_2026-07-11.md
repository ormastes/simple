# Rust Seed Accepts Reserved `on` Identifier
**Status:** CLOSED-STALE (2026-09-12: not re-verifiable from the record; reopen with a fresh repro against the current seed)

The Rust seed accepted `val on = ...` in `src/os/hosted/hosted_entry.spl`, while
the stage3 pure-Simple discovery parser rejected it with `expected pattern,
found On`. Source checks performed only with the seed therefore produced a
false green result.

Production code now uses `fullscreen_enabled`. Parser conformance should add a
shared negative fixture so seed and self-hosted frontends reject reserved
identifiers consistently with a source location.

## Triage 2026-09-12
Rule C: record predates 2026-07-29 (>=45 days) and carries no short (<=3 min) repro; closed stale per the standing triage decision. Binary identity (not run, no repro to verify): /home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple, 50,093,192 B, 2026-09-06 09:59.
