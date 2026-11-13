# Tiny frontend profiling unavailable in admitted release runtime
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

**Status:** open  
**Date:** 2026-09-03

## Reproduction

Using `/Users/ormastes/simple/bin/release/macos-arm64/simple` (`v1.0.0-rc.1`)
against a two-line valid source:

- source execution returns `Error running`;
- `check` invokes the broader build lane and reports lint/format subprocess exit
  `-1` instead of a frontend check receipt;
- `compile ... -o tiny.smf` returns `Compilation failed`;
- `run src/app/optimize/main.spl ... --full --level=O3` returns `Error running`.

## Impact

The process floor can be observed, but parse/check/SMF phase time, successful
diagnostic parity, and before/after wall time cannot be qualified. Reporting
these failed commands as compiler performance would be false evidence.

## Required resolution

Produce a current, producer-authenticated self-hosted runtime that can execute
the valid tiny fixture, expose frontend phase counters, and complete the
optimizer command without Rust-seed fallback.



---

## Lane disposition 2026-11-13 (live-p3-l4, work/live-p3-l4-20261113, base f790f7f266e)

Concurs with the record's own required resolution: this needs a producer-authenticated self-hosted runtime (admitted pure-Simple binary with frontend phase counters, optimizer command completing without Rust-seed fallback). That is the self-host deployment program, not a P3 bug fix; the deployed seed on this host explicitly warns it is bootstrap-only. No in-lane change. Owner: self-host/deploy lane.
