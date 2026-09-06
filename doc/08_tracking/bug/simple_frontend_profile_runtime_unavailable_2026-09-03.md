# Tiny frontend profiling unavailable in admitted release runtime

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

