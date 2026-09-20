# Bootstrap diagnostic sweep missing-child preflight
## Closed 2026-09-16 — ...e` before launching parallel work. ## Fix and evidence The harness now rejects a missing o

Reviewed in the 2026-09-16 bug-ledger normalization pass; classification is
bookkeeping from in-file evidence, not a re-run of the repro. Re-open with a
fresh dated repro if the symptom returns.

## Reproduction

A canonical diagnostic sweep in a fresh worktree dispatched all selected files
with the Rust bootstrap seed, but the ignored deployed `bin/simple` target was
absent. Every sampled worker failed with `/bin/sh: 1: exec: bin/simple: not
found`, producing no source diagnostics.

## Root cause

The sweep validated its explicit seed compiler but not the seed's canonical
pure-Simple child at `bin/simple` before launching parallel work.

## Fix and evidence

The harness now rejects a missing or non-executable `bin/simple` with exit 2
before creating worker state. The integration test covers that exact fail-fast
case and the adjacent admitted-child aggregation/cache-preservation path.

