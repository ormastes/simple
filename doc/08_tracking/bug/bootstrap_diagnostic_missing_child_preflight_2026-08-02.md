# Bootstrap diagnostic sweep missing-child preflight

Status: OPEN (P3)
Status re-verified 2026-08-17 by source inspection (triage shard 00).

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
