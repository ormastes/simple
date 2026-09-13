# Bootstrap diagnostic sweep missing-child preflight
**Status:** OPEN (unverified 2026-09-12)

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

## Triage 2026-09-12
Rule D: record postdates 2026-07-29 and has no cheap repro reachable within budget; left open with an explicit unverified status line.

## Triage 2026-09-13

The doc's own "Fix and evidence" section describes a landed fail-fast fix (harness rejects a missing/non-executable `bin/simple` with exit 2, covered by an integration test), but no `Status:` line reflects that and the fix location/test file were not identified by name in the record or found by a scoped grep this pass (`missing-child preflight`, `admitted-child aggregation` — zero hits in `test/`/`scripts/`). Not confident enough to mark RESOLVED without locating and re-running that evidence. Leaving OPEN (unverified) as previously triaged; no code change made.
