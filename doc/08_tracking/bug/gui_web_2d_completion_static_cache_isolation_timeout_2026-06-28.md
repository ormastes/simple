# GUI/Web/2D Completion Static Cache Isolation Timeout
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

## Triage note 2026-09-13 — could not verify: the spec runner is broken on this host
- **measured** (Windows Rust seed v1.0.0-rc.1): `bin/simple test` is non-functional here — a 3-line 1-assertion spec returns in under a second with `WARNING: test daemon unavailable; running directly`, `error: test-runner: code -1 (process_run_bounded killed the child at its budget)` and a false `reason=outer-bound-timeout budget_ms=930000`. Seven real specs produced byte-identical verdicts.
- **inferred**: every runner-behaviour claim in this entry (example counts, PASS/FAIL bookkeeping, daemon timeouts) is therefore unverifiable here; a green or red from this host would be meaningless either way.
- **inferred**: left OPEN, not stale — the referenced spec files all still exist.

## Status

Mitigated.

## Summary

`test/03_system/check/gui_web_2d_goal_completion_criteria_spec.spl` now uses
per-run build roots so concurrent agents do not overwrite lane output while the
SSpec is reading evidence. The aggregate nested-gate static cache still uses
the shared `build/test-gui-renderdoc-feature-coverage-static-cache` directory.

An attempted headless change to move
`GUI_RENDERDOC_AGGREGATE_STATIC_CACHE_DIR` under each per-run root made the
focused SSpec exceed the test daemon timeout. The command failed with:

```text
ERROR: test daemon timed out: test/03_system/check/gui_web_2d_goal_completion_criteria_spec.spl
```

## Impact

The shared static cache is currently required to keep the headless completion
SSpec within the daemon timeout. It may still be a concurrency risk because
`scripts/check/check-gui-renderdoc-feature-coverage-status.shs` can populate
that cache when a key is missing.

Mitigation: `scripts/check/check-gui-renderdoc-feature-coverage-status.shs`
now supports `GUI_RENDERDOC_AGGREGATE_READONLY_STATIC_CACHE_DIR` for seeded
lookup and keeps `GUI_RENDERDOC_AGGREGATE_STATIC_CACHE_DIR` as the writable
cache for misses. The completion SSpec uses the shared seeded cache as
read-only and writes misses under its per-run build root.

## Reproducer

1. In `test/03_system/check/gui_web_2d_goal_completion_criteria_spec.spl`,
   replace the shared static cache path with a per-run path such as
   `${root}/static-cache`.
2. Run:

```sh
SIMPLE_LIB=src bin/simple test test/03_system/check/gui_web_2d_goal_completion_criteria_spec.spl --mode=interpreter --clean --fail-fast
```

## Expected

The completion SSpec keeps isolated mutable output and cache paths while still
finishing within the test daemon timeout.

## Actual

The SSpec times out when every nested aggregate gate has a cold per-run cache.

## Implemented Fix

Split the aggregate cache into two modes:

- read-only seeded cache for expensive stable nested evidence
- per-run writable cache for newly generated nested evidence

The completion SSpec can then consume the read-only seeded cache without
allowing concurrent runs to mutate shared evidence.

