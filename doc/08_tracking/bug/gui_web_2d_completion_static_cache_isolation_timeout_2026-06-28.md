# GUI/Web/2D Completion Static Cache Isolation Timeout

## Closed 2026-11-25 — SSpec side of the documented fix landed

The 2026-06-28 "Implemented Fix" was only half-landed: the aggregate script
grew `GUI_RENDERDOC_AGGREGATE_READONLY_STATIC_CACHE_DIR` support, but the
completion SSpec still pointed the shared seeded cache at the *writable*
`GUI_RENDERDOC_AGGREGATE_STATIC_CACHE_DIR`, so concurrent runs could still
mutate shared evidence. This change makes the SSpec match the documented
design: all six lane commands now pass the shared
`build/test-gui-renderdoc-feature-coverage-static-cache` as read-only and
write cache misses under each lane's per-run build root
(`<root>/static-cache`).

- **measured** (Windows host, Git Bash): the exact lane command with the new
  env completed in ~19 s, produced a 1109-line `evidence.env`, took all six
  static-cache gates from the read-only seed (no per-run cache dir was
  created, and the shared dir's mtimes were untouched); a second run with an
  empty read-only seed populated misses under the per-run writable cache and
  left the shared dir absent.
- **limit**: the full SSpec cannot execute on this host — the Rust seed
  (v1.0.0-rc.1) rejects `@representation_boundary` in the imported
  `std.io_runtime` (edited spec re-parses cleanly; the error is unchanged and
  pre-existing), and there is no SPipe test daemon here, so the original
  daemon-timeout acceptance is verified only indirectly via the per-lane
  command evidence above.
- **host caveat**: `check-gui-renderdoc-feature-coverage-status.shs` needs
  `PYTHONUTF8=1` under this host's cp949 locale (pre-existing, affects the
  old env identically — subprocess reader threads crash decoding non-ASCII
  gate output); orthogonal to this fix.

## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

## Triage note 2026-09-13 — could not verify: the spec runner is broken on this host
- **measured** (Windows Rust seed v1.0.0-rc.1): `bin/simple test` is non-functional here — a 3-line 1-assertion spec returns in under a second with `WARNING: test daemon unavailable; running directly`, `error: test-runner: code -1 (process_run_bounded killed the child at its budget)` and a false `reason=outer-bound-timeout budget_ms=930000`. Seven real specs produced byte-identical verdicts.
- **inferred**: every runner-behaviour claim in this entry (example counts, PASS/FAIL bookkeeping, daemon timeouts) is therefore unverifiable here; a green or red from this host would be meaningless either way.
- **inferred**: left OPEN, not stale — the referenced spec files all still exist.

## Status

Closed 2026-11-25 (SSpec now uses the read-only seeded cache plus per-run
writable cache exactly as documented below; see the dated section at the top
for measured evidence and verification limits).

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

