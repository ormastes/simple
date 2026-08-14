# Render performance 8K80 parent aggregator is missing

Status: open

The canonical plan's A7 row requires one parent-authoritative decision over
the production-native DrawIR receipt, semantic producer receipt, and physical
presentation receipt.  No `scripts/check/check-render-perf-8k80-completion.shs`
owner exists yet, so separate green rows could otherwise be combined manually
or promoted despite mismatched device, viewport, damage class, revision, or
artifact provenance.

## Location and effect

- Plan contract: `doc/03_plan/ui/perf/render_perf_redesign_plan_2026-08-06.md`,
  A7 in §0-B.
- Missing implementation: `scripts/check/check-render-perf-8k80-completion.shs`.
- Blocked acceptance: A7 and umbrella 8K80 promotion.

## Unblock condition

Implement the named wrapper with explicit `--drawir`, `--producer`,
`--physical`, and `--report` inputs.  It must bind all three receipts to the
same 7680x4320 workload, named physical device/driver, damage class, and source
revision; require p95 at most 12.5 ms, nonzero RSS/checksum, exact readback
scope, no seed/interpreter/CPU/stub fallback, and known completion; reject
missing, glob-ambiguous, stale, or mismatched inputs.  Add a bounded self-test
with one passing fixture and deliberate-red missing/mismatched/fallback rows.

Resume with the exact A7 command in the canonical plan and retain the generated
report plus all three input receipts.  Owner: render-performance integration.
Final reviewer: independent highest-capability Codex.
