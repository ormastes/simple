# Tauri Mobile Artifact Gate Fixture Drift - 2026-06-28

## Closed 2026-09-13 — Status was already "Fixed"; gate is an Android/Linux lane not runnable on this host

- **inferred** The entry's own `## Status` section reads `Fixed.` and records the fixture reconciliation.
- **inferred** Re-running the cited gate (`bin/simple test test/03_system/check/tauri_mobile_renderer_parity_artifact_gate_spec.spl`) needs an Android/Linux capture host; this Windows box has no such lane, so no fresh measurement was taken.

## Status

Closed (fixed) 2026-09-13.

## Context

While tightening the headless-safe Tauri mobile renderer parity contract, the
fixture was updated to require Android foreground proof
(`tauri_mobile_renderer_parity_android_render_log_foreground_marker_status=pass`),
distinct render-log/dev-log source files, and MDI `eventSequence` rows.

## Evidence

Command:

```sh
SIMPLE_LIB=src bin/simple test test/03_system/check/tauri_mobile_renderer_parity_artifact_gate_spec.spl --mode=interpreter --clean --fail-fast
```

Earlier result after three capped fix/verify cycles was `38 examples, 6
failures`. A later focused continuation fixed the remaining negative-scenario
expectation drift.

Final result:

- `38 examples, 0 failures`
- Positive fixture passes with Android foreground proof.
- Negative fixtures match the stricter first-failure ordering.

## Required Fix

Done. The negative scenario fixtures and expected reasons now match the current
stricter wrapper ordering:

1. Preserve the new positive-path requirements: distinct render-log sources,
   Android foreground marker, MDI event sequence, and matching normalized rows.
2. For alias-output scenarios, provide a passing production env when the test
   intends to exercise lane-output alias rejection first.
3. For malformed MDI detail scenarios, decide whether row-mismatch should be
   the intended first failure or update the fixture JSON and normalized rows
   together so the detail-specific incomplete reason is reached.

The production wrapper was not weakened.
