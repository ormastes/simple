# Tauri Mobile Artifact Gate Fixture Drift - 2026-06-28

## Status

**Status:** RESOLVED (per body: "Fixed."; not independently re-run in this pass, 2026-09-12)

Fixed.

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

## Triage 2026-09-12

Corrected in the 2026-09-12 bug-db triage sweep (Rule E: body already says FIXED; the bulk stale-close pass had wrongly applied CLOSED-STALE here — corrected to RESOLVED to match the record's own verdict). Not independently re-run in this pass. Evidence: worktree `simple-bugdb-triage` branch `work/bugdb-triage-2026-09-12`; deployed seed `/home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple` (50,093,192 B, 2026-09-06 09:59) available for re-verification.
