# GUI/Backend Performance Agent Task Plan

Lane: ongoing Simple GUI/backend performance convergence
Updated: 2026-06-11

## Completed (already pushed)

- `e0a0ec15f0c60d96dd320054e02c8309229e54ce` -- `perf(gui): carry browser text line widths`
- `248bf87` -- glyph fallback scan removal
- `c166d` -- backend preference lanes
- `97ed` -- DirectX backend order

## Current remaining work

1. Collect and record additional startup/render evidence (timing + throughput + parity)
   - Add evidence artifacts for the latest startup/render behavior in the same shape as existing perf evidence.
   - Update plan/spec references to point to the new evidence.
2. Provide GPU/font offload proof
   - Demonstrate measured proof of GPU/font offload path behavior or explicit typed unavailability.
   - Ensure evidence includes the decision path and fallback behavior.
3. Execute focused pure Simple GUI text/layout optimization pass
   - Target isolated hot-path opportunities in text layout, line width handling, and browser text path.
   - Keep changes small and attributable with before/after measurements.
4. Preserve app behavior
   - Keep rendering semantics and UI behavior unchanged while tuning performance.
   - Add or refresh regression checks if behavior drift risk is introduced by any micro-optimization.

## Near-term handoff priorities

- Update backend startup/render evidence set first.
- Capture GPU/font offload decision proofs second.
- Continue pure Simple text/layout optimization with explicit behavior-preservation checks.
