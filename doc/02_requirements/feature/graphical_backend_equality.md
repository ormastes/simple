# Graphical Backend Equality — Feature Requirements

Date: 2026-06-03

Selected scope: Feature Option B, Engine2D + WM unified test facade.

## Requirements

- REQ-001: Provide a common test-facing graphical backend selector for
  `2d:*`, `web:*`, `gui:*`, and `wm:*` backends, including composed specs such
  as `gui:electron+wm:host`.
- REQ-002: Provide a normalized capture metadata model that records logical
  size, physical size, scale factor, capture kind, color space, content rect,
  panel rect, and optional outer window rect.
- REQ-003: Provide a graphical equality report that separates backend
  selection, capture failure, metadata mismatch, pixel/shape/color diagnostic
  status, and acceptance policy.
- REQ-004: Reuse existing pixel comparison and tolerance profile helpers before
  adding new image-processing algorithms.
- REQ-005: Make the first implementation slice usable from `wm_compare` specs
  and suitable for later Engine2D readback adapters.
- REQ-006: Do not claim GPU/backend parity from fixture-only comparisons; real
  backend readback must be identified separately in reports and tests.

## Traceability

- `doc/01_research/ui/graphical_backend_equality.md`
- `doc/03_plan/graphical_backend_equality.md`
- `test/03_system/wm_compare/graphical_backend_equality_spec.spl`
