# FR: Draw IR inspection contract (Protocol v2)

- **Date filed:** 2026-07-06
- **Status:** Covered by existing tests (added for traceability only — see
  `scripts/check/cert/check-req-traceability.shs`)

## Summary

`ui.test_api` exposes a Protocol-v2 draw-IR inspection surface alongside the
existing v1 element endpoints. The requirements below are the minimal set
already exercised by
`test/03_system/app/ui_test_api/feature/draw_ir_inspection_contract_spec.spl`.

## Requirements

- REQ-DRAW-INSPECT-001: Protocol-v2 endpoint surface — draw-ir route handling
  is added to `ui.test_api`, advertised separately from the v1 API, and
  guarded behind an explicit capability.
- REQ-DRAW-INSPECT-002: producer enrichment — WM and web Draw IR are
  enriched with hit/clip rectangles, z-index style, and computed style/box
  rectangles.
- REQ-DRAW-INSPECT-003: `expect_draw` helper — exposed from the UI test
  helper layer, usable inside normal `std.spec` scenarios, and covers
  geometry, hit-rect, css, parent, and kind assertions.
- REQ-DRAW-INSPECT-004: v1 compatibility guardrails — Protocol v2 is
  documented without replacing v1 element endpoints, an empty source does
  not satisfy the endpoint contract, and a synthetic Protocol v2 header
  marker is detected.
