# Feature Request: Engine2D Facade Must Preserve Backend Pixel Mutations

Date: 2026-06-02
Status: open
Area: Engine2D, render backends, web renderer parity

## Problem

Backend-executed parity evidence found that direct concrete backends preserve
drawn pixels, but the generic `Engine2D` facade path can lose pixel mutations
when drawing through the `RenderBackend` trait field.

The reduced scene:

- clear `0xFF102030`
- filled rect `0xFF010204`

passes exact parity when driven directly through:

- `SoftwareBackend`
- `CpuBackend`
- `MetalBackend`

The same scene driven through `Engine2D.create_with_backend(...).backend`
returned opaque black for software and CPU SIMD pixels while Metal direct
readback returned the expected colors.

## Expected Behavior

`Engine2D` should be the canonical production facade. Drawing through
`Engine2D.clear`, `Engine2D.draw_rect_filled`, `Engine2D.present`, and
`Engine2D.read_pixels` must produce the same pixels as the concrete backend.

## Required Fix

Refactor `Engine2D` so backend state mutations cannot be lost behind trait-field
dispatch. Acceptable approaches:

- Store concrete backend variants explicitly and dispatch through typed fields.
- Introduce a boxed/reference backend model with proven mutation semantics.
- Add a generated backend enum wrapper if that matches Simple language limits.

## Acceptance Criteria

- A spec proves `Engine2D.create_with_backend(16, 16, "software")` preserves
  clear and filled-rect colors.
- A spec proves `Engine2D.create_with_backend(16, 16, "cpu_simd")` preserves
  the same colors and records SIMD hits.
- On macOS, a spec proves `Engine2D.create_with_backend(16, 16, "metal")`
  returns exact pixels from GPU readback for the reduced scene.
- The web renderer backend parity harness can use `Engine2D` directly without
  falling back to direct concrete backend calls.

## Notes

This is not a request to hardcode web-rendered pixels. The final renderer path
must remain HTML/CSS-driven and backend-selectable.
