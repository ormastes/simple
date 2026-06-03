# Graphical Backend Equality — Detail Design

Date: 2026-06-03

## Data Model

- `GraphicalBackendSpec`: raw spec, primary kind/name, chain count, validity,
  and parse reason.
- `SurfaceRect`: integer rectangle for content, panel, and outer-window data.
- `SurfaceGeometry`: logical size, physical size, scale factor, rect metadata,
  scroll offset, and color space.
- `GraphicalCapture`: backend, capture kind, pixel buffer, physical dimensions,
  geometry, success flag, error, and artifact paths.
- `RenderCase`: canonical drawing case metadata for shared fixtures.
- `GraphicalEqualityReport`: backend/capture/metadata/pixel/shape/color
  statuses, comparison metrics, acceptance policy, and artifact links.

## Algorithms

Selector parsing validates the primary component before any `+` chain. Capture
validation checks positive dimensions, valid scale, known capture kind, and
pixel buffer length. Equality comparison fails closed on invalid capture or
metadata, then delegates pixel comparison to `compare_with_profile`.

Shape and color fields are diagnostic classifications in this first slice:
exact pixel equality reports `shape_status="pixel_proxy_match"` and
`color_status="pixel_proxy_match"`; threshold-only matches report
`pixel_proxy_tolerated`; failures report `pixel_proxy_mismatch`.

## First Slice Tests

`test/system/wm_compare/graphical_backend_equality_spec.spl` covers selector
parsing, metadata validation, exact equality, tolerance diagnostics, mismatch
classification, backend unavailability separation, and SDN report content.

`test/integration/rendering/graphical_backend_capture_spec.spl` covers the
render-side capture facade, including browser-rendered pixels, Engine2D
filled-rect readback, and feeding captured pixels into the `wm_compare`
graphical equality report.
