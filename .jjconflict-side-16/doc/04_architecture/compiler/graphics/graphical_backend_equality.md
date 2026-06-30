# Graphical Backend Equality — Architecture

Date: 2026-06-03

## Layering

The first slice adds a test-facing `wm_compare` contract above existing
renderer and compositor comparison helpers.

- Existing low-level comparison remains in `src/os/compositor/screenshot_compare.spl`.
- Existing tolerance profiles remain in `src/os/compositor/tolerance_profile.spl`.
- New `src/app/wm_compare/graphical_backend_equality.spl` owns backend selector
  parsing, normalized capture metadata, and equality report classification.
- New `src/lib/gc_async_mut/gpu/browser_engine/backend_screenshot_capture.spl`
  repairs the test-facing capture facade for browser-rendered pixels and
  Engine2D readback, including quality metrics and repeated-capture performance
  evidence.
- Future Engine2D adapters should feed real `RenderBackend`/`Engine2D`
  readback into this contract instead of adding another comparison vocabulary.

## Boundaries

This slice does not touch native GPU kernels, Electron capture scripts, Tauri
shells, or production renderer hot paths. It creates a stable test facade that
those paths can feed later.

## Failure Model

Reports are ordered by evidence strength:

1. backend selector/capability status;
2. capture status;
3. metadata and geometry status;
4. pixel comparison status;
5. shape/color diagnostic status;
6. final acceptance status.

This preserves the existing `wm_compare` principle that capture and metadata
failures are not hidden behind a raw pixel mismatch.
