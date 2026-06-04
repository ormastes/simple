# Shared WM Renderer Unification System Test Plan

Date: 2026-05-29

## Scope

Verify the documented API convergence and size-baseline evidence without requiring optional local dependencies.

## Scenarios

1. Shared web render API parity: Web, Electron, Tauri, and pure Simple browser paths use `src/lib/common/ui/web_render_api.spl` request/artifact behavior.
2. Engine2D backend parity: CPU, Metal, and CUDA files expose `RenderBackend`; unavailable hardware reports capability state instead of false success.
3. WM service/core convergence: host and SimpleOS lifecycle behavior is covered by shared WM specs before host-specific adapter effects.
4. Qt size baseline: `scripts/check/check-qt-gui-size-baseline.shs` writes a report with `qt_status=unavailable` when Qt is missing and exits successfully.

## Focused Commands

- `sh scripts/check/check-qt-gui-size-baseline.shs`
- `SIMPLE_LIB=src bin/simple test test/unit/app/ui/web_render_backend_api_spec.spl --mode=interpreter`
- `SIMPLE_LIB=src bin/simple test test/unit/app/ui/backend_matrix_spec.spl --mode=interpreter`

## Evidence

Record report paths and test outcomes in `doc/09_report/` or the final verification response. Do not make Qt a normal CI prerequisite.
