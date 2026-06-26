# Graphical Backend Equality Quality/Perf Evidence

Date: 2026-06-03

## Scope

Quality continuation for the graphical backend equality slice. This report
records actual drawing checks and performance evidence added after the initial
common contract landed.

## Quality Fixes

- Composed selectors now validate every backend component in
  `gui:electron+wm:host` style specs.
- Capture metadata now fails closed for empty color space, out-of-bounds content
  rectangles, out-of-bounds panel rectangles, invalid outer-window rectangles,
  invalid dimensions, invalid scale factor, and bad pixel counts.
- `BackendCapture` now records pixel checksum, non-background pixel count,
  sampled color diversity, and elapsed capture time.
- Engine2D filled-rect capture is checked for actual drawing content:
  non-background pixels must be present, the frame must not be entirely
  non-background, and sampled color diversity must exceed one.

## Perf Evidence

`benchmark_engine2d_filled_rect_capture(16, 12, "cpu", 8)` is covered by
`test/02_integration/rendering/graphical_backend_capture_spec.spl`. It records:

- `iterations: 8`
- `pixels_per_iteration: 192`
- `aggregate_checksum > 0`
- `total_us >= 0`
- serialized SDN containing `backend_capture_perf_report`

Focused run result:

- `test/03_system/wm_compare/graphical_backend_equality_spec.spl`: 8 passed, 0 failed.
- `test/02_integration/rendering/graphical_backend_capture_spec.spl`: 4 passed, 0 failed.

## Sync Evidence

`jj git fetch` failed on this host with:

```text
git@github.com: Permission denied (publickey).
fatal: Could not read from remote repository.
```

No rebase or push was attempted.
