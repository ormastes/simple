# HTML Compat Fixture 18 Live Source-B Timeout

- **Status:** open
- **Date:** 2026-06-11
- **Lane:** Simple Web / Chromium HTML pixel parity

## Summary

`18_flex_grow_weights` is present in the HTML compat catalog and has checked-in
Chrome/Simple PPM baselines plus an exact `report.sdn`, but a fresh live run of
the source-B Simple renderer path currently times out before producing the
Simple PPM.

## Reproduction

```sh
SIMPLE_LIB=src bin/simple run src/app/wm_compare/html_compat.spl --only=18_flex_grow_weights
```

Observed result on Linux:

```text
[html_compat] Chromium golden <-> Simple — 23 fixtures, 320x240
[html_compat] Fixture: 18_flex_grow_weights
[html_compat]   loading source A (checked-in Chromium golden)...
[html_compat]     ok  pixels=76800
[html_compat]   capturing source B (Simple browser engine)...
[html_compat]     fail: timed out after 20000 ms while rendering source B in child process
[html_compat]   RESULT: simple capture failed
```

The command exits with code `2`.

## Notes

Do not fix this by adding a compact marker that bypasses the pure Simple render
path or by copying Chromium pixels into the Simple side. A valid fix must still
execute the Simple layout/raster path for the fixture, then serialize or compare
the resulting pixels within the harness timeout.

Likely areas to inspect:

- `src/app/wm_compare/simple_html_capture_worker.spl`
- `src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer.spl`
- `src/app/wm_compare/html_compat_part1.spl`

## Acceptance Criteria

- The reproduction command exits `0` without increasing blur/tolerance.
- `test/09_baselines/html_compat/18_flex_grow_weights/report.sdn` records
  `simple: (capture success: true ...)`.
- The compare row remains exact: `exact: true`, `different_pixels: 0`,
  `match_pct_10000: 10000`.
