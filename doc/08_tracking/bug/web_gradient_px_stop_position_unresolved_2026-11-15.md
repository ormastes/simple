# Web renderer: `linear-gradient` stop positions in `px` are ignored (both lanes)

Status: FIXED (2026-11-22 — per-line `px`/`em` stop resolution via `parse_gradient_stops_on_line` verified across both Draw IR and CPU raster lanes and pinned against Chrome 159 in `linear_gradient_angle_draw_ir_chrome159_spec.spl`). Found 2026-11-15 on `work/engine2d-lane-parity-20261115`.

## Repro

`linear-gradient(to right, #ff0000 20px, #0000ff 180px)` on a 200x100 box,
`body{margin:0;background:#fff}`, window 200x400 (box at y 200..299).
Chrome 159.0.8154.6 `chrome-headless-shell`, `--force-device-scale-factor=1`:

| x   | Chrome 159 | cpu_simd (fb raster) | Draw IR (`software`) |
|-----|------------|----------------------|----------------------|
| 0   | #ff0000    | #ff0000              | #ff0000              |
| 19  | #ff0000    | #e60019              | #e70018              |
| 20  | #fe0000    | #e5001a              | #e60019              |
| 60  | #be0040    | #b2004d              | #b3004c              |
| 100 | #7e0080    | #7f0080              | #7f0080              |
| 140 | #3f00c0    | #4c00b3              | #4c00b3              |
| 180 | #0000ff    | #1900e6              | #1900e6              |

Both lanes paint the ramp as if the stops sat at 0% and 100%: about 24
levels off at x = 19 and x = 180.

## Cause

`gradient_stop_position_or_neg1`
(`src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_foundation.spl`)
turns a stop into permille at CSS-apply time. A `px` position needs the
gradient line length, which is only known when the box is painted, so it
falls back to "unpositioned" (evenly spaced).

## Fix direction

Carry px stops through the Style as a separate (length, unit) list and resolve
them against `|w sin a| + |h cos a|` where the line length is computed: the fb
raster's `fb_linear_gradient_general_clip` and Engine2D's
`emu_draw_linear_gradient_stops`. The parse side is in `browser_engine/**`,
which another lane was editing on 2026-11-15, so it was not changed here.
`test/01_unit/browser_engine/linear_gradient_angle_draw_ir_chrome159_spec.spl`
carries the box in its PAGE4 but does not assert it; add the rows above when
this is fixed.
