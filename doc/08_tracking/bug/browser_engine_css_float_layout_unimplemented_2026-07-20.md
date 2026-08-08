# browser_engine: CSS `float`/`clear` layout produces no visible geometry (all-zero pixel counts)

**Status:** open
**Found:** 2026-07-20 (whole-suite triage campaign, test/01_unit shard)
**Area:** `src/lib/gc_async_mut/gpu/browser_engine/**` (contested GPU/browser-engine area;
related to `browser_engine_text_metrics_api_drift_2026-07-20.md` filed same shard)

## Symptom

`test/01_unit/lib/gc_async_mut/gpu/browser_engine/float_layout_spec.spl` fails
11 of 18 examples. Every failure is either:

- `expected 0 to be greater than 0` (a colored-pixel region count that should
  be positive comes back 0), or
- `expected 384 to equal 0` (a `display:none` box that should render nothing
  still occupies area)

Representative case (`describe "CSS float placement"`,
`it "float:right renders colored box at right edge"` and siblings):

```
val html = "<html><body ...><div style='width:40px;height:40px'>
  <div style='float:left;width:20px;height:20px;background:#ff0000'></div>
</div></body></html>"
val pixels = render_html_to_pixels_with_viewport(html, VW, VH).pixel_data
expect(_count_region_color(pixels, VW, 0, 0, 20, 20, 0xFFFF0000u32))
    .to_be_greater_than(0)
```

The rendered pixel buffer never contains the expected colored region for any
float-related layout (`float:left`, `float:right`, two floats side by side,
`clear:both`, `clear:left`, in-flow content narrowing beside a float,
`overflow:hidden`/`display:flow-root` height-enclosing a float, non-
overlapping left/right floats) — 11 distinct float/clear scenarios all
return 0 painted pixels in the expected region. One `display:none` case
paints 384 pixels where it should paint 0 (element should not render at
all). Only `float wraps to next line when container is too narrow` passes.

## Assessment

This is consistent with CSS `float`/`clear` positioning being unimplemented
(or a no-op) in the browser_engine layout pass — not a renamed API or a
migratable spec issue. All 11 failures share the identical "expected N > 0,
got 0" signature, i.e. floated boxes never get painted at their expected
offset. This sits in the same contested `gpu/browser_engine` module already
flagged this shard for `text_metrics_spec.spl` (missing `content_x`,
`warnings` fields, missing font-probe function) — likely reflects a
still-in-progress DrawIR/browser-engine layout feature area rather than a
regression.

## Minimal repro

```
SIMPLE_RUST_SEED_WARNING=0 timeout 90 \
  /home/ormastes/dev/pub/simple/bin/release/x86_64-unknown-linux-gnu/simple \
  test test/01_unit/lib/gc_async_mut/gpu/browser_engine/float_layout_spec.spl \
  --no-session-daemon
```

## Affected specs seen this shard

- `test/01_unit/lib/gc_async_mut/gpu/browser_engine/float_layout_spec.spl`
  (11 of 18 examples)
