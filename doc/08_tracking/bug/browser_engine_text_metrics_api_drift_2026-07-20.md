# browser_engine text-metrics spec: multiple real API gaps (missing fields/fn, nil SFFI)

**Status:** open
**Found:** 2026-07-20 (whole-suite triage campaign, test/01_unit shard)
**Area:** `src/lib/gc_async_mut/gpu/browser_engine/**` (contested GPU/browser-engine area)

## Symptom

`test/01_unit/app/ui.chromium/text_metrics_spec.spl` fails 13 of 14 examples
with 4 distinct root causes (not one migratable rename):

1. **Missing struct field** `content_x` on `BeLayoutBox`
   (`src/lib/gc_async_mut/gpu/browser_engine/layout_box.spl:12`) — confirmed
   by reading the class definition: it has `x`, `y`, `width`, `height` plus
   margin/padding/border fields, but no `content_x` (content-area x after
   padding+border offset). 5 examples fail with
   `semantic: class 'BeLayoutBox' has no field named 'content_x'`.

2. **Missing struct field** `warnings` on `BeRenderResult`
   (`src/lib/gc_async_mut/gpu/browser_engine/browser_renderer.spl:15`) —
   confirmed: fields are `pixels, pixel_data, width, height, title,
   source_html, ok, error, scene, node_count`, no `warnings`. 1 example:
   `semantic: class 'BeRenderResult' has no field named 'warnings'`.

3. **Missing function** `browser_render_vector_font_probe_pixels` — 1
   example: `semantic: function 'browser_render_vector_font_probe_pixels'
   not found`.

4. **`nil.trim()`** — 6 examples fail with `semantic: method 'trim' not
   found on type 'nil' (receiver value: nil)`, all in SFFI TTF
   renderer/layout tests (font metrics, glyph bearing, subpixel coverage,
   line-width corpus). Consistent with a font/SFFI resource (e.g. a TTF
   file path or font-lookup result) returning `nil` in this environment,
   then `.trim()` being called on it unconditionally.

## Why this is GENUINE-BUG, not STALE-TEST

Each of (1)-(3) is a genuine, non-trivial gap between the spec's expected
API surface and the actual `BeLayoutBox`/`BeRenderResult`/module-fn
implementation — not a renamed/moved symbol. Migrating the spec to use `.x`
instead of `.content_x`, for example, would silently change what's being
asserted (content-box origin vs border-box origin) rather than fix a stale
reference, which the campaign rules classify as weakening, not a fix.
(4) looks environment/resource-dependent (likely missing TTF font asset or
SFFI font-loader unavailable in this sandbox) layered on browser-engine
work already flagged contested in this campaign.

## Minimal repro

```
SIMPLE_RUST_SEED_WARNING=0 timeout 90 \
  /home/ormastes/dev/pub/simple/bin/release/x86_64-unknown-linux-gnu/simple \
  test test/01_unit/app/ui.chromium/text_metrics_spec.spl --no-session-daemon
```

## Affected specs seen this shard

- `test/01_unit/app/ui.chromium/text_metrics_spec.spl` (13 of 14 examples,
  4 distinct root causes as above)
