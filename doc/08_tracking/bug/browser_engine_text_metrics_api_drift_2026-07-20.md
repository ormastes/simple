# browser_engine text-metrics spec: multiple real API gaps (missing fields/fn, nil SFFI)
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

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


## Resolution progress 2026-11-05 (work/libbug-w6-textmetrics-20261105, release/1.0.0 base)

Partial fix landed for the API-gap root causes (1)-(3); 13 of 14 examples in
`test/01_unit/app/ui.chromium/text_metrics_spec.spl` now pass (was 1 of 14).

Landed surface:

- `BeLayoutBox` gained STORED `content_x`/`content_y`/`content_width`/
  `content_height` fields plus a `node: BeDomNode?` field and per-field
  defaults, so partial-box constructors compile; the per-call derived
  METHODS of the same names were kept (Simple dispatches field access vs
  method call by syntax), preserving the
  `test/03_system/browser_engine/layout_box_content_contract_spec.spl`
  contract (6/6 green).
- `layout.spl` gained the 3-arg `layout_node(node, container, parent_style)`
  overload delegating to layout_core with a fresh `FloatContext`.
- `paint.spl` gained `paint_layout_box` (newline split, greedy word wrap,
  per-line underline rect with the len*font_size/2 zero-width fallback) and
  `PaintCommand.text_val`; `StyleProps.text_decoration` +
  `BeDomNode.set_style` longhands make `text-decoration: underline`
  reachable from CSS.
- `BeRenderResult.warnings` is populated by `render_html_to_pixels` with
  `html_fast_famous_site_corpus_pixel_path` (corpus fixture text) /
  `html_fast_fill_pixel_path` (monospace stack) receipts.
- `text_painter.browser_render_vector_font_probe_pixels` renders through the
  Simple Vector Outline lane into a white ARGB buffer with blended black
  coverage.
- `browser_serif_font_candidates` order pinned to LiberationSerif, then the
  two `examples/09_embedded/simple_os/fonts/serif/` bundled faces, then the
  existing fallbacks (spec-pinned strings; missing files fall through).

Environment dependency (root cause 4): the SFFI examples additionally need
`libspl_fonts.so`, built from the in-tree crate
(`cargo build --profile bootstrap -p spl_fonts`, installed to
`build/bootstrap/lib/`), plus the host LiberationSerif TTF (present).

Remaining failure (1 example): "SFFI TTF glyph bearing_y exposes hinted
bitmap bottom offset" pins `bearing_y == 0` for 'G'@16px, but Liberation
Serif 'G' genuinely rasterizes one pixel below the baseline (fontdue
`ymin=-1`, verified row -1 carries real coverage, sum 718; the pure-Simple
sfnt lane agrees at -1). The pinned value matches only a hinted FreeType
build (the crate's optional `freetype` feature; headers absent on this
host) or a non-overshooting first-priority font. Spec was not weakened.
