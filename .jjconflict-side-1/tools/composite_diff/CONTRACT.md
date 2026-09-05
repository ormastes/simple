# Chrome ↔ Simple compositing-stage I/O contract (stage 6)

This is the fourth stage of the per-component Chrome↔Simple differential. It
is **not** a whole-page pixel comparison, and it is one level below
`tools/paint_diff`. Each stage fixes an *input* both engines receive and
compares the *output* each engine's own instrumentation reports for that
stage.

| stage | tool | chrome oracle | simple oracle |
|-------|------|---------------|---------------|
| 1–2 DOM + cascade | `tools/web_diff` | `DOMSnapshot.captureSnapshot` computed styles | `parse_html` → `compute_styles` |
| 3–4 layout + text  | `tools/layout_diff` | snapshot `bounds` + `textBoxes` | `layout` box tree + wrap cache |
| 5 paint            | `tools/paint_diff` | `LayerTree.snapshotCommandLog` | `simple_web_layout_render_html_draw_ir` → `DrawIrComposition` |
| **6 compositing**  | **`tools/composite_diff`** | **`LayerTree.layerTreeDidChange` + `LayerTree.compositingReasons`** | **`DrawIrComposition.batches`** |

## Why compositing, not raster/tiling

The candidates considered were (a) layer structure/promotion reasons and
(b) tile/raster decisions. Raster tiling (`LayerTree.pictureAsData`, tile
sizes) is **two** stages below paint — it depends on a layerization decision
that doesn't exist on the Simple side yet, so a tile-level comparison would
be comparing an artifact Simple cannot produce at all. Layerization is the
narrower, betterfounded next stage: it is the decision paint (stage 5)
already depends on (paint ops are recorded *per layer*), and Chrome exposes it
directly as a named, stable API (`compositingReasons`) rather than an
internal heuristic that would need to be reverse-engineered from pixels.

## What this stage actually found

**Simple has no layerization pass.** `src/lib/cc/entity/layer.spl` and
`layer_tree_host.spl` define `Layer` / `LayerTreeHost` classes, but nothing in
`src/lib/gc_async_mut/gpu/browser_engine/**` ever constructs one — `git grep`
for `LayerTreeHost`/`LayerTreeImpl`/`cc.entity.layer` outside `src/lib/cc/`
and its own unit specs (`test/01_unit/lib/cc/*`) returns nothing. The web
renderer's `DrawIrComposition` always has exactly **one** batch
(`html-layout-0`) holding every component, regardless of `will-change`,
`transform`, `position: fixed`, animations, or anything else that makes Chrome
promote an element to its own layer. This is a `src/lib` gap; per the task
scope (`tools/**`, `test/**`, `doc/**` only) it is **reported, not fixed**.

Because of that gap, this stage measures two separable things instead of one:

1. **Unit-count** — does Simple produce more than one compositing unit at all
   when Chrome does? (Always no, currently — see finding `no-layerization`.)
2. **Trigger-property survival** — for each Chrome promotion reason, does the
   *CSS property that drives it* even reach Simple's Draw IR? This separates
   two different defects that a bare "Simple didn't layerize" verdict would
   conflate:
   - `trigger-property-absent`: the property never reaches the Draw IR at
     all (style plumbing gap) — e.g. `transform`, `position`, `opacity`,
     `overflow-x/y` are **not** in Simple's `COMPOSITING_PROPS` output at all.
   - `trigger-property-inert`: the property IS carried on the component
     (e.g. `will-change: transform`, `z-index`, `transform-style`,
     `animation-name`) but nothing downstream layerizes on it.

## Input (identical to both engines)

* one fixture from `fixtures/*.html`, loaded from `file://`
* viewport `800×600` css px, `deviceScaleFactor: 1`
* 18 fixtures, each isolating one compositing trigger (`will-change`,
  `transform: translateZ`, 3D transform, `position: fixed`,
  `position: sticky`, `overflow: scroll`, opacity/transform animations,
  `preserve-3d`, two/nested promoted siblings, `z-index` alone (negative
  control — z-index without a compositing trigger does NOT promote in
  Chrome), static `opacity` alone (negative control), overlap-induced
  promotion, `backface-visibility: hidden`, `will-change: scroll-position`)

## Output (canonical compositing model)

### Chrome lift (`chrome_composite_dump.js`)

```
{ layer_id, parent_id, role, x, y, w, h, draws_content,
  compositing_reasons: [name, ...], transform?, scroll_rects, sticky? }
```

`role` is `element` or one of the four `scaffold_*` kinds. Chrome unconditionally
emits **four scaffolding layers** for any ordinary document — an anonymous 0×0
root, the root scroll container, the root scrolling-contents layer (tagged
`RootScroller`), and the visual viewport layer (tagged `Viewport`) — that
describe the *frame*, not any element. Counting them as "layers Simple is
missing" would inflate every fixture by a constant 4 and drown the real
signal, so `classifyLayer()` strips them before the element-level comparison.
See the classifier's own comment in `chrome_composite_dump.js` for the exact
rule and why the root-scroll-container clause is narrow enough not to also
strip an *element's own* `overflow: scroll` container (verified against
`08_overflow_scroll`, which correctly keeps its 200×100 scroll layer as an
element).

Every element layer's `x, y` from `LayerTree` is `0, 0` — a promoted layer
gets a fresh transform-node origin, not a page position — so the differ
matches Chrome layers to Simple components by **size** (`w`, `h`), not
position. Page position is already gated by `tools/layout_diff`.

### Simple lift (`simple_composite_dump.spl` + `composite_diff.js`)

`simple_web_layout_render_html_draw_ir(html, w, h)` returns a
`DrawIrComposition` of `batches` of component commands. A **batch** is
Simple's only unit of independently-submitted backend work, and therefore the
closest existing counterpart to a composited layer — so
`simple_units = batches.len()` is what's compared against
`chrome_element_layers + 1` (the `+1` is the always-present root unit both
sides agree on). Every component additionally carries a `triggers` object: the
subset of its `computed_style` that is a CSS property capable of driving
compositing (`COMPOSITING_PROPS` in `simple_composite_dump.spl` — the full
candidate set, not just what Simple happens to emit, so an absent key is
itself a recorded finding).

## Two extractor facts inherited from `tools/paint_diff` — still load-bearing here

Both fail *silently* — an empty layer list is indistinguishable from perfect
agreement:

1. **`--disable-gpu` yields zero layers.** Compositing must stay on.
2. **`LayerTree.enable` must be sent once, after a first real paint,** and the
   layer list read off the persistent `LayerTree.layerTreeDidChange` event.

This stage adds a third failure mode of its own, also silent unless checked:
**a fixture whose Chrome side has zero `element` layers after scaffolding is
stripped** reads exactly like "Simple matched perfectly" when it actually
means "this fixture never exercised the compositor." Fail-closed responses:

* the Chrome extractor exits nonzero if *any* fixture classifies with zero
  scaffolding at all (`layers.length === elements.length`) — that means the
  classifier itself broke, not that the page is simple;
* the Chrome extractor exits nonzero (`FATAL`) if the run-wide total of
  element promotions is 0 — the fixture set exists specifically to produce
  promotions, so zero across all 18 means the launch flags regressed;
* the differ additionally reports `distinct_compositing_reasons` in the
  summary, so a fixture set that degenerated to testing only one trigger is
  visible even though it would still "pass".

## Epsilon

`1` css px on layer/component size matching. `compositing_reasons` and
`triggers` are compared **exactly** as strings — a promotion decision is
discrete, not a measurement.

## Known modelling caveats

* **`no-reason` promotions.** `translateZ(0)` promotes in Chrome
  (`04_translate_z`) with an empty `compositingReasonIds` array in this Chrome
  build — Chrome's CDP surface does not always name every promotion path.
  Reported as `chrome=no-reason` rather than silently dropped.
* **`Overlap`-only promotions have no CSS trigger.** `06_position_fixed` and
  half of `07_position_sticky`/`08_overflow_scroll`/`16_overlap_promoted`
  promote because of *geometric* overlap with another promoted layer, not
  because of a property on the element itself. `REASON_TRIGGER['Overlap'] =
  null` and the differ skips the trigger-property check for those, so it
  never asserts a `position: fixed` → `trigger-property-*` finding that
  would actually be about `Overlap`, not about `position`.
* **Two negative-control fixtures are load-bearing, not filler.**
  `14_z_index_only` and `15_static_opacity` isolate `z-index` and `opacity`
  *without* a compositing trigger; Chrome promotes neither. Their presence is
  what proves the fixture set isn't just "everything promotes" — removing them
  would make `distinct_compositing_reasons` unfalsifiable.

## Simple text-literal trap

Same defect as `tools/paint_diff`: `"body{margin:0}"` written as a Simple text
literal parses `{margin:0}` as string interpolation and fails with
``variable `margin` not found``. Fixtures are read from files, never embedded.
A literal `}}` also collapses to a single `}` (the brace-escape pairing with
`{` interpolation); closes are routed through the `RB` constant in
`simple_composite_dump.spl`.
