# Blink paint pipeline wiring — `StyledLayout` → paint output

Status: RESEARCH ONLY. No implementation in this doc.

## 0. Context

Landed 2026-08-09 (`c28e1b008b02`): DOM (`src/lib/blink/dom/node.spl`), CSS
selector engine (`src/lib/blink/css_parser/selector.spl`), cascade
(`src/lib/blink/style/cascade.spl`), HTML tree builder/tokenizer
(`src/lib/blink/html_parser/*`), and the style→layout bridge
(`src/lib/blink/layout/style_bridge.spl`) proved end-to-end by
`test/01_unit/lib/blink/render_lane_pipeline_spec.spl` (7/7): HTML+CSS string
in → correct laid-out `StyledLayout` out. `style_bridge.spl`'s own header
states painting is a deliberate non-goal ("No paint and no rasterisation...
turning that into pixels is a separate lane").

This doc scopes exactly that separate lane: `StyledLayout` → `[PaintChunk]`,
and separately, whether an existing rasterizer can consume the result.

## 1. Paint-type census

`/usr/bin/grep -rln 'paint_artifact\|paint_chunk\|PaintChunk\|PaintArtifact' src/`
(excluding vendored/build-output noise under `src/compiler_rust/target/**` and
`src/app/vscode_extension/.vscode-test/**`) hits exactly these production
files:

- `src/lib/blink/entity/paint_artifact.spl`
- `src/lib/blink/entity/paint_chunk.spl`
- `src/lib/common/ui/render_opt/draw_ir_delta.spl`
- `src/lib/common/ui/render_opt/paint_chunk_rasterizer.spl`
- `src/lib/common/ui/render_opt/property_trees.spl`
- `src/lib/common/ui/render_opt/revisions.spl`
- `src/lib/common/ui/render_opt/web_style.spl`
- `src/lib/content/entity/web_contents.spl`

There are **two independent `PaintChunk` definitions** — census both, they are
NOT interchangeable:

### 1a. `src/lib/blink/entity/paint_chunk.spl` (blink-native, index-range only)

```
struct PropertyTreeState: transform_id, clip_id, effect_id, scroll_id: i64
struct PaintChunkId: owner_node_id, display_item_index: i64
class PaintChunk:
    begin_index, end_index: i64
    id: PaintChunkId
    property_state: PropertyTreeState
    bounds: SkRect          # left/top/right/bottom, from std.skia.entity.geometry
    is_cacheable: bool
fn paint_chunk_new(begin_index, end_index, id, property_state, bounds) -> PaintChunk
```
Pairs with `src/lib/blink/entity/paint_artifact.spl`'s `PaintChunkProperties`
(a simpler 3-field transform/clip/effect record) and `PaintArtifact { items:
[DisplayItem], chunks: [PaintChunk] }` where `DisplayItem { op: PaintOp,
z_index: i64 }` (`src/lib/common/render_scene/paint_types.spl:28`). This
family has **no consumer** — it exists as typed scaffolding for a full
display-item-list paint pass (multiple items per chunk, property-tree
threading) and nothing walks it into pixels or even reads it.

### 1b. `src/lib/common/ui/render_opt/paint_chunk_rasterizer.spl` (flat rect+colour, HAS A CONSUMER)

`PaintChunkRects` (own class, deliberately NOT columns on the shared
`PaintChunks` cache in `property_trees.spl` — "keeps property_trees.spl free
of any pixel-format opinion"):
```
class PaintChunkRects:
    rect_x, rect_y, rect_w, rect_h: [i64]
    colour: [i64]          # packed ARGB i64, one entry per chunk index
    rect_count: i64
    static fn create() -> PaintChunkRects
    me add_rect(x, y, w, h, argb: i64) -> i64     # returns pushed index
```
Indices in `PaintChunkRects` must line up 1:1 with the matching
`PaintChunks.add_chunk*` calls in `property_trees.spl`.

`ChunkRasterBuffer` — owned, non-aliased `[u32]` pixel storage (explicitly
never `get_pixel_buffer()`, to avoid the live-alias hazard documented in the
module header re: `src/os/compositor/compositor.spl`).

`paint_chunk_rasterizer_run(chunks: PaintChunks, rects: PaintChunkRects,
trees: PropertyTrees, revs: RenderRevisions, buf: ChunkRasterBuffer,
component_gen, theme_rev, scale_rev, viewport_gen, capability_gen: u32) ->
RasterStats` — walks `chunks`, computes per-chunk staleness against
`revisions.spl`/`property_trees.spl` revision counters, and for every dirty
chunk index calls `paint_rect(buf, rects.rect_x[idx], rects.rect_y[idx],
rects.rect_w[idx], rects.rect_h[idx], rects.colour[idx])`, which flat-fills via
`oracle_fill_const` (a STORE not a blend — correct for an opaque
background-color fill; matches `src/lib/common/gpu/engine2d/scalar_oracle`
ground truth). Skipped (non-dirty) chunks are left byte-for-byte untouched.

**This is a real, already-working, alias-safe rasterizer.** It is proven by
`test/01_unit/lib/common/ui/render_opt/paint_chunk_rasterizer_spec.spl`. It
consumes flat `(x, y, w, h, argb)` tuples and a `PaintChunks`/`RenderRevisions`
staleness-tracking pair — it does **not** know about `StyledLayout`,
`ComputedStyle`, or DOM nodes at all.

### 1c. `src/lib/common/ui/render_opt/property_trees.spl`

Owns `PaintChunks` (the staleness-tracking cache keyed by
`key_component_gen/key_grouping_rev/key_property_rev/key_theme_rev/
key_scale_rev/key_viewport_gen/key_capability_gen`, one column-array per key)
and `PropertyTrees`. `paint_chunks_raster(...)` computes `RasterStats`
(`rastered_count`/`skipped_count`). This layer is generation/revision
bookkeeping, not geometry or colour — the rasterizer reads `rects` (1b)
separately and in lockstep by index.

### 1d. `src/lib/common/ui/render_opt/{revisions,draw_ir_delta,web_style}.spl`,
`src/lib/content/entity/web_contents.spl`

Not directly load-bearing for this task; `revisions.spl` supplies
`revisions_chunk_grouping_rev` consumed by 1b above. `web_style.spl` and
`web_contents.spl` are content-layer plumbing with no `StyledLayout`
awareness — out of scope, note only.

## 2. Conclusion: which family to target, and why

Use family **1b** (`paint_chunk_rasterizer.spl`'s `PaintChunkRects` +
`ChunkRasterBuffer` + `paint_chunk_rasterizer_run`), NOT family 1a
(`blink/entity/paint_chunk.spl`'s `PaintChunk`/`PaintArtifact`).

Reasons:
- 1b already has a proven, alias-safe pixel consumer. 1a has zero consumers —
  targeting it would mean building the consumer too, which is explicitly a
  separate, larger task (see §5).
- 1b's shape (flat rect + packed ARGB colour) is an exact match for what
  `StyledLayout` can produce today: one axis-aligned rect (`b.computed_rect`,
  already `SkRect`-shaped: left/top/right/bottom) and one colour
  (`ComputedStyle.background_color: SkColor4f`, with a ready
  `to_sk_color() -> i64` packer at `src/lib/skia/entity/color.spl:62-67`).
  1a's `PaintChunk` wants a `[DisplayItem]` list and property-tree ids that
  nothing in the cascade/layout lane produces yet (transform/clip/effect
  trees do not exist in this lane — only flat block-flow boxes do).
- 1b is **spec-provable at the chunk-list level alone** — `PaintChunkRects` is
  inspectable data (`rect_x[i]`, `colour[i]`, ...), so a spec can assert on it
  directly with zero pixel output required, matching the "minimal deliverable"
  ask in §4 below.

The existing `PaintChunks`/`RenderRevisions` staleness machinery in
`property_trees.spl`/`revisions.spl` is **not required** for the minimal
deliverable — it is a damage-tracking optimization layer on top of a rect
list, orthogonal to producing the rect list correctly the first time. Do not
wire it in until a caller actually needs incremental re-paint; scope it out
explicitly (see §4).

## 3. `StyledLayout` — precise shape (from `src/lib/blink/layout/style_bridge.spl`)

```
class StyledLayout:
    context: LayoutContext         # src/lib/blink/layout/block_flow.spl
    node_ids: [i64]                # nodes that produced a box, index-parallel with styles
    styles: [ComputedStyle]        # src/lib/blink/entity/computed_style.spl

impl StyledLayout:
    fn style_for(node_id: i64) -> ComputedStyle?
    fn rect_for(node_id: i64) -> (f64, f64, f64, f64)?   # (left, top, right, bottom)
```

`node_ids[i]` / `styles[i]` are index-parallel (`i` is NOT a node id — walk
by index, not by `node_ids[i]` as an array subscript). `context.get_box(id)`
(via `rect_for`) is the authoritative source of computed geometry;
`context.boxes` is the underlying `[BlockFlowBox]` if a walker needs direct
iteration order instead of going through `node_ids`.

`ComputedStyle` (`src/lib/blink/entity/computed_style.spl:100-109`), the
properties cascade resolves tonight — **exactly these and no others**:
```
color: SkColor4f
background_color: SkColor4f
margin_left/right/top/bottom: Length
padding_left/top: Length          # padding_right/bottom NOT modeled (style_bridge.spl:29)
width/height: Length
```
No border, no `padding_right`/`padding_bottom` (cascade never resolves them —
`style_bridge.spl` line 29 already documents this and zeros them in
`BoxGeometry.spacing`), no text/font properties, no `display` beyond
`Display.None` skip. A background-only, geometry-only paint step must not
invent values for anything not in this list.

`SkRect` fields used: `left, top, right, bottom` (from `rect_for`'s tuple, or
`box.computed_rect` directly). Width/height in device pixels = `right-left`,
`bottom-top` — already resolved by block-flow layout, no re-derivation of
`Length.to_px()` needed at paint time.

## 4. Minimal spec-provable deliverable

**New file**: `src/lib/blink/paint/style_paint.spl` (new directory —
`src/lib/blink/paint/` does not exist yet; `src/lib/blink/layout/`,
`src/lib/blink/style/`, `src/lib/blink/entity/` are its siblings, so this
follows the existing per-concern layout of `src/lib/blink/*`).

Function signature:
```
use std.blink.layout.style_bridge.{StyledLayout}
use std.common.ui.render_opt.paint_chunk_rasterizer.{PaintChunkRects}

pub fn paint_chunks_from_styled_layout(layout: StyledLayout) -> PaintChunkRects
```

Body (pseudocode, index-parallel walk over `layout.node_ids`/`layout.styles`):
```
var rects = PaintChunkRects.create()
var i = 0
while i < layout.node_ids.len():
    val node_id = layout.node_ids[i]
    val style = layout.styles[i]
    match layout.rect_for(node_id):
        Some((l, t, r, b)):
            val argb = style.background_color.to_sk_color()
            rects.add_rect(l.to_i64(), t.to_i64(),
                           (r - l).to_i64(), (b - t).to_i64(), argb)
        None:
            pass_do_nothing()
    i = i + 1
rects
```
Explicit scope:
- IN: box rect (from already-computed `computed_rect`) + `background_color`
  only, packed via the existing `SkColor4f.to_sk_color()` — no new colour math.
- OUT (defer, do not implement here): border, text/glyph rendering (no font
  metrics anywhere in this lane), transparent-background skip-optimization
  (an alpha=0 rect is still emitted — correctness first, optimize later if a
  spec demands it), z-order/stacking-context sort (block-flow lane is a
  single flat list in document order already; do not add a sort until a spec
  needs one), and the `PaintChunks`/`RenderRevisions` staleness/damage-tracking
  wiring from `property_trees.spl` (orthogonal optimization layer, §2).
- No rasterization/PPM output in this step — `PaintChunkRects` is the
  deliverable, inspectable directly.

**New spec**: `test/01_unit/lib/blink/paint/style_paint_spec.spl` (mirrors
`src/lib/blink/paint/style_paint.spl`, same convention as
`render_lane_pipeline_spec.spl` living beside the modules it chains).

Spec should:
1. Build a small HTML+CSS document via the SAME entry points
   `render_lane_pipeline_spec.spl` already proves (tokenize→parse HTML,
   parse CSS, `build_styled_layout`) — e.g. one `<div>` with
   `background-color: red; width: 100px; height: 50px; margin: 10px;`.
2. Call `paint_chunks_from_styled_layout(layout)`.
3. Assert `rects.rect_count == 1` (or N for N boxes).
4. Assert `rects.rect_x[0]`, `rects.rect_y[0]` equal the box's laid-out
   `left`/`top` (from `layout.rect_for(node_id)`, cross-checked against the
   same values `render_lane_pipeline_spec.spl` already asserts for that
   geometry — do not recompute margins independently, reuse the proven
   numbers).
5. Assert `rects.rect_w[0] == 100`, `rects.rect_h[0] == 50` (width/height from
   CSS, unaffected by margin per box-model semantics already proven by
   block_flow).
6. Assert `rects.colour[0] == sk_color_argb(255, 255, 0, 0)` (red, opaque) —
   use the existing `sk_color_argb` helper from `src/lib/skia/entity/color.spl`
   as the oracle, not a hand-packed literal.
7. A second example with `display: none` on a child: assert that node
   contributes NO rect (rect_count does not grow) — proves the `None` branch
   in `rect_for` is handled, consistent with `style_bridge.spl`'s documented
   `display:none` skip.
8. A third example with `background-color` unset (default
   `computed_style_default()`'s `sk_color4f(0,0,0,0)`, fully transparent):
   assert the rect is still emitted with `colour[i] == 0` (alpha 0) — proves
   the "no skip-optimization" scope decision from above is actually what the
   code does, not just documented intent.

This is fully provable without touching pixels, `ChunkRasterBuffer`, or
`property_trees.spl` — the whole surface is arrays of ints.

## 5. Larger, separate task: rects → actual pixels

Not in scope for the minimal deliverable, but the path exists and should be
named so it isn't rediscovered from scratch:

`paint_chunks_from_styled_layout`'s output (`PaintChunkRects`) is
**already the exact input shape** `paint_chunk_rasterizer_run` consumes for
its `rects` parameter. The remaining wiring for actual pixel output is:
1. Construct a `ChunkRasterBuffer` sized to the viewport
   (`stride`/`height` from the same `viewport_width`/`viewport_height`
   already passed into `build_styled_layout`).
2. Either bypass `paint_chunk_rasterizer_run`'s staleness machinery entirely
   for a first pass (call `paint_rect` directly per rect — it's a free
   function in the same module) or construct a trivial always-dirty
   `PaintChunks`/`RenderRevisions`/`PropertyTrees` to drive
   `paint_chunk_rasterizer_run` for real damage-tracking behaviour.
3. `ChunkRasterBuffer.pixels: [u32]` is then a real ARGB framebuffer that
   could feed a PPM writer (grep for an existing one before writing a new
   one — not confirmed in this pass) or, per the task brief's hint, the
   SimpleOS WM/compositor lane (`src/os/compositor/compositor.spl`,
   `src/lib/gc_async_mut/gpu/engine2d/**`). **Not verified in this research
   pass**: whether `engine2d`'s compositor can take an externally-owned
   `[u32]` buffer as an input surface, or only ever writes its own. That is
   the next open question for whoever picks up this larger task — grep
   `src/lib/gc_async_mut/gpu/engine2d/` for a buffer-import / blit-from
   entry point before assuming either way.

## 6. Step-by-step implementation plan (for an agent with no other context)

1. Read `src/lib/blink/layout/style_bridge.spl` and
   `test/01_unit/lib/blink/render_lane_pipeline_spec.spl` in full — the new
   spec must reuse their exact HTML/CSS-string-to-`StyledLayout` entry point
   pattern, not reinvent it.
2. Read `src/lib/common/ui/render_opt/paint_chunk_rasterizer.spl` in full —
   confirm `PaintChunkRects.add_rect` signature and `use` path
   (`common.ui.render_opt.paint_chunk_rasterizer.{PaintChunkRects}` — check
   the module's own `use`/namespace declarations for the exact import
   string, matching how `style_bridge.spl` imports `block_flow`).
3. Read `src/lib/skia/entity/color.spl` in full for `SkColor4f.to_sk_color()`
   and `sk_color_argb` — confirm exact signatures before use.
4. Create `src/lib/blink/paint/` directory, add
   `src/lib/blink/paint/style_paint.spl` per §4's pseudocode. Handle `i64`
   casts on `f64` rect coordinates explicitly (`.to_i64()`); check whether
   negative coordinates are possible from block_flow (they should not be for
   this box model, but confirm — `paint_rect`'s own header in
   `paint_chunk_rasterizer.spl` references a real historical bug,
   `doc/08_tracking/bug/paint_rect_negative_x_row_bleed_2026-08-07.md`, about
   exactly this class of mistake).
5. Create `test/01_unit/lib/blink/paint/style_paint_spec.spl` per §4's 8
   assertions (adjust count/shape once the HTML/CSS fixture is finalized;
   keep at minimum: single-box rect+colour, `display:none` skip, and
   transparent-background non-skip).
6. Run `bin/simple test test/01_unit/lib/blink/paint/style_paint_spec.spl`
   (per `.claude/rules/commands.md`, no build needed — `src/lib/**` is read
   as source every run).
7. Do NOT touch `paint_chunk_rasterizer.spl`, `property_trees.spl`, or
   `revisions.spl` in this step — they are the input contract, not something
   this change modifies. If `PaintChunkRects.add_rect`'s signature doesn't
   match what's documented in §1b (re-verify — this doc is a snapshot),
   STOP and file a bug rather than changing the shared rasterizer to fit.
8. Update `doc/02_requirements/feature/feature.md` /
   `doc/08_tracking/test/test_result.md` only happens automatically on
   `bin/simple test` per `.claude/rules/structure.md` — no manual edit needed.
9. Land via the plumbing protocol (see repo `vcs.md`), scoped to exactly the
   two new files plus this research doc if not already landed separately.
