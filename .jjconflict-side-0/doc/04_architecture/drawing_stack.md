# Drawing Stack Architecture

**Status:** In progress (Chromium-parity renderer for Simple browser)
**Last updated:** 2026-04-15

## Overview

The drawing stack is a Chromium-class rendering pipeline written in Simple,
consumed by `examples/browser/` (simple_browser V3 shell). It mirrors
Chrome's layering — **Blink** (DOM/CSS/layout) → **cc** (layer trees + tiles)
→ **viz** (compositor frames) → **Skia** (2D graphics core) — so existing
Chromium literature applies. Where the MDSOC capsule model forces divergence
(sandbox boundaries, capability handles, no POSIX), the Simple module keeps the
Chrome name but documents the drift inline.

Code lives under four top-level libraries with matching specs under `test/lib/`:

- `src/lib/skia/`
- `src/lib/blink/`
- `src/lib/viz/`
- `src/lib/cc/`

## Module Map

### Skia (2D graphics core)

- **Backends** — `cpu/backend.spl` (CanvasState save/restore stack with clip,
  alpha, transform), `vulkan/backend.spl` (PipelineKey cache + triangulator).
- **Entities** — `canvas.spl` (SkCanvas + recorder + translate/scale/rotate/
  concat/set_matrix), `matrix.spl` (Matrix3x3 + tx/ty/scale_x/scale_y),
  `path.spl` (contains/bounds), `picture.spl` (SkPictureOp list),
  `color_space.spl`, `vertices.spl` (SkVertices triangle mesh),
  `textblob_v2.spl` (multi-run text), `runtime_effect.spl` (SkRuntimeEffect
  stub), `region.spl` (YX-banded SkRegion), `surface.spl` (SkSurface + canvas
  factory).
- **Color management** — `tone_map.spl` (PQ/HLG/sRGB/γ2.2 transfers +
  rgb_to_rgb), `color_convert.spl` (pixel + bitmap RGBA conversion),
  `icc_profile.spl` (ICC v4 parser), `icc_writer.spl` (ICC v4 writer),
  `yuv_convert.spl` (BT.601/709/2020).
- **Filters** — `blur.spl` (Kovesi 3-pass Gaussian), `color_filter.spl`
  (Identity/Invert/Grayscale/Matrix4x5/Lerp), `morphology.spl`
  (Erode/Dilate), `compose.spl` (N-stage pipeline), `mask_filter.spl` (alpha
  filters: Blur/Emboss/Shadow).
- **Path** — `path_op/boolean.spl` (Union/Intersect/Difference/Xor),
  `stroke/dash.spl` (SkDashPathEffect), `stroke/expand.spl` (stroke-to-fill
  with StrokeJoin/StrokeCap), `path_effect/corner_discrete.spl`
  (SkCornerPathEffect + SkDiscretePathEffect).
- **Image** — `resample/scale.spl`
  (Nearest/Bilinear/Mitchell-Netravali Bicubic), `codec/raw_rgba.spl` (raw
  bitmap codec).
- **Text / Glyph** — `ot_parser.spl` extended with gvar packed decoders +
  apply_gvar_deltas_to_points; `font_metrics.spl` (hhea/OS2/post);
  `colrv1.spl` Transform/Translate/Rotate/Scale/Skew + PaintGlyph;
  `ascii_fallback.spl` (5x7 bitmap debug font); `shaper.spl` extended with 10
  script classifiers (Thai, Myanmar, Khmer, Tibetan, Hangul, Hebrew,
  Mongolian — alongside existing Arabic + Indic).
- **Glyph cache / fonts** — `glyph_cache/cache.spl` (LRU atlas),
  `font_loader/registry.spl` (FontRegistry + match_family_style).
- **Text layout** — `text/line_break.spl` (UAX#14-lite word-wrap).
- **Animation** — `animation/interpolate.spl` (cubic-bezier easing + lerp),
  `animation/keyframe.spl` (KeyframeSequence sampler).
- **SkSL** — `sksl/tokenizer.spl`, `sksl/parser.spl` (minimal AST: top-level
  uniforms + functions + return + expressions; left-chain binary ops, no
  precedence).

### Blink (rendering engine frontend)

- **DOM** — `dom/node.spl` (DomTree: create_element / create_text /
  append_child / set_attribute), `dom/document.spl` (Document + URL +
  ready_state + DomTree).
- **Style** — `entity/computed_style.spl` (ComputedStyle, 22 fields across
  display/position/visibility/color/width/height/margins/padding/font/
  opacity/z-index); `style/cascade.spl` (resolve_style walks the DOM,
  matches selectors, cascades declarations, honours !important).
- **HTML parse** — `html_parser/tokenizer.spl` (HTML5 tokenization subset),
  `html_parser/tree_builder.spl` (tokens → DomTree; 7 insertion modes;
  open-element stack; void elements).
- **CSS parse** — `css_parser/tokenizer.spl` (CSS Syntax L3 subset),
  `css_parser/parser.spl` (tokens → CssStyleSheet), `css_parser/selector.spl`
  (parse_selector + matches_compound + matches_complex:
  Type/Class/Id/Universal/AttributePresence +
  Descendant/Child combinators).
- **Paint** — `entity/paint_chunk.spl` (PaintChunk + PropertyTreeState).
- **Input** — `input/event.spl` (InputEvent with mouse/key/touch/wheel;
  has_modifier/mark_handled).
- **URL** — `url/url_parser.spl` (WHATWG-subset + percent_encode/decode +
  query_string_parse).
- **Layout** — `layout/block_flow.spl` (BoxGeometry + LayoutBox +
  compute_layout vertical stacking); `layout/inline_flow.spl` (InlineItem +
  LineBox + greedy line packer).

### Viz (compositor frontend)

- `feature/frame_builder.spl` — CompositorFrameBuilder with 5 quad types:
  SolidColor, Texture, Surface, RenderPass, DebugBorder.
- `feature/frame_scheduler.spl` — 60Hz cadence throttle; deadline-miss
  tracking.
- Pre-existing: `feature/damage.spl`, `feature/aggregator_walker.spl`,
  `feature/aggregator_compose.spl`.

### cc (compositor backend)

- `entity/property_tree.spl` — unified PropertyTrees with
  compute_*_to_root walks + legacy TransformTree / ClipTree / EffectTree /
  ScrollTree backward-compat wrappers (restored after a rewrite broke
  aggregator_compose.spl).
- `entity/tile.spl` — Tile with TilePriority / TileDrawState + legacy
  TileKey / NowBin backward-compat wrappers (restored after a rewrite broke
  picture_layer_impl and tile_manager).
- `entity/layer_base.spl` — new Layer base, added alongside the existing
  `layer.spl` to avoid another rewrite regression.

## Pipeline Flow

```
 HTML bytes ─► Blink html_parser ──┐
 CSS bytes  ─► Blink css_parser ───┤
                                   ▼
                             DomTree + CssStyleSheet
                                   │
                                   ▼
                      Blink style/cascade (ComputedStyle)
                                   │
                                   ▼
                   Blink layout/block_flow + inline_flow
                                   │  (LayoutBox tree)
                                   ▼
                         Blink paint (PaintChunks)   ← not yet wired
                                   │
                                   ▼
                       cc property_tree + tile grid
                                   │
                                   ▼
                   viz frame_builder → CompositorFrame
                                   │
                                   ▼
                  Skia SkCanvas ► SkPicture ► Backend
                                   │
                                   ▼
                         cpu/backend  |  vulkan/backend
```

Each stage is a pure Simple module with its own spec in `test/lib/<lib>/…`.
Only Backend is side-effecting (pixel writes, GPU submissions).

## Key Design Decisions

1. **Chromium naming, MDSOC plumbing.** File names, type names, and public
   API surface mirror Chromium (`SkCanvas`, `PropertyTrees`, `PaintChunk`,
   `CompositorFrameBuilder`) so that a Chrome engineer can navigate the tree.
   Where the MDSOC capsule model forces a different boundary — e.g. the
   compositor runs in a separate capsule behind capability handles — the
   module documents the drift inline. See
   `memory/feedback_mirror_chromium_naming.md`.

2. **Backward-compat when rewriting entities.** Two rewrites (cc
   PropertyTree, cc Tile) silently replaced the legacy types and broke
   external callers (aggregator_compose, picture_layer_impl, tile_manager).
   Fix: new rewrites now keep the legacy class names as thin wrappers over
   the new data. The layer_base.spl/layer.spl split was designed this way up
   front.

3. **Bash-verify after every Write.** Four agent-dispatched Write calls
   silently dropped content in this session (tone_map, icc_profile, gvar
   decoders, textblob v2). The Read tool can return phantom content in that
   state. The recovery protocol is documented in
   `memory/feedback_write_tool_silent_drops.md` — after every Write do
   `wc -l`, `md5sum`, and a `grep` for a known-unique token before
   considering the file saved.

4. **Destructive-upstream detection.** Before rebasing we snapshot
   `git ls-files | wc -l`, then re-check after rebase; if the file count
   drops we revert the upstream WIP and cherry-pick local work instead of
   adopting the destructive rewrite. See
   `memory/feedback_destructive_upstream_detection.md`.

5. **Split commits for force-push resilience.** Renderer subsystems land in
   ≤5-file atomic commits so a parallel force-push can only strip a small
   wave. See `memory/feedback_force_push_kernel_arc.md`.

## Out-of-Scope / Remaining Work

See `doc/08_tracking/drawing_stack_remains.md` for the full backlog
(paint pass integration, hit testing, real font metrics, GPU path
submission, navigation controller, scroll manager, HTML error recovery,
CSS @media + pseudo-classes + calc/var/em, flex/grid, bidi + justify,
SkSL type checker + bytecode, surface aggregator dispatch, real font
enumeration, display compositor, floats + tables + margin collapse).
Known issues and workarounds live in
`doc/08_tracking/drawing_stack_bugs.md`.
