# Web Semantic/Layout + DrawIR Pipeline — Optimization & Refactoring Plan

Status: draft plan (not yet executed). Scope: `src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer.spl`
(9,456 lines) and its relationship to the existing Draw IR layer
(`src/lib/common/ui/draw_ir*.spl`, `src/lib/gc_async_mut/gpu/engine2d/draw_ir_adv.spl`).

Related: `doc/03_plan/ui/rendering/draw_ir_multibackend_plan.md` (Engine2D backend/op
unification — orthogonal, this plan does not duplicate it). This plan is the
concrete response to the perf regression exposed in
`doc/08_tracking/bug/web_render_full_engine_content_frame_reroute_perf_2026-07-12.md`.

## 1. Current State

### 1.1 The monolith's internal stages (file:line)

`simple_web_html_layout_renderer.spl` runs one parse→style→layout pipeline that
feeds **two independent output paths**:

| Stage | Functions | Lines |
|---|---|---|
| HTML parse | `parse_html` (L724), tag/attr scan (L132-611), entity decode (L611-724) | ~600 |
| CSS extract + cascade | `extract_css_vw` (L4309), selector match (L4386-5383), specificity/order (L5387-5627), `apply_decls` (L2150-3896, the single largest function — CSS property application), `tag_defaults` (L3896) | ~3,700 |
| Style resolution (orchestrator) | `compute_styles` (L5663) | ~60 |
| Layout (box model / flex / text-wrap) | `_layout` (L7492-8308, 800+ lines), `layout_document` (L8328) | ~950 |
| **Path A: direct pixel paint** | `paint` (L8483-8846) + ~40 `fb_*` pixel primitives (rects, rounded rects, gradients, shadows, borders, glyphs, scrollbars) at L5720-8465 | ~3,100 |
| **Path B: Draw IR emission** | `_html_draw_ir_commands` (L9048), `_html_draw_ir_command` (L9001), `_html_draw_ir_style_props` (L8862) | ~220 |
| Iframe embedding | `_web_paint_iframes` (L9169) — **Path A only, Path B does not call it** | ~90 |

Public entry points: `simple_web_layout_render_html_software_pixels` (L9259,
Path A), `simple_web_layout_render_html_draw_ir` (L9203, Path B — **already
exists**), `simple_web_layout_render_html_gpu_frame` (L9408, solid-fill op list
+ CPU residual), `simple_web_layout_render_html_software_pixels_at_scroll`
(L9434). All four re-run `parse_html → extract_css_vw → compute_styles →
layout_document` independently — the styled/laid-out tree is never named or
shared as a first-class value.

### 1.2 What already exists vs. what's missing

**Already exists (verified by reading the code, not assumed):**
- `simple_web_layout_render_html_draw_ir` (L9203) already converts HTML → `DrawIrComposition` via the SAME web semantic/layout stages as Path A; the lowering is thin and incomplete (§1.3).
- `src/lib/gc_async_mut/gpu/browser_engine/simple_web_layout_engine2d_fast.spl:27` `simple_web_layout_render_html_pixels_engine2d` already chains HTML → `simple_web_layout_render_html_draw_ir` → `Engine2D.create_with_backend_fast()` (no-mirror GPU mode) → `engine2d_draw_ir_adv_composition` (`draw_ir_adv.spl:422`) → one-shot GPU readback. Comment there cites this as the fix for the interpreted per-op framebuffer mirror being the dominant cost.
- This fast path is **already wired into production**, but only for the WM chrome scene: `src/os/compositor/wm_scene.spl:462-487` `render_scene_to_backend()` uses the full CSS pixel path below `WM_SCENE_CSS_RENDER_PIXEL_CAP=10000px`, else the DrawIR+Engine2D-fast path if Metal is available (`engine2d_fast_metal_available()`, L479), else a non-CSS themed rect rasterizer (`wm_scene_direct_rect_pixels`, L489) that **skips text entirely** (L500-501).
- `engine2d_draw_ir_adv.spl` already re-derives border-radius, linear-gradient background, and box-shadow from `DrawIrCommand.computed_style` text props (`_engine2d_draw_ir_render_box`, L188) and calls real Engine2D primitives (`draw_rounded_rect`, `draw_gradient_rect`, `draw_shadow_rect`). Only `RECT`/`TEXT`/`IMAGE` command kinds are executed (`_engine2d_draw_ir_supported_command`, L82); others are tracked as skipped/unsupported.
- `DrawIrSourceInfo` (`draw_ir.spl:78-86`) already carries `html_tag`/`html_node_id`/`css_selector`/`css_class`/`style_key`/`style_revision` — built by `draw_ir_source_html_ast` (L385) and used today by `simple_web_layout_render_html_draw_ir` (L9213: `source_kind="html_ast"`).
- `draw_ir_diff.spl:219` `draw_ir_diff_compositions` — a working node-level diff (added/removed/changed by `component_id`, with geometry/color/text/style/border/hit-rect change flags) — exists and is spec-tested.
- Precedent for "layout tree → DrawIR directly, no intermediate pixel path": `widget_draw_ir.spl:217` `widget_tree_to_draw_ir` walks a laid-out `WidgetNode` tree and emits `DrawIrCommand`s with no separate pixel-paint code path at all.
- `window_scene_draw_ir.spl` (1,086 lines) already threads a revision string into `DrawIrSourceInfo` as a cache key precedent: `"rev={frame.content_revision}"` (`_wm_draw_ir_child_content_frame_batch`) — the seed of exactly the IR-level cache this plan proposes.

**Missing / gaps:**
- **The window content-frame path — the one users actually type into — does not use Path B or the fast GPU path at all.** `src/os/compositor/simple_web_window_renderer.spl:158-164` `simple_web_content_frame_cached_from_request` calls `cache.request_to_pixel_artifact` → `web_render_pixel_software_backend.spl:129` → `_software_pixels` → `simple_web_layout_render_html_software_pixels` (Path A, full pixel paint, interpreted, measured 55-60x slower than the deprecated tag-strip fallback — `web_render_full_engine_content_frame_reroute_perf_2026-07-12.md`).
- `draw_ir_diff_compositions` has **zero production render-loop callers** — its only caller outside its own spec is `src/app/ui.test_api/handler.spl` (a test API), not any paint path.
- `WebRenderPixelArtifactCache` (`web_render_pixel_software_backend.spl:97`) caches on **whole-HTML-string equality** (`self.last_html == full_html`, L119) — one changed character invalidates the entire cache; there is no node-level cache.
- Path B (`_html_draw_ir_commands`) never sets `parent_id` on emitted commands — every call site of `draw_ir_box_with_style`/`draw_ir_text_styled` (`draw_ir.spl:241-260`, `217-239`) hardcodes `parent_id: ""`, even though `HNode` already carries a `parent` field (`mk_node(tag, parent: i64)`, L172). Tree structure is discarded exactly where a future diff/subtree-invalidation would need it.
- Path B never emits `<img>` as `DRAW_IR_COMMAND_IMAGE`, and never calls `_web_paint_iframes` — iframe/image content silently renders as an empty box in the DrawIR path today (untested — no parity spec covers it).
- `DrawIrComposition`/`DrawIrEmbeddingConfig` carry no DPI field; `dpi_scale_milli` is a bare function parameter in `window_scene_draw_ir.spl` (e.g. `shared_wm_scene_draw_ir_composition`, L623), baked into pixel coordinates before any IR is built.
- **Open correctness bug that blocks any pixel-parity gate**: `doc/08_tracking/bug/web_render_full_engine_call_order_nondeterminism_2026-07-12.md` — the full engine produces different checksums for byte-identical input depending on call order/count within a process (suspected process-lifetime cache/arena state).

## 2. Target Architecture

**Decision: do not add a `WebIR`/`WebIrDocument` type or a second display-list
format.** The existing private `(nodes: [HNode], styles: [Style], boxes:
LayoutResult)` semantic/layout state remains owned by the web renderer.
`DrawIrComposition` remains the sole shared display list and already carries
CSS provenance through `DrawIrSourceInfo` (`html_ast`). This matches the
canonical UI architecture in `doc/04_architecture/ui/00_ui_architecture.md`.

```
HTML/CSS text
    │  parse_html / extract_css_vw
    ▼
existing web semantic/layout state (private nodes+styles+boxes)
    │  _html_draw_ir_commands (extend: parent_id, image, iframe-as-embedded-batch)
    ▼
DrawIrComposition (EXISTING — draw_ir.spl, already HTML-aware)
    │  engine2d_draw_ir_adv_composition (EXISTING — draw_ir_adv.spl)
    ▼
Engine2D backend (software / Metal / CUDA / ... — EXISTING, unmodified)
```

Widgets (`widget_draw_ir.spl`) skip the web semantic/layout stage entirely
because widget layout has no CSS cascade or text-wrap ambiguity — the
box-model result IS the display list. Web may cache its existing private
semantic/layout state because CSS cascade, flex, and text wrap are expensive,
and use `HNode` parent/child structure for subtree invalidation, without
promoting that state into a named or shared IR.

Backends are already shared (Engine2D executes WM chrome, widgets, and (via
the existing fast path) web content through the same `draw_ir_adv.spl`
executor) — this plan does not need to build a new backend, only route more
producers through the one that exists and complete its command coverage.

## 3. The Optimization Win

1. **Route content-frame rendering through the fast path that already exists
   for WM chrome.** `simple_web_layout_render_html_pixels_engine2d` is proven
   at ~1.4s exec+readback at 1024x768 on Metal vs. "minutes interpreted"
   (`wm_scene.spl:475-476` comment) for the CSS engine — the same order of
   speedup the content-frame path needs relative to its measured ~4-5s/render
   interpreted cost.
2. **Wire `draw_ir_diff_compositions` into the render loop** (currently unused
   in production). Diff the new `DrawIrComposition` against
   the last one cached per `window_id`, and re-issue backend draw calls only
   for nodes whose diff state is `"changed"`/`"added"`/`"removed"` — replacing
   `WebRenderPixelArtifactCache`'s whole-string equality with a node-level
   cache keyed on `content_revision` (already threaded end-to-end as
   `WmContentFrame.content_revision` and `DrawIrSourceInfo.style_revision`).
3. **This decouples repaint cost from viewport size.** Today `paint()` and its
   `fb_*` primitives touch every pixel in the framebuffer on every call
   regardless of what changed, which is why the render ladder scales linearly
   with pixel count (80x60≈6s, 1080p≈24s, 4K≈73-590s interpreted, per the
   mission brief). A diff-based repaint ties cost to *changed node count*, not
   *pixel count* — the only lever that makes interactive (per-keystroke) 4K/8K
   editing feasible; one-shot full-frame 8K cost is a separate, already-tracked
   effort (`doc/08_tracking/bug/cpu_simd_external_cairo_8k_perf_gap_2026-07-09.md`).
4. Quantitative target (to validate empirically in Phase 3/4, not assumed):
   content-frame re-render on a small edit should approach the GPU fast-path's
   ~1.4s/full-frame ceiling in Phase 3, then drop toward O(changed nodes) —
   sub-100ms for a single-line edit in a multi-hundred-node document — in
   Phase 4.

## 4. Migration Strategy (staged, non-breaking, flag-gated)

The monolith is load-bearing (the de-fake effort just made its real content
path reachable in production). No phase deletes Path A until parity is proven
in CI for multiple cycles.

**Phase 0 — Determinism prerequisite (blocks all parity gates).**
Root-cause `web_render_full_engine_call_order_nondeterminism_2026-07-12.md`.
*Acceptance:* 100 repeated same-input renders in one process produce identical
checksums.

**Phase 1 — Share the existing web semantic/layout lowering (pure refactor).**
Keep nodes/styles/boxes private to the web renderer and extract only the
smallest internal helper needed to remove duplicated parse→style→layout call
sequences at L9203/9220/9259/9408/9434. Do not expose or name a new IR type.
*Acceptance:* existing spec suite (`simple_web_renderer_spec.spl` and friends,
~800 lines) green, byte-identical output — no behavior change.

**Phase 2 — Close web semantic/layout→DrawIR coverage gaps.**
Set `parent_id` from `HNode.parent`; emit `<img>` as `DRAW_IR_COMMAND_IMAGE`;
emit iframe content as a nested embedded `DrawIrBatch` (reuse the depth-3
embedded-surface mechanism already in `draw_ir_adv.spl:336`
`_engine2d_draw_ir_render_batch_embedded`) instead of leaving iframes
unimplemented in Path B. *Acceptance:* new pixel-parity spec — Path B (via
`engine2d_draw_ir_adv_composition`) byte-matches Path A
(`simple_web_layout_render_html_software_pixels`) over a corpus that includes
images and iframes (currently untested since Path B silently drops both).

**Phase 3 — Route content-frame rendering through the fast path, flag-gated.**
Add `WebRenderPixelArtifactCache.request_to_pixel_artifact_via_draw_ir`
(env flag `SIMPLE_WEB_CONTENT_DRAW_IR`, default off) calling
`simple_web_layout_render_html_pixels_engine2d` instead of `_software_pixels`
— the same pattern `wm_scene.spl` already uses for chrome. *Acceptance:*
pixel-parity spec (Phase 2 corpus) green under the flag; perf probe on
**`bin/simple` (self-hosted, not the bootstrap seed)** showing content-frame
re-render time vs. the current interpreted baseline; flag flipped default-on
only after N clean CI cycles.

**Phase 4 — Wire `draw_ir_diff` into the cache for incremental repaint.**
Cache `DrawIrComposition` per `window_id`; on a new
`content_revision`, diff via `draw_ir_diff_compositions` and extend
`draw_ir_adv.spl` with an incremental entry that skips `"unchanged"` commands.
*Acceptance:* perf probe demonstrating re-render cost scales with changed-node
count, not total node count (e.g., a 1-line edit in a 500-node document costs
~O(1), not O(500)).

**Phase 5 — Cut over, audit for dead code.**
Once Phases 3-4 have run default-on with the parity gate green for a defined
period, either delete the direct Path A content-frame call site or keep it
only as an explicit crash-recovery fallback (mirroring
`request_to_native_safe_pixel_artifact`'s existing documented role). Do **not**
bulk-delete the ~3,100-line `fb_*` primitive block without first checking
whether Engine2D's own software backend depends on equivalent primitives —
audit, don't assume duplication.

## 5. Risks / Unknowns

1. **Determinism.** Every phase after Phase 0 depends on a bit-exact
   pixel-parity gate, but the engine is currently proven non-deterministic
   across calls for identical input. If root cause isn't found quickly, gates
   may need statistical tolerance instead of bit-exact equality — weakening
   every later phase's confidence.
2. **Text fidelity.** `draw_ir_adv.spl:93-107` re-derives font size by
   re-parsing the `font-size` string out of `computed_style` rather than
   reusing a value the web semantic/layout stage already computed — any encoding
   drift (e.g., `parse_font_shorthand_size_px`, L1827, edge cases) could
   silently diverge between Path A and Path B without tripping a
   geometry-only parity check. Needs its own text-fidelity corpus.
3. **Interpreted vs. compiled perf.** Every cost number cited in the driving
   bug docs is measured on the interpreted bootstrap seed; both bug docs
   explicitly flag that the self-hosted compiled binary was not separately
   measured. Per `.claude/rules/bootstrap.md`, all real numbers for this plan
   must come from `bin/simple` (self-hosted), not the seed — re-validate the
   whole cost/benefit case in Phase 3 before investing in Phase 4.
4. **Scope.** This is a multi-week effort touching a 9,456-line file with an
   ~800-line existing spec suite plus WM/compositor integration tests. It must
   ship as the staged, flag-gated phases above — never as one large PR.
5. **GPU-fast-path availability is untested outside Metal.** The only gate
   found for the existing fast path is `engine2d_fast_metal_available()`
   (`simple_web_layout_engine2d_fast.spl:44`) — whether
   `Engine2D.create_with_backend_fast()`'s no-mirror mode works correctly on
   non-Metal backends (CPU-SIMD, CUDA, Vulkan) for web content specifically is
   not established by anything read here.

## 6. Relation to Today's Work

- **De-fake content-frame routing (2026-07-12).** The routing fix that made
  the full engine the default for content frames (swapping away from the
  tag-strip fallback) is exactly what made this plan's target — the full
  engine's true interactive cost — reachable and measurable in production.
  This plan is the planned follow-up to that fix, not a new direction.
- **4K/8K directive.** Cited 4K/8K numbers
  (`cpu_simd_external_cairo_8k_perf_gap_2026-07-09.md`: 7680x4320 @ 300dpi,
  ~0.8-1.3s p50) are all **one-shot full-frame** renders. This plan's
  diff-based repaint (Phase 4) is the only lever that makes *interactive*
  (per-keystroke) 8K editing feasible — one-shot full-frame cost is a
  separate, already-tracked effort this plan does not duplicate.
- **300 DPI.** Neither `DrawIrComposition` nor `DrawIrEmbeddingConfig` carries
  a DPI field today — `dpi_scale_milli` is passed as a bare parameter and
  baked into pixel coordinates before any IR value exists
  (`window_scene_draw_ir.spl:623`). Include `dpi_scale_milli` in the existing
  render-cache key (or the canonical Draw IR embedding configuration if that
  owner gains the field) so a future cache/diff layer can distinguish DPI
  changes from content changes without creating a parallel web IR type.

## Unknowns not determined from code

- Real self-hosted-binary (`bin/simple`) timing for the content-frame path —
  no measurement of this exists anywhere found; only interpreted-seed numbers
  are on record.
- Whether the Metal-only-gated fast path generalizes correctly to other
  Engine2D backends for web content (only the WM-chrome caller and its Metal
  gate were found).
