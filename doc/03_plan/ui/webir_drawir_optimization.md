# Web Semantic/Layout + DrawIR Pipeline — Optimization & Refactoring Plan

Status: active, partially implemented. Source anchors below were refreshed on
2026-07-31 after the stage split. **RED:** iframe rendering still uses the
legacy private pixel blit; it is not a completed DrawIR migration. Scope:
the private web semantic/layout stages and their relationship to the existing Draw IR layer
(`src/lib/common/ui/draw_ir*.spl`, `src/lib/gc_async_mut/gpu/engine2d/draw_ir_adv.spl`).

Related: `doc/03_plan/ui/rendering/draw_ir_multibackend_plan.md` (Engine2D backend/op
unification — orthogonal, this plan does not duplicate it). This plan is the
concrete response to the perf regression exposed in
`doc/08_tracking/bug/web_render_full_engine_content_frame_reroute_perf_2026-07-12.md`.

**2026-07-31 reconciliation:** production cutover, persistent Engine2D
lifecycle, compatibility-path isolation, backend capability evidence, and live
acceptance are now ordered in
`unified_2d_engine/draw_ir_web_renderer_reconciliation_2026-07-31.md`.
Main parent/image lowering is implemented; iframe embedding remains red.

## 1. Current State

### 2026-07-29 implementation status

- The architectural decision remains unchanged: there is no new `WebIR`;
  private web semantic/layout state lowers to `DrawIrComposition`.
- The shared Draw IR contract now owns rectangle translation/intersection, and
  the Engine2D executor reuses it for command clips. This is a bounded,
  behavior-preserving part of Phase 1.
- The first retained-render slice is done in source and runtime-blocked:
  authoritative BrowserSession document/style/resource revisions feed one
  worker-owned `SimpleWebRenderSession`, and an unchanged frame reuses the
  existing semantic/layout/Draw IR result. Stage-selective mutation,
  viewport, animation, scroll, and resource invalidation remain open. No
  whole-HTML pixel cache was added.
- External `<img>` and CSS background lowering cover part of Phase 2. Iframe
  embedding and exact Path-A/Path-B parity remain open; the legacy iframe
  pixel blit stays RED until its embedded-batch replacement has parity.
- The CPU benchmark adapter no longer owns a private painter. It constructs
  the requested `cpu`/`cpu_simd` `Engine2D` and executes the composition only
  through `engine2d_draw_ir_adv_composition(..., false)`.

### Ordered next backlog

1. **Done in source, runtime-blocked:** retain DOM `parent_id` on main HTML
   commands and owning-element IDs on synthetic image/input overlays; image
   command lowering is also present. Keep the
   REQ-WEB-BROWSER-003/004 semantic composition oracle before pixels and
   round-trip it through the existing hosted SBRF/Draw IR v2 codec.
2. Emit iframe content through the existing embedded `DrawIrBatch` mechanism.
3. **Partial, runtime-blocked:** finish authoritative mutation/style/resource
   revision sites and split the retained owner into stage-selective
   parse/style/layout/paint invalidation. Exact unchanged reuse and close
   reclamation are implemented.
4. Cut `ui.browser` over from its ignored composition/pixel rebuild to the
   supplied `DrawIrComposition`, then run exact Path-A/Path-B corpus parity and
   route production frames through one persistent Engine2D owner.
5. Classify private bitmap text, heuristic scenes, CPU fallback, and readback
   routes as explicit compatibility/diagnostic/recovery paths with guards.
6. Prove web execution separately on physical CUDA, Vulkan, and Metal; Metal
   evidence does not qualify the other backends.
7. Consider Draw IR diff/damage only after retained-stage measurements prove
   unchanged-frame reuse is insufficient.

`simple_web_html_layout_renderer_paint_layout.spl` remains a pre-existing
>800-line stage-owner exception. Split it only behind the semantic composition
and pixel-parity gates above; do not mix file movement with fidelity changes.

### 1.1 Current source map

The public facade is `simple_web_html_layout_renderer.spl`; its private stages
are split by owner, not line number:

| Stage | Current owner | Status |
|---|---|---|
| HTML parse/CSS cascade | `simple_web_html_layout_renderer_core.spl`, `_declarations.spl`, `_decl_apply.spl`, `_style.spl` | private semantic state |
| Layout | `simple_web_html_layout_renderer_layout.spl` | private semantic state |
| **Path A: direct pixels** | `_paint_layout.spl`, `_paint_primitives.spl`, facade software entry points | compatibility/reference path |
| **Path B: DrawIR** | `_paint_layout.spl` (`_html_draw_ir_style_props`, `_html_draw_ir_command`, `_html_draw_ir_commands`), facade DrawIR entry points | canonical shared display list |
| CPU benchmark adapter | `simple_web_layout_engine2d_cpu.spl` | `Engine2D` + shared DrawIR executor only |
| Iframe pixels | `_paint_layout.spl` (`_web_render_child_pixels`, `_web_blit_child`, `_web_paint_iframes`) | **RED: legacy Path-A-only blit** |

The active content-frame cache is `ui/web_render_pixel_backend.spl` backed by
`SimpleWebEngine2DStaticPixelCache` in `simple_web_engine2d_renderer.spl`.
It keys exact HTML, render mode, and content revision; it is not yet a
node-level DrawIR-diff cache.

### 1.2 What already exists vs. what's missing

**Already exists (verified by reading the code, not assumed):**
- `simple_web_layout_render_html_draw_ir` in `simple_web_html_layout_renderer.spl` converts HTML → `DrawIrComposition` through the same private semantic/layout stages as Path A.
- `simple_web_layout_engine2d_fast.spl` chains HTML → DrawIR → `Engine2D.create_with_backend_fast()` → shared DrawIR execution → one-shot readback. The CPU benchmark adapter uses the same executor with `gpu_available=false`; it has no private style, border, gradient, text, or clip painter.
- The fast path is wired into the WM chrome scene. `render_scene_to_backend()` chooses the DrawIR+Engine2D-fast path when its Metal gate is available; its non-CSS fallback skips text and is not a web-content replacement.
- `engine2d_draw_ir_adv.spl` owns border-radius, linear-gradient background, box-shadow, text, and clip execution from `DrawIrCommand.computed_style`. Supported command accounting remains in that shared executor.
- `DrawIrSourceInfo` in `draw_ir.spl` carries HTML/CSS provenance and is used by the public DrawIR entry.
- `draw_ir_diff_compositions` exists and is spec-tested; it has no production incremental paint caller.
- `widget_draw_ir.spl` remains the precedent for layout directly to DrawIR with no intermediate pixel painter.
- `window_scene_draw_ir.spl` carries content revision provenance; it remains the cache-key precedent.

**Missing / gaps:**
- The window content-frame path in `simple_web_window_renderer.spl` calls `WebRenderPixelArtifactCache.request_to_pixel_artifact[_at_time]`; that cache routes static frames through the retained Engine2D DrawIR result. Dynamic regions retain their explicit fallback branch and require separate evidence.
- `draw_ir_diff_compositions` has **zero production render-loop callers** — its only caller outside its own spec is `src/app/ui.test_api/handler.spl` (a test API), not any paint path.
- `SimpleWebEngine2DStaticPixelCache` still caches whole-document identity, so one changed character invalidates the frame; no node-level invalidation exists.
- Main DrawIR commands retain parent IDs and image lowering. The bounded
  `srcdoc` embedded-batch source tranche is under review; legacy pixel blitting
  remains the oracle and stays RED until qualified exact parity permits caller
  migration.
- `DrawIrComposition`/`DrawIrEmbeddingConfig` carry no DPI field; `dpi_scale_milli` is passed by the scene owner and baked into pixel coordinates before DrawIR is built.
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
sequences. Do not expose or name a new IR type.
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
   drift (for example, font-shorthand edge cases) could
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
