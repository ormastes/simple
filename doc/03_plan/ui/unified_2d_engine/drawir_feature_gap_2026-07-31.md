# DrawIR feature gap — game + GUI/web renderer needs vs what DrawIR supports (2026-07-31)

Survey lane. No production code changed. Companion to
`unified_2d_event_panel_offload_2026-07-30.md` (event/panel/GPU-offload work) —
this document instead answers the campaign goal item "all game and GUI
(through web) renderer needed features exist; DrawIR fully supported", which
had never been enumerated. Produced by 3 parallel research passes (DrawIR
core, game-renderer needs, GUI/web-renderer needs), each independently
re-verified by grep/read against the actual source. Every claim below cites
`file:line`; anything not independently confirmed is marked **UNVERIFIED**
rather than guessed.

## 1. What DrawIR supports today

Core contract: `src/lib/common/ui/draw_ir.spl`. Advanced execution
(shadows/radii/glass/gradients) lives in
`src/lib/gc_async_mut/gpu/engine2d/{draw_ir_adv,draw_ir_box_effects,draw_ir_glass_material,draw_ir_target,draw_ir_target_metal}.spl`
— **not** in `common/`, contrary to what the campaign doc's file list implied;
this is existing pre-campaign code, not a D8 violation to fix here, just a
correction for anyone searching by the wrong path. Diff/patch:
`src/lib/common/ui/{draw_ir_diff,draw_ir_patch}.spl`. Hit bridge:
`src/lib/common/engine/interaction/draw_ir_hit_bridge.spl`.

**Command kinds — SCHEMA-ADMITTED, small closed set.**
`draw_ir.spl:10-16`: `DRAW_IR_COMMAND_{RECT,TEXT,EDGE,PATH,IMAGE,GROUP,PORT}`.
Edge sub-kinds `DRAW_IR_EDGE_{STRAIGHT,ORTHOGONAL,BEZIER}` (`:17-19`). No
dedicated circle/triangle/glyph/gradient/blur *kind* — those ride as
`computed_style` string props (key/value pairs, `draw_ir.spl:34-36`,
`DrawIrCommand.computed_style: [DrawIrStyleProp]` `:79`) decoded downstream by
`draw_ir_adv.spl`. The shared executor currently handles RECT, TEXT, and IMAGE;
EDGE, PATH, GROUP, and PORT still need behavior or typed fail-closed coverage.

**Batch/embedding model — SUPPORTED.** Verified directly
(`draw_ir.spl:57-105`, read in full this session):
```
struct DrawIrEmbeddingConfig:
    surface_id, component_id, x, y, width, height, layer: i32,
    opacity_milli: i32, clip: bool
struct DrawIrCommand:
    kind, component_id, x, y, width, height, color,
    text_value, advance_widths, border_rect, content_rect,
    hit_rect: DrawIrRect, clip_rect: DrawIrRect, computed_style,
    edge: DrawEdge?, parent_id: text, image_uri, points, glyph_run
struct DrawIrBatch:
    schema, batch_id, backend_target, source, embedding, commands: [DrawIrCommand]
struct DrawIrComposition:
    schema, composition_id, scene_key, ... [DrawIrBatch]
```
`hit_rect` (`:80`) and `parent_id` (`:84`) confirmed still present, matching
prior campaign notes. `layer: i32` is batch-level only (`:63`), consumed by
`Panel2D.layer` (`panel2d.spl:78,134` → `panel_to_draw_ir_batch` at
`panel2d.spl:275-293`, passed straight into `embedding.layer` — Panel2D has no
separate z-model of its own).

**Transforms — ABSENT.** No rotation/scale/skew/matrix field anywhere in
`draw_ir.spl`; only `x/y` offset + `width/height`. Only x/y placement.

**Blend modes — ABSENT at the DrawIR level.** `color.spl:74`'s `blend(src,dst)`
is plain Porter-Duff src-over; `DrawIrRenderTarget.draw_image_blend` /
`draw_image_scaled_blend` (`draw_ir_target.spl:46,48`) are alpha-blit variants,
not a selectable-mode enum.

**Opacity/compositing groups — PARTIAL.** `opacity_milli: i32` batch-level
(`draw_ir.spl:65`), consumed in offscreen compositing
(`draw_ir_target.spl:60`, `draw_ir_composite_readback(...opacity_milli)`). No
per-command opacity, no isolated-blend-group concept. Backdrop-filter
(blur+saturation) group compositing exists via glass material (see below).

**Clipping — PARTIAL, rect-only.** `clip_rect: DrawIrRect` per command
(`:81`), `clip: bool` per batch (`:66`), trait `set_clip/clear_clip/clear_mask`
(`draw_ir_target.spl:49-51`). No clip-path, no multi-rect clip stack.

**Gradients — PARTIAL, linear only, 2-stop.**
`draw_gradient_rect(x,y,w,h,top_color,bottom_color)`
(`draw_ir_target.spl:40`) — vertical 2-color, no stop list, no radial, no
angle. Rounded+gradient explicitly unimplemented: "No backend owns a
rounded-gradient clip yet" (`draw_ir_adv.spl:635-637`).

**Box shadow — SUPPORTED, typed.**
`Engine2dDrawIrBoxShadowLayer{kind:text("outer"|"inset"), offset_x, offset_y,
blur_radius, spread_radius, color:u32}` (`draw_ir_box_effects.spl:20-26`),
up to `_E2D_BOX_MAX_SHADOW_LAYERS = 24` (`:13`, confirmed directly this
session). Encoded as `box-shadow-layer-*` style props, not native
`DrawIrCommand` fields. Legacy single-shadow fallback:
`Engine2dDrawIrLegacyShadow{visible,safe,offset_x,offset_y,blur_radius,color}`
(`:41-47`, no spread/inset).

**Corner radii — SUPPORTED, per-corner (decode-time), uniform (render-time).**
`Engine2dDrawIrCornerRadii{schema_present, valid, top_left, top_right,
bottom_right, bottom_left: i32}` (`draw_ir_box_effects.spl:33-39`). The render
trait only exposes uniform `draw_rounded_rect(...,radius:i32,...)`
(`draw_ir_target.spl:38-39`) — per-corner values are parsed but a single
radius is what actually reaches the paint call.

**Other filters — PARTIAL, blur/saturation only.** `backdrop-filter` drives
`Engine2dGlassMaterialConfig{blur_radius, saturation_milli,
surface_alpha_milli, surface_color, gradient_from/to, gradient_enabled/
layered}` (`draw_ir_glass_material.spl:13-28`) via
`draw_ir_apply_glass_material` (`draw_ir_target.spl:32-34`). No grayscale/
hue-rotate/brightness/drop-shadow-as-filter.

**Text — PARTIAL.** `text_value`, `advance_widths`,
`glyph_run: DrawIrGlyphRunPayload{glyph_ids,xs,ys,clusters,valid}`
(`:42-47,76-77,87`), font metadata via `computed_style`. No text-decoration
field in `DrawIrCommand` itself (decoration is a consumer-side concern — see
§3.7).

**Retained mode / diff+patch — SUPPORTED, category-level not field-level.**
`DrawIrPatchOp{kind:i32, component_id, parent_id, command:DrawIrCommand?,
old_bounds, new_bounds, old_index, new_index}` (`draw_ir_patch.spl:64-72`),
kinds `INSERT/REMOVE/UPDATE_GEOMETRY/UPDATE_STYLE/UPDATE_TEXT/REORDER`
(`:57-62`). Each update still carries the whole replacement `command` — patch
granularity is "which category changed," not per-field diffing.
`draw_ir_diff.spl:14,28` does added/removed/changed classification on the same
command-index model. Per the campaign doc, this exists but has zero adoption
in the per-frame path yet (frames are still rebuilt, not patched).

**Render-to-texture / offscreen — SUPPORTED.**
`DrawIrRenderTarget.draw_ir_create_offscreen(w,h) ->
Result<DrawIrRenderTarget,text>` and `draw_ir_composite_readback(...)`
(`draw_ir_target.spl:59-60`); used in `draw_ir_adv.spl:1809,1862,1993-1998`.
Region readback: `_engine2d_read_pixels_region` (`draw_ir_adv.spl:1537`, per
the campaign doc) is an API seam only; the default backend reads the full frame
and crops on the host, so device-region readback remains open.

## 2. What a 2D game renderer needs

Evidence lives outside `common/` — in `src/lib/gc_async_mut/game2d/` and
`src/lib/nogc_sync_mut/{engine/render,game2d/render}/` — i.e. a real,
substantially-built game layer sits *above* DrawIR and is largely disconnected
from it (own transform/z-order/camera model, not DrawIR fields).

| Feature | Status | Evidence |
|---|---|---|
| Sprites/atlases | **SUPPORTED** | `Sprite`/`FrameRef` w/ `texture_id`+UV rect (`game2d/sprite.spl:16-25,33-52`); two atlas packers: `nogc_sync_mut/engine/sprite/atlas.spl:21-35` (`TextureAtlas.pack()`) and `nogc_sync_mut/game2d/render/texture_atlas.spl:23-38` (duplicate, `TextureAtlas2D`) |
| Transforms (rotate/scale) | **PARTIAL** | `Transform2D{pos_x,pos_y,rotation,scale_x,scale_y,parent}` + cached 3x3 matrix, `game2d/transform.spl:13-31`. No `skew` field anywhere (`grep -rn skew` across engine/game2d/common/ui = 0 hits) |
| Blend modes | **PARTIAL** | `enum BlendMode{Alpha,Additive,Multiply,Opaque}` (`nogc_sync_mut/engine/render/types.spl:28-33`); real per-channel math primitive `emu_draw_rect_blend_mode` (modes 0-3) at `gpu/engine2d/backend_emu_adv.spl:192-229`. `BlendMode.Additive` has **zero call sites** — not wired into the sprite/particle draw path |
| Tilemaps | **PARTIAL** | `TileMap`, grid `[[i32]] cells`, `render_tilemap()` (`game2d/tilemap.spl:16-56`) but explicit in-code comment: tiles paint as flat-color rects, "placeholder — real texture sampling would require a TextureRegistry" |
| Particles | **SUPPORTED** | `Particle{x,y,vx,vy,life,max_life,size,color,alpha,rotation,angular_velocity}`, `ParticleEmitter`/`EmitterConfig` (`nogc_sync_mut/engine/render/particle.spl:19-49`), pooled via `ParticlePool` (`particle_pool.spl:13-24`) |
| Camera/viewport | **SUPPORTED** | `Camera2D{viewport_x/y/w/h, target:Transform2D, zoom, bounds:Rect?}` (`game2d/camera.spl:31-53`); calls real `engine.set_clip(vx,vy,vw,vh)` (`:127` → `engine.spl:2421`) |
| Z-ordering | **SUPPORTED** | `Sprite.z: f32` (`sprite.spl:44`); `SpriteEntry.z_order: ZIndex` sorted in `sprite_batch.spl:33` (doc `:9-11`); every `RenderCommand` carries `z_order` (`engine/render/command.spl:41-49`) — own model, independent of DrawIR `layer` |
| Clipping | **SUPPORTED** | Reuses DrawIR `clip_rect`/`set_clip` (`draw_ir.spl:81`, `engine.spl:2421`) — confirmed game-usable via Camera2D |
| Render-to-texture | **SUPPORTED (primitive); usage UNVERIFIED** | `Engine2D.create_offscreen()` (`engine.spl:413`, wired `:2214-2229`) exists; no minimap/particle-compositing consumer was located in the game2d layer — search only, none found |
| Animation | **SUPPORTED (frame-based); tweening ABSENT** | `AnimationFrame`/`SpriteAnimation`/`AnimationPlayer.from_strip()` (`nogc_sync_mut/engine/render/sprite_animation.spl:17-31`), `AnimatedSprite{frames,current_frame,tick(dt_ms)}` (`game2d/sprite.spl:105-135`). Skeletal animation infra exists too (`engine/animation/{skeleton,skinning,ik_solver,clip,blender}.spl`, 3D-oriented, not confirmed wired to 2D). No `Tween`/`Easing` helper found (0 hits) |

## 3. What a GUI-through-web renderer needs

Consumers: HTML/CSS layout renderer
`src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_*.spl`
(foundation/core/style/layout/decl_apply/paint_layout/paint_primitives/
declarations) and widget path `src/lib/common/ui/widget_draw_ir.spl`, both
emitting `DrawIrComposition` directly (no separate GUI/Web IR — confirmed by
the prior campaign doc, D9).

| Feature | Status | Evidence |
|---|---|---|
| Box shadows | **SUPPORTED, typed** | Same `Engine2dDrawIrBoxShadowLayer` as §1, consumed via `engine2d_draw_ir_render_typed_outer_shadows`/`_inset_shadows`, called from `draw_ir_adv.spl:583,620,645` |
| Border radii | **SUPPORTED, per-corner (decode); uniform (render)** | `Engine2dDrawIrCornerRadii` as §1; browser layer mirrors with discrete `border_radius_tl_px/tr_px/br_px/bl_px` (`simple_web_html_layout_renderer_style.spl`) |
| Gradients | **PARTIAL** | Only `linear-gradient`, 2 stops, via `parse_linear_gradient_color()` (`foundation.spl:1027-1049`); direction/angle tokens explicitly skipped (a numeric `Ndeg` angle is misparsed as a color stop); **zero** `radial-gradient` hits anywhere in `browser_engine/` |
| Opacity/compositing | **SUPPORTED (opacity + backdrop-filter); ABSENT (isolation)** | `Style.opacity_pct` (`decl_apply.spl:767-769`); `filter: opacity(N)` multiplies into it — the *only* recognized `filter` function (`decl_apply.spl:770-774`, `foundation.spl:1245-1254`); threads via `DrawIrEmbeddingConfig.opacity_milli`; backdrop-filter glass material genuinely composited (`draw_ir_adv.spl:450-550`). CSS `isolation: isolate` — 0 hits (only unrelated `unicode-bidi: isolate`) |
| Transforms | **PARTIAL, layout-level approximation only** | `translate`/`translateX/Y`/`scale()` rewrite layout box geometry (`left_px/top_px/width_px/height_px`, `decl_apply.spl:785-821`) — not a paint-time affine transform. `rotate()` only detects a 90°/270° quarter-turn to swap w/h (`foundation.spl:1181-1200`, `decl_apply.spl:808-811`). No arbitrary-angle rotation, no `skew()`, no `matrix()` |
| Filters | **effectively ABSENT beyond opacity** | Only `opacity(N)` recognized under `filter:`; no `blur()`, `drop-shadow()`, `brightness()`, `grayscale()`, `contrast()`, `saturate()`, `invert()`, `sepia()`, `hue-rotate()` |
| Text decoration | **PARTIAL, and split across two coexisting paint paths (inconsistency, not just a gap)** | Primary `Style` struct (`style.spl:155-160`) has only `text_decoration_underline: bool`(+color/style/thickness/offset) — no field for overline or line-through; `paint_layout.spl:953-983` draws underline only. A second, older path (`layout_paint.spl:141-155` via `be_dom_get_text_decoration`, reached through `text_painter.spl`, imported by `mod.spl`) does compare `"underline"`/`"overline"`/`"line-through"` and draws all three — so behavior likely depends on which paint path a given call site hits |
| Overflow/scroll | **SUPPORTED (in-renderer); NOT via scroll_surface/panel2d** | `overflow_hidden`/`overflow_auto_y`/`overflow_scroll_y` drive real clip/scroll (`paint_layout.spl:23,41,855,2007-2100`). `grep -rl "scroll_surface\|panel2d" browser_engine/*.spl` = 0 matches — those are separate widget/WM abstractions, not part of the HTML/CSS path |
| Stacking contexts | **SUPPORTED for position:absolute; UNVERIFIED for relative/sticky/flex/grid** | Real z-index sort `_z_index_sort_before` (`core.spl:2188-2220`); paint splits absolute elements into `z_index<=0` vs `>0` deferred groups (`paint_layout.spl:741,775-778,1982`). Full CSS stacking-context formation for other position/layout modes was not traced this session |

## 4. Gap table (ranked)

"GPU needed to verify" = true only where the feature is inherently a
raster/shader concern that a CPU-only spec cannot meaningfully prove (per the
board-runnable rule and the campaign's own stance: CPU is the executable spec,
GPU parity is a separate, later proof).

| # | Feature | Needed by | Current state | Size to close | GPU needed to verify |
|---|---|---|---|---|---|
| 1 | Text decoration unification (overline/strikethrough, single source of truth) | web, both indirectly (widget text) | PARTIAL / inconsistent — two paint paths disagree | S | No |
| 2 | Radial gradients + angled linear gradients + N-stop | web (also useful to game for radial vignettes) | ABSENT (radial), PARTIAL (linear, 2-stop, no angle) | M | No |
| 3 | Rounded-gradient clip | web | ABSENT (explicit TODO comment) | S–M | No |
| 4 | Per-command/paint-time affine transform (rotate/scale/skew, arbitrary angle) at the DrawIR or browser-paint layer | both — game has its own `Transform2D` but it does not flow into DrawIR; web has only a layout-geometry approximation | ABSENT at DrawIR; PARTIAL (quarter-turn only) at web paint | L | No (CPU rasterizer can do affine sampling) |
| 5 | Blend-mode wiring into sprite/particle draw calls | game | PARTIAL — primitive exists (`emu_draw_rect_blend_mode`), unwired | S–M | No |
| 6 | Tilemap real texture sampling (vs flat-color placeholder) | game | PARTIAL, explicit placeholder | S–M | No |
| 7 | CSS filter functions beyond `opacity()` (blur/drop-shadow/grayscale/etc) | web | ABSENT | M–L | Maybe (blur can reuse existing glass-material blur primitive on CPU) |
| 8 | CSS `isolation`/isolated blend groups, per-command opacity | web | ABSENT | M | No |
| 9 | Game↔web convergence: unify `Transform2D`/`ZIndex` (game) with `layer`/x-y (DrawIR) so game sprites and web nodes share one transform+z model instead of two parallel systems | both | ARCHITECTURAL GAP, not a missing primitive | L (design first) | No |
| 10 | Duplicate texture-atlas implementations (`engine/sprite/atlas.spl` vs `game2d/render/texture_atlas.spl`) | game | Debt, not a feature gap, but blocks confident atlas work | S (consolidate) | No |
| 11 | Full stacking-context formation (relative/sticky/flex/grid, not just absolute) | web | UNVERIFIED — needs a dedicated read before scoping | Unknown until surveyed | No |
| 12 | Render-to-texture game-layer consumer (minimap/particle post-fx) | game | Primitive SUPPORTED, no consumer found | S–M (once a concrete use case is picked) | No |
| 13 | Field-level DrawIR patch (vs whole-command replace) + per-frame adoption of diff/patch | both (perf) | SUPPORTED structurally, unused in the frame path (per campaign D9 notes) | L | No |
| 14 | Tween/easing helpers for animation | game | ABSENT | S | No |

Items 1, 3, 5, 6, 10 are the cheapest, most self-contained lanes. Item 4 is
the single biggest structural hole shared by both consumers and should be
scoped carefully (it touches DrawIR's core struct, so it is not "add a
field" — see lane breakdown).

## 5. Recommended lane breakdown

Each sized to be one reviewable change with its own spec, following the
existing campaign's lane pattern (D8: new code in `common/` only; SSpec
mirrors source path; cite `Results:` lines, not per-example ticks).

1. **Lane GAP-1 — Text decoration unification.** Add `overline`/
   `line-through` fields to `simple_web_html_layout_renderer_style.spl`'s
   `Style` struct, make `paint_layout.spl` the single paint path (retire or
   redirect the `layout_paint.spl`/`text_painter.spl` legacy path), one spec
   asserting all three decorations render identically regardless of entry
   point. No GPU needed.

2. **Lane GAP-2 — Gradient upgrade.** Extend
   `draw_gradient_rect`/`parse_linear_gradient_color` to N-stop + angle;
   add `radial-gradient` parsing and a radial paint primitive; fix the
   `Ndeg`-misparsed-as-color-stop bug found in this survey
   (`foundation.spl:1027-1049`). Depends on nothing. Spec: stop-count,
   angle, and radial cases against known pixel output.

3. **Lane GAP-3 — Rounded-gradient clip.** Close the explicit
   `draw_ir_adv.spl:635-637` TODO: apply the corner-radii clip before
   painting a gradient rect. Small, self-contained once GAP-2 lands (shares
   the gradient paint call site).

4. **Lane GAP-4 — Blend-mode wiring.** Thread `BlendMode` from
   `nogc_sync_mut/engine/render/types.spl` through the sprite/particle draw
   call path into the already-real `emu_draw_rect_blend_mode` primitive.
   Spec: additive/multiply/screen produce the expected composited pixel for
   a 2-sprite overlap.

5. **Lane GAP-5 — Tilemap texture sampling.** Replace the flat-color
   placeholder in `game2d/tilemap.spl` with real `TextureRegistry`-backed
   sampling (first resolve which of the two atlas implementations is
   canonical — see GAP-10). Depends on GAP-10 if the atlas consolidation
   is done first; otherwise pick one atlas explicitly and record the other
   as deprecated.

6. **Lane GAP-10 — Atlas de-duplication.** Diff
   `nogc_sync_mut/engine/sprite/atlas.spl` vs
   `nogc_sync_mut/game2d/render/texture_atlas.spl`, pick the canonical one
   per D8-style dedup rules, delete/redirect the other. Prerequisite for
   GAP-5 to avoid building on the wrong one.

7. **Lane GAP-4T — Affine transform at paint time (the big one).** Design
   step first (not code): decide whether rotation/scale/skew becomes a new
   optional field on `DrawIrCommand`/`DrawIrEmbeddingConfig` (cheap, but
   every one of the ~14 render backends needs to honor it or silently
   ignore it — same fan-out risk noted for D9's `read_pixels_with_source`)
   or a paint-time wrapper that pre-transforms rect geometry on CPU before
   handoff (no backend changes, but loses GPU-side transform acceleration
   later). Recommend the latter as Stage A (CPU pre-transform, matches the
   project's own D6-style staging precedent), matrix-in-backend as a future
   Stage B. This lane should also decide whether game's `Transform2D` and
   DrawIR converge (ties to GAP-9) or stay parallel — that decision, not
   the code, is the actual deliverable of a first sub-lane.

8. **Lane GAP-11 — Stacking-context audit.** Pure survey lane (like this
   one): read `core.spl`/`paint_layout.spl` for `position: relative`,
   `sticky`, flex, and grid to determine whether z-ordering is correct
   beyond the already-confirmed `position: absolute` path. Blocks nothing
   else; unblocks a future GAP-9-adjacent web-correctness lane if gaps are
   found.

Not recommended as near-term lanes: GAP-7 (CSS filters beyond opacity) and
GAP-13 (field-level patch adoption) are real but large and lower-urgency —
park them behind the above until GAP-1/2/3/4/5/10 prove out the lane
pattern on this surface.

## Sources

Three parallel research passes, each independently grepping and reading
source (not each other's output): DrawIR core (`draw_ir.spl`,
`draw_ir_adv.spl`, `draw_ir_box_effects.spl`, `draw_ir_target.spl`,
`draw_ir_diff.spl`, `draw_ir_patch.spl`, `panel2d.spl`), 2D game renderer
needs (`game2d/*`, `engine/render/*`, `engine/sprite/*`), GUI/web renderer
needs (`browser_engine/simple_web_html_layout_renderer_*.spl`,
`widget_draw_ir.spl`). Struct definitions for `DrawIrCommand`,
`DrawIrEmbeddingConfig`, `DrawIrBatch`, `DrawIrComposition`
(`draw_ir.spl:57-107`) and `_E2D_BOX_MAX_SHADOW_LAYERS`/box-effect classes
(`draw_ir_box_effects.spl:13-47`) were independently re-read and confirmed by
the synthesizing session.
