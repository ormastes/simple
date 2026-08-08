# Tile-Based Render Culling — Chrome cc/ Research and Repo Mapping

**Date:** 2026-08-02 · **Status:** Research (docs-only; implementation planned in
`doc/03_plan/ui/rendering/tile_render_culling_plan.md`)

Goal: cull paint work for content that is hidden (`display:none`,
`visibility:hidden`, occluded, zero-area) or scrolled out of the viewport,
modeled on Chrome's tiled compositing (`cc/`).

Sourcing note: this section is written from model knowledge of Chromium's
`cc/` design docs and source layout (WebFetch is blocked in this session).
The *architecture* below (recording vs raster split, tiling sets, priority
bins, occlusion tracker, damage tracker, checkerboarding) is stable, long-
documented Chromium design and can be treated as authoritative. Specific
*constants* (exact tile sizes per platform, prefetch margins, skewport
extrapolation factors) have drifted across Chromium versions and are marked
"recalled — verify before citing".

## 1. Chrome cc/ architecture

### 1.1 Recording: PictureLayer / DisplayItemList

- Blink paints each composited layer into a **display list** (paint ops /
  `PaintRecord`, historically `SkPicture`), not directly into pixels. The
  `PictureLayer` owns the recording; rasterization is a separate, later,
  schedulable step.
- Recording is bounded: for very tall layers only an **interest rect /
  recorded viewport** around the visible area is recorded (recalled: a few
  thousand px past the viewport), so even the recording step is
  viewport-bounded on huge documents.
- Key property this buys: paint ops are *data*. They can be binned, culled,
  re-rastered at other scales, and replayed per tile without re-walking the
  DOM.

### 1.2 Tilings at multiple scales

- `PictureLayerImpl` owns a `PictureLayerTilingSet`: one tiling per raster
  scale. The **ideal scale** = device scale × page scale × layer transform
  scale. During pinch-zoom, old-scale tilings are kept temporarily so
  something is always drawable; non-ideal-scale tiles draw scaled until
  ideal-scale tiles arrive. A LOW_RESOLUTION tiling (recalled: eighth-ish
  scale) may back fast scrolls cheaply.
- Each tiling is a regular grid over layer content space (`TilingData`),
  with 1-texel shared borders for filtering seams.
- **Tile size:** 256×256 is the classic software-raster default; 512×512
  (and viewport-width strips) are used for GPU raster (recalled — exact
  per-platform policy varies by version). Two forces set the size: smaller
  tiles cull tighter and re-raster less on damage; larger tiles mean fewer
  draw calls/allocations and less border overhead.

### 1.3 TilePriority

Each tile gets a priority from the visible rect and scroll trajectory:

- **Bins:** NOW (intersects visible rect), SOON (within the *skewport* —
  the visible rect extrapolated along current scroll velocity), EVENTUALLY
  (within the eventually-rect: visible rect expanded by a fixed prefetch
  margin; recalled: on the order of 3000px), and not-prioritized beyond it.
- **Ordering inside bins:** distance-to-visible-rect (screen-space) and
  ideal-vs-non-ideal scale: ideal-scale NOW tiles first; non-ideal tiles
  are kept only while they cover for missing ideal tiles.
- Priorities feed a memory budget: tiles past the budget are dropped
  farthest-first.

### 1.4 Occlusion tracking

- During the front-to-back draw-order traversal that builds the compositor
  frame, an **OcclusionTracker** accumulates the union of *opaque* regions
  drawn so far (as an axis-aligned region, `SimpleEnclosedRegion` — a
  deliberately conservative approximation).
- Each layer's visible rect is reduced by subtracting the accumulated
  opaque region; fully-occluded layers/tiles/quads emit nothing and are not
  rastered. Only content flagged opaque (opaque background, no rounded
  corners/filters/partial opacity, axis-aligned) contributes to the
  occluding region — translucency never occludes.
- Net effect: work is proportional to what a user can actually see, even
  with heavy overdraw stacks.

### 1.5 Raster scheduling and checkerboarding

- The `TileManager` turns prioritized, budgeted tiles into **raster tasks**
  on a worker pool (`TaskGraphRunner`); decode dependencies (images) are
  edges in the task graph. Raster targets come from a raster buffer
  provider (software bitmap, GPU, one-copy staging, zero-copy).
- If a NOW tile is not ready at draw time, cc draws a **checkerboard**
  (solid background-color quad) instead of blocking the frame — trading
  visual completeness for guaranteed frame cadence. Pending-tree activation
  waits on "required for activation" tiles to bound how much checkerboard
  a commit can introduce.

### 1.6 Damage / invalidation

- `Layer::SetNeedsDisplayRect(r)` records an invalidation rect; only tiles
  intersecting the invalidation are re-rastered — all other tiles keep
  their textures.
- A `DamageTracker` unions per-layer damage (invalidations + property
  changes like transform/opacity) into a per-render-surface damage rect,
  enabling partial swap: only the damaged screen region is recomposited /
  presented.

### 1.7 Scroll offset translation vs re-raster

- Compositor-thread scrolling only changes a layer transform: existing
  tile textures are re-presented at a new offset — **zero re-raster** for
  the already-covered region. Raster happens only for tiles newly entering
  the skewport/eventually rect. This is the core reason Chrome scrolling is
  cheap; any plan here should preserve the same property (scroll = tile
  re-offset + raster of newly exposed tiles only).

## 2. Mapping to this repo

### 2.1 Current pipeline (browser_engine → engine2d)

- Entry: `simple_web_layout_render_html_software_pixels_at_scroll`
  (`src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer.spl:2497`)
  → parse → styles → `layout(...)` → `_simple_web_scrolled_layout(...,
  scroll_y)` which **shifts every box by scroll_y**, then paints the full
  framebuffer. Scroll today = full re-layout-shift + full re-paint; there
  is no tile retention (the anti-pattern §1.7 exists to avoid).
- CPU paint: `paint(nodes, styles, bx, by, bw, bh, ..., fb, fbw, fbh, ...)`
  (`.../simple_web_html_layout_renderer_paint_layout.spl:629`) is
  **immediate-mode**: a document-order loop over all nodes, painting
  backgrounds/borders/shadows then a text pass, directly into `fb: [u32]`
  via the `fb_*_clip` primitives in
  `simple_web_html_layout_renderer_paint_primitives.spl` (`fb_rect_clip:97`,
  `clip_intersect:82`, `fb_style_background_opacity_clip:613`, ...). Per-node
  clipping exists (`build_ancestor_clip_cache:28`, `paint_clip_at:51`,
  `ClipRect`), and hidden-node skips exist
  (`paint_layout.spl:43` — `display != "none" and not visibility_hidden and
  not content_paint_hidden_by_ancestor`; `:44` — `y < fbh`), but there is no
  bottom-edge/off-top culling symmetry, no op list, no tiles, no occlusion.
  A time-budget guard (`_web_budget_expired`) degrades by *truncating draw
  order*, not by prioritizing visible content — exactly the failure
  checkerboarding + priority bins are designed to replace.
- DrawIR paint-op path (the recording analog): the same file also emits
  retained commands — `_html_draw_ir_command`
  (`paint_layout.spl:1440`) + `_html_draw_ir_style_props:1133` produce
  `DrawIrCommand`s consumed by engine2d:
  `_engine2d_draw_ir_render_commands(engine, commands, offset_x, offset_y,
  images, ..., active_clip: DrawIrRect, ...)`
  (`src/lib/gc_async_mut/gpu/engine2d/draw_ir_adv.spl:1232`). `active_clip`
  is a single whole-batch clip — a ready-made seam for a per-tile clip loop.
- Packed display list: `src/lib/common/ui/draw_ir_v3.spl` —
  `DrawIrV3Scene:283` with typed tables including `DrawIrV3ClipTable:148`
  (`DrawIrV3Clip:242` = rect + corner_radius + parent chain) and
  `DrawIrV3TransformTable`. No viewport, tile, or priority concept in the
  scene schema today.
- Backends: `engine2d/backend_vulkan.spl:150 class VulkanBackend` already
  carries scissor-like clip state (`clip_x/clip_y/clip_w/clip_h/
  clip_enabled`, `:205-210`). `engine2d/backend_software.spl:48
  class SoftwareBackend` already has a **64×64 dirty-tile grid**
  (`TILE_SIZE=64:42`, `tiles_x/tiles_y/dirty_tiles:63-65`) — but only to
  minimize `present()` copies, not to cull painting or cache raster.

### 2.2 Existing plumbing (grep survey)

| Concern | Exists today | Where |
|---|---|---|
| Per-node clip rects | yes | `paint_layout.spl:28,51` (`PaintClipCache`), `paint_primitives.spl:82` |
| Viewport overlap test | yes (helper, barely used) | `engine2d/helpers_clip.spl:113 clip_rect_to_viewport` |
| Scroll offset | yes — box shift + full repaint | `simple_web_html_layout_renderer.spl:2497` + `_simple_web_scrolled_layout` |
| Hidden-content skip | yes (display/visibility/ancestor) | `paint_layout.spl:43,64,79` |
| Dirty tiles | yes — present-copy only, 64×64 | `engine2d/backend_software.spl:42-137` |
| Whole-frame dirty flag | yes | `engine2d/backend_intel.spl:92` (`dirty: bool`, full re-upload) |
| Batch clip on DrawIR replay | yes — single rect | `engine2d/draw_ir_adv.spl:1232,1438` |
| Vulkan clip/scissor state | yes | `engine2d/backend_vulkan.spl:205-210,377-379` |
| Layout invalidation frontier | yes — layout bits only | `browser_engine/gpu_web/layout/invalidation.spl` (`DIRTY_LAYOUT` etc.) |
| Paint-only damage rects | **missing** — `StyleDifference.PaintOnly` is dropped (`return merged` no-op) | `gpu_web/layout/invalidation.spl:53` |
| Occlusion mask (pixel-level) | partial | `engine2d/helpers_clip.spl:124 mask_blocks_at` (mask buffer, not region algebra) |
| Tile binning of paint ops | **missing** | — |
| Tile texture/raster cache | **missing** | — |
| Priority / prefetch margin | **missing** | — |
| Per-tile GPU submission/scissor loop | **missing** (name reserved: `backend_lane.spl:172 "dirty_tile_batch"`) | — |
| Occlusion by opaque later ops | **missing** | — |
| Frame pacing dirty region | coarse = full viewport | `engine2d/wm_frame_pacing.spl:99` |

### 2.3 Where a tile/culling stage fits

Pipeline today: layout boxes → (a) immediate `paint()` into fb, and
(b) DrawIR command emission → engine2d replay. The tile stage belongs
between op production and rasterization, in document space (pre-scroll):

```
layout boxes ──> paint-op list (DrawIR commands with document-space rects)
                    │
                    ▼
             TILE BINNING (fixed 256px grid over document space)
                    │   per-op: ops → tile id lists; opaque-op tracking
                    ▼
             TILE CULL (viewport rect + scroll offset → live tile set;
                        skip hidden/zero-area ops at bin time;
                        occlusion: drop tiles fully covered by a later
                        opaque op; damage: keep unchanged tiles' pixels)
                    │
        ┌───────────┴─────────────┐
        ▼                         ▼
  CPU raster per tile        GPU replay per tile
  (fb_* primitives with      (_engine2d_draw_ir_render_commands with
   clip = tile rect,          active_clip = tile rect; Vulkan
   only live tiles)           clip/scissor; skip culled tiles;
                              tile texture cache)
```

Concrete insertion points:

1. **Op-list producer** — reuse `_html_draw_ir_command`
   (`paint_layout.spl:1440`); the CPU lane gains the same op list rather
   than a second recording path (WebIR rejection stands: one display list).
2. **New tile module** — proposed
   `src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_paint_tiles.spl`
   (binning, live-set computation, per-tile checksums, occlusion) shared by
   both lanes; pure functions in the style of `helpers_clip.spl`.
3. **CPU raster loop** — a tiled sibling of `paint()`
   (`paint_layout.spl:629`) that iterates live tiles and calls the existing
   `fb_*_clip` primitives with `clip = tile ∩ ancestor clip` (the
   `ClipRect` plumbing already reaches every primitive).
4. **GPU replay loop** — wrap `_engine2d_draw_ir_render_commands`
   (`draw_ir_adv.spl:1232`) in a per-tile loop driving `active_clip`;
   Vulkan scissor via `VulkanBackend` clip state
   (`backend_vulkan.spl:205`); tile texture retention in
   `vulkan_session.spl`.
5. **Damage feed** — stop dropping `StyleDifference.PaintOnly`
   (`gpu_web/layout/invalidation.spl:53`): route it to per-tile dirty
   marking so style-only changes re-raster only affected tiles.
6. **Scroll** — `_simple_web_scrolled_layout` keeps producing document-space
   boxes; the tile stage translates the *viewport*, not the boxes, so an
   unchanged document scrolled by N px re-rasters only newly exposed tiles
   (§1.7 parity).

### 2.4 Deltas vs Chrome to keep in mind

- This repo's CPU lane paints node-by-node, not from a recording; the plan
  converts it to consume the DrawIR op list so both lanes share one culled
  input (otherwise culling logic forks).
- No impl/main thread split here; priority bins reduce to NOW +
  EVENTUALLY-margin (no skewport velocity model needed initially).
- The existing 64×64 SoftwareBackend tile grid is a *present* optimization
  in framebuffer space; the new 256px grid is in *document* space. They
  compose but must not be conflated.
- Chrome's budget answer is checkerboarding; this repo's is the
  `_web_budget_*` deadline. Tiling makes the budget degrade
  *outside-in* (drop EVENTUALLY tiles first) instead of truncating draw
  order mid-document.
