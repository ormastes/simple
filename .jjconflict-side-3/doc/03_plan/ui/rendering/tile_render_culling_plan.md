# Tile Render Culling Plan (CPU + GPU lanes)

**Date:** 2026-08-02 · **Status:** Proposed
**Research:** `doc/01_research/ui/rendering/tile_render_culling_chrome.md`
**Convention parent:** mirrors the work-group/gate structure and
shadow → candidate → promotion flow of
`doc/03_plan/platform/structural_compute/webrender_gpu_offload_plan.md`
(and its parent's flag-off byte-identical rule). DrawIR v3 remains the one
shared display list — this plan adds a *stage*, not a second format
(WebIR rejection stands: `doc/03_plan/ui/webir_drawir_optimization.md`).

## Scope

Cull paint/raster work for content that cannot be seen: `display:none`,
`visibility:hidden`, hidden-by-ancestor, zero-area, scrolled out of the
viewport, or occluded by later-in-paint-order opaque content. Chrome-style
fixed tile grid (256px, document space) with per-tile visibility, damage
reuse, and (GPU lane) per-tile scissor submission + tile texture cache.

Out of scope: multi-scale tilings, skewport velocity model, raster worker
threads, pinch-zoom — recorded as follow-ups, not silently implied.

| Group | Content |
|---|---|
| T1 | Tile core: grid math, op→tile binning, live-set (viewport+scroll), op-level hidden/zero-area cull |
| T2 | CPU tiled raster lane (fb primitives per live tile) + damage reuse |
| T3 | Occlusion: opaque-op tracking, fully-covered-tile skip (both lanes) |
| T4 | GPU lane: per-tile `active_clip`/scissor submission, culled-tile skip, tile texture cache |
| T5 | Perf gate benchmark + CPU-vs-GPU decision rule, promotion evidence |

## Design

### Coordinate model

- Grid: fixed `TILE_PX = 256` over **document space** (pre-scroll). Tile id
  = `(tx, ty)`; index `ty * tiles_x + tx`. Document height comes from
  layout output; width from render width.
- Viewport rect in document space = `(0, scroll_y, width, height)` (extend
  to `scroll_x` when horizontal scroll lands). Live set = tiles
  intersecting viewport, plus an `EVENTUALLY_MARGIN_PX = 512` prefetch band
  (2 tile rows) above/below — margin is a tunable constant, one place.
- Scroll changes the *viewport*, never the binned rects:
  `_simple_web_scrolled_layout` output feeds op emission once; scrolling by
  N px re-uses all still-covered tiles and rasters only newly exposed ones.

### T1 — Tile core (shared, pure functions)

New file
`src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_paint_tiles.spl`
(pure-function style of `engine2d/helpers_clip.spl`; no classes, no state):

- `tile_grid(doc_w, doc_h) -> TileGrid` (tiles_x/tiles_y).
- `tile_bin_ops(commands: [DrawIrCommand], grid) -> TileBins` — per-op
  device rect → covered tile-index range (O(ops × covered tiles)); ops with
  zero area, `display:none`, `visibility:hidden`, or hidden-by-ancestor are
  **dropped at bin time** (the checks already exist:
  `paint_layout.spl:43,64,79`; binning must call the same predicates, not
  reimplement them).
- `tile_live_set(grid, viewport, margin) -> [bool]` — reuses
  `clip_rect_to_viewport` logic (`engine2d/helpers_clip.spl:113`).
- `tile_checksum(ops-in-tile) -> u64` — FNV-1a over each op's kind, rect,
  style-prop hash, resource id, in tile-local order. Checksums drive damage
  reuse (T2/T4). Note native-codegen Dict pitfalls
  (`.claude/rules/code-style.md`): use arrays indexed by tile index, never
  `Dict.len()`/`Dict.get()` with struct values.
- Op producer: reuse `_html_draw_ir_command` (`paint_layout.spl:1440`) so
  CPU and GPU lanes cull one identical op list.

### T2 — CPU tiled raster lane

- New `paint_tiled(...)` sibling of `paint()` (`paint_layout.spl:629`):
  outer loop over live tiles (skip non-live), inner loop over that tile's
  binned ops, rasterizing with the existing `fb_*_clip` primitives
  (`simple_web_html_layout_renderer_paint_primitives.spl`) with
  `clip = tile rect ∩ op's ancestor ClipRect` via `clip_intersect`
  (`paint_primitives.spl:82`). Draw order inside a tile = original op
  order (bin preserves sequence), so output is order-identical.
- Damage reuse: keep previous frame's per-tile checksum + the framebuffer;
  a tile whose checksum and scroll-relative position are unchanged is
  copied (or left in place) instead of re-rastered. Per-tile pixel store is
  the frame's fb itself when size is unchanged; a row-band copy handles
  scroll deltas that are a multiple of 1px (memmove of fb rows), i.e.
  scroll = translation + newly-exposed-tile raster only.
- Budget interaction: `_web_budget_*` now degrades outside-in — raster NOW
  (visible) tiles first, then margin tiles; on expiry, unpainted *margin*
  tiles are simply absent (never a half-painted visible document).
- Flag: `SIMPLE_WEB_TILE_PAINT=0|1` (default 0). Flag-off path is
  byte-identical: `paint_tiled` is a separate function; `paint()` is not
  modified beyond the dispatch site.

### T3 — Occlusion (both lanes)

- During binning, track per tile a conservative opaque coverage: an op
  contributes only if axis-aligned rect, alpha=255 fill, opacity 100%, no
  corner radius/shadow/gradient-with-alpha (predicate
  `_op_is_opaque_rect`). Chrome-style region algebra is overkill for v1:
  per tile keep the single latest opaque op that **fully contains the tile
  rect**; every earlier op in that tile is culled (back-to-front paint ⇒
  later fully-covering opaque op hides all prior content in that tile).
- This is deliberately weaker than Chrome's accumulated-region subtraction
  (it only catches full-tile coverage by one op) but is exact-safe and
  covers the common overlay/modal/sticky-header cases. Region-union
  occlusion is a recorded follow-up, gated on benchmark evidence.

### T4 — GPU lane (engine2d)

- Per-tile replay: wrap `_engine2d_draw_ir_render_commands`
  (`engine2d/draw_ir_adv.spl:1232`) in a live-tile loop passing
  `active_clip = tile rect` (the parameter exists; today it is one
  whole-batch rect, `draw_ir_adv.spl:1438`). Culled tiles: no call at all —
  no clear, no submission.
- Vulkan: drive `VulkanBackend` clip state
  (`engine2d/backend_vulkan.spl:205-210`) as the scissor per tile;
  per-tile clear only for live+dirty tiles. Batch all live tiles of a
  frame into one command submission (per-tile *recording*, single submit)
  to avoid per-tile submit overhead — mirrors the parent plan's "no
  per-widget submission" proof.
- Tile texture cache: retain per-tile raster results keyed by
  `(tile index, checksum)` in `vulkan_session.spl`-owned memory; unchanged
  live tiles are composited from cache (blit/quad) without replaying ops.
  Cache capacity = live set + margin, evict farthest-from-viewport first
  (TilePriority reduced to distance ordering). Software lane may reuse the
  existing 64×64 `dirty_tiles` machinery of `SoftwareBackend`
  (`backend_software.spl:42-137`) for the present step, unchanged — the
  256px document grid and the 64px present grid compose; do not merge them.
- Damage feed: route `StyleDifference.PaintOnly` — today a dropped no-op
  (`browser_engine/gpu_web/layout/invalidation.spl:53`) — into per-tile
  dirty marks so style-only mutations invalidate only intersecting tiles.
- Flag: `SIMPLE_WEB_TILE_GPU=0|1` (default 0), independent of the CPU flag.

### T5 — Perf gate: benchmark spec + decision rule

Benchmark spec (sspec, `test/system/gpu/browser_engine/` lane;
per-repo test conventions):

- Fixture generator: document of `R` rows × mixed content (text, bordered
  boxes, images, gradients) sized so total document height ≈ `K ×`
  viewport height. Parameters: `K ∈ {5, 20}` (N% offscreen = 80%/95%),
  occluder overlay covering `M ∈ {0, 30, 70}`% of the viewport with an
  opaque panel, viewport 1280×720, scroll positions {0, mid, near-end},
  plus a 60-step 16px-per-step scroll sweep for damage-reuse measurement.
- Metrics per lane (CPU non-tiled baseline, CPU tiled, GPU tiled):
  **ops-painted** (ops actually rasterized after culling),
  **bytes-rastered** (Σ tile px × 4 for rastered tiles; baseline = full fb
  per frame), **wall time** per frame (median of ≥20 frames, warm), plus
  tile-cache hit rate on the scroll sweep. Counters are level-gated log
  fields on the tile stage (retained per log-retention policy).
- Expected shape: culling win ≈ proportional to offscreen% + occluded%;
  scroll sweep win ≈ (1 − newly-exposed fraction).
- **Decision rule (user-set):** if the CPU tiled lane's measured shortfall
  vs the GPU tiled lane is large on the gate fixture set — operationally:
  GPU tiled median wall time ≤ ½ CPU tiled on `K=20` fixtures at parity —
  the **GPU-optimized version ships as the default lane** (backend
  selection defaults to the engine2d tiled path where a device exists,
  CPU tiled remains the fallback + oracle). Otherwise CPU tiled is default
  and GPU stays opt-in. Either way both lanes land; the rule only picks
  the default.

## Acceptance

Per the webrender plan's gate style:

1. **Parity (blocking):** pixel-identical output vs the non-tiled renderer
   for the visible region, for every benchmark fixture × scroll position ×
   both lanes (checksum compare of the visible fb region; the existing
   render session readback is the oracle). Occlusion culling must be
   provably conservative: any parity diff disables T3 for that fixture and
   files a bug — never "close enough".
2. **Flag-off byte-identical:** with both flags off, rendered output and
   render-path call graph are unchanged (shadow → candidate → promotion,
   as in the webrender plan; promotion only on measured p50/p95 win
   including binning overhead).
3. **Cull-effectiveness floor:** on the `K=20, M=70` fixture:
   ops-painted ≤ 30% of baseline and bytes-rastered ≤ 25% of baseline;
   scroll-sweep re-raster ≤ 2 tile rows per 16px step after warmup.
4. **No-regression floor:** on a fully-visible single-viewport document
   (worst case for binning overhead), tiled wall time ≤ 110% of baseline.
5. **Coverage:** tile core (T1/T3) ≥ 95% line coverage via unit specs
   (grid math, binning edges: op spanning 4 tiles, exact tile-boundary
   rects, zero-area, negative coords); lane loops (T2/T4) exercised by the
   parity + benchmark specs on all three engines where applicable
   (interpreter oracle for tile-core math; JIT/native for lanes).
6. **Budget behavior:** with an artificially small `_web_budget`, visible
   tiles are complete before any margin tile is attempted (spec asserts
   raster order).

## Ordering and ownership

T1 → T2 (CPU proves parity + damage model) → T3 (occlusion on the proven
tile set) → T4 (GPU lane reuses T1/T3 verbatim) → T5 gate → default-lane
decision → promotion. Each group lands flag-off with its specs; nothing is
promoted before T5 evidence. Owned paths: the new `paint_tiles.spl`
module, one dispatch site in `simple_web_html_layout_renderer.spl`, the
per-tile loop in `engine2d/draw_ir_adv.spl`, Vulkan scissor/tile cache in
`engine2d/backend_vulkan.spl` + `vulkan_session.spl`, and the
`PaintOnly` route in `gpu_web/layout/invalidation.spl`.

## Open questions

1. Grid space for `position:fixed` / `background-attachment:fixed`
   content: viewport-anchored ops break document-space caching — likely a
   small "unbinned always-repaint" op class in v1.
2. `_simple_web_scrolled_layout` currently shifts boxes *before* op
   emission; the tile lane needs unshifted document-space ops. Does layout
   ever depend on scroll (sticky headers)? If so, sticky nodes join the
   unbinned class.
3. Tile texture cache memory ceiling on the Vulkan session (live+margin at
   1280×720 ≈ 6×4 tiles ≈ 6 MB @256px — fine; ceiling policy needed for
   large viewports / future multi-document sessions).
4. Text pass ordering: `paint()` runs a separate whole-document text pass
   after backgrounds; per-tile raster must interleave per tile
   (bg-then-text within a tile). Confirm no cross-tile text overdraw
   (glyphs crossing tile edges rely on clip-correct glyph rasterizers).
5. Should DrawIR v3 gain optional tile/viewport tables now, or does the
   stage stay entirely outside the scene schema until promotion? (Leaning:
   outside until promoted; schema changes ripple through I1–I12.)
