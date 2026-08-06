# WS-D3 — Damage-driven present: investigation

Read-only audit of the CURRENT tree (2026-08-06). No renderer source modified.
**[V]** = verified by reading code · **[I]** = inference.
Owner file: `src/lib/gc_async_mut/gpu/engine2d/backend_software.spl` (999 lines).

---

## 1. Mark sites — enumerated [V]

Field `dirty_tiles: [bool]` `:65`, allocated `:118`, freed `:137`.
Primitives (all `me` methods — free-function `self` passing loses mutations, see
comment block `:686-694`): `mark_dirty(tx,ty)` `:794`;
`mark_pixel_dirty(x,y)` `:800`; `mark_span_dirty(x,y,len)` `:806` (single row).

Marking call sites: `:151-154` `clear()` marks **all** tiles · `:215` `fill_rect`
row span · `:394` fill inner span · `:443` `draw_image` opaque copy ·
`:652` `draw_image` blend (SIMD + scalar) · `:737` `indexed_fill` ·
`:829` `sw_set_pixel` · `:842` `sw_set_pixel_blend` · `:858` `sw_hline` ·
`:874` `sw_hline_blend`.

### 1a. Vector-draw API: marks are transitive and safe [V]
`draw_rect`, `draw_ellipse*`, `draw_circle*`, `draw_triangle*`, `draw_text*`,
`draw_image_scaled`, gradients all delegate to `emu_*` in `backend_emu.spl`.
Those free functions take `mut core: RenderBackend` — a **trait object** — and
write pixels **only** through public trait `me` methods, overwhelmingly
`core.draw_rect_filled(...)` (e.g. `backend_emu.spl:46-49`, `:100-117`).
`draw_rect_filled` on `SoftwareBackend` is the marked `:215` path. Trait method
list: `backend.spl:62-94` — it exposes **no** raw pixel/buffer accessor, so emu
physically cannot bypass marking. **[V]**

The `emu_draw_ellipse(self, ...)` call at `:669-689` *is* the
`self`-to-free-function shape of the mutation-loss bug, but pixel writes and
dirty writes travel the *same* `mut core` handle: if mutations were dropped,
nothing would render at all. Marks survive exactly iff pixels do. **[I, strong]**

### 1b. UNMARKED pixel-mutating paths — the correctness blockers
1. **`scale_alpha_in_place` `:504-522`.** Rewrites **every** pixel
   (`self.buf[i] = rgba(...)` `:521`) and marks **nothing**. **[V]** Used for
   partial-opacity offscreen compositing. Fix: mark all tiles.
2. **`init` `:118-127`.** Allocates `dirty_tiles` all-`false`, then fills the
   buffer with opaque black `:124`. First frame has empty damage but a fully
   written buffer. **[V]** Fix: `[true; tile_count]`, or force a full first present.
3. **Latent, not live: SIMD buffer identity swap.** `sw_fill_raw_span:746` and
   `sw_copy_raw_span:756` reassign `self.buf = rt_engine2d_simd_*(...)`; marking
   is done by the *caller* afterwards. Correct today; unguarded against a future
   caller that forgets. **[V]**
4. **`mark_span_dirty` is single-row by construction** `:806-815`. No rect-level
   marker exists; every vertical extent must be marked per row. All current
   callers do. **[V]**

Exhaustive grep of `self.buf[..] =` in the file — lines 124, 521, 635, 643, 650,
732, 761, 781, 785, 791, 828, 841 — every one is covered above. **[V]**

---

## 2. "Read by nobody" — CONFIRMED [V]
- `grep -rn '\.dirty_tiles' src/ test/` hits **only** `backend_software.spl`.
  The only reads are its own self-set loop `:151` and self-clear loop `:480`.
- `get_dirty_tiles()` at `tile.spl:102` exists in **three** tier copies
  (`src/lib/{gc_async_mut,nogc_sync_mut,nogc_async_mut}/compositor/tile.spl`)
  with **zero** call sites in `src/` or `test/`. Unrelated `TileManager`
  (runtime `tile_size` field, not `TILE_SIZE`).

**The claim holds: the marking cost is paid and the signal is discarded.**

---

## 3. Tile geometry [V]
```
val TILE_SIZE: i32 = 64                              # :42
self.tiles_x = (width  + TILE_SIZE - 1) / TILE_SIZE  # :115
self.tiles_y = (height + TILE_SIZE - 1) / TILE_SIZE  # :116
self.dirty_tiles = [false; tiles_x * tiles_y]        # :118
val idx = ty * self.tiles_x + tx                     # :795
```
Row-major, 64×64, one `bool`/tile. 1920×1080 ⇒ 30×17 = 510 tiles. Pixel→tile is
integer division; callers clip to `>= 0` first, so trunc-toward-zero is not live.

---

## 4. The present path [V]
`SoftwareBackend.present()` `:478-484` does **nothing but clear the dirty
array** — no flush. The backend owns a CPU buffer the compositor reads via
`read_pixels()` `:485-495`, which copies the **entire** buffer every frame,
unconditionally. `Engine2D.present()` `engine.spl:2692` dispatches by backend.

`present_rect(x,y,w,h)` is on the trait at `os/compositor/display_backend_core.spl:17`:

| genuinely partial? | backends |
|---|---|
| **YES** | win32 DIB — `hosted_backend_win32.spl:95,175` → `rt_win32_dib_present_rect` (`src/runtime/hosted_win32.c:56,619`) takes the rect |
| **partial** | `os/drivers/framebuffer/fb_driver.spl:520` — `mark_dirty_rect` + `swap_buffers`; but `flush_dirty_rects` only clears bookkeeping for MMIO/host modes |
| **NO — full present** | `hosted_backend.spl:179`, `hosted_backend_sdl2.spl:117,203`, `hosted_backend_winit.spl:131`, `hosted_backend_cocoa.spl:97,175`, `hosted_backend_gui_renderer.spl:84`, `compositor_engine2d.spl:324`, `os/desktop/shell_baremetal.spl:59` |
| **no-op stub** | `shared_mdi_framebuffer_scene.spl:193`, `browser_compositor_backend.spl:114`, `host_compositor_core.spl:530` (`self.w = self.w`) |

**Only Win32 has a true partial present.** So the win is *not* at the present
syscall — it is in skipping the full-buffer `read_pixels()` copy and the
per-tile composite upstream of it. That is the real 10-100× target. **[I]**

Existing precedent to reuse: `host_compositor_core.spl:1474` already unions a
bounding rect (`host_background_bounding_rect` `:2111-2131`) for `present_rect`,
capped by `HOST_BACKGROUND_REGION_DIRTY_MAX_RECTS` `:2100`. **[V]**

---

## 5. Widget-layer hook-in [V/I]
`DrawIrV3Scene` (`src/lib/common/ui/draw_ir_v3.spl:285-299`) carries
`schema/schema_id/scene_id/generation/commands` + side tables. There is **no
bbox, no damage rect, no per-command bounds, no invalidation concept anywhere in
DrawIR v3** — grep for `bbox|bounding|invalidate|damage` across
`draw_ir_v3*.spl` + `window_scene_draw_ir.spl` yields one unrelated comment
(`draw_ir_v3_emit_full.spl:1139`). Widget damage would be **new**. **[V]**

Cheapest-first **[I]**: (1) **backend-level, no DrawIR change** — consume
`dirty_tiles` after scene replay; **recommended for D3**. (2) **scene-level** —
`generation` already exists (`draw_ir_v3_ports.spl:90 present(scene_generation)`),
unchanged generation ⇒ zero damage, a free early-out. (3) **per-command bbox** —
largest change, defer past D3.

---

## 6. Recommendation
1. Fix §1b-1 and §1b-2 **first**. Without them damage present is *incorrect*.
2. Add `me take_damage_rects(max_rects: i32) -> [Rect]`: scan `dirty_tiles`
   row-major, emit row run-length segments, merge, then clear — folding the
   existing `present()` clear loop in, so exactly one owner clears.
3. Merge heuristic: merge when `area(union(a,b)) <= (area(a)+area(b)) * k`,
   `k = 1.5`. Cap at **16** rects (8-32 band); past the cap collapse to the
   single bounding rect. Fall back to full-screen if the bound exceeds ~60% of
   the surface — a partial path costing more than a memcpy is a loss.
4. Consumer: **no persistent-mirror consumer exists today.** Every
   `read_pixels()` caller is an app/test that allocates a fresh full array per
   call (`src/app/wm_compare/production_gui_web_renderer_parity.spl:244,254`;
   `src/app/game.rollball/game.spl:288,297`;
   `src/app/test/renderdoc_vulkan_capture.spl:117`). **[V]** A per-rect copy
   therefore requires introducing a frame-persistent mirror buffer — a
   structural prerequisite, not a drop-in. On the nine full-present backends,
   issue **one** `present_rect` with the overall bounding rect.
5. **Risk to test: stale pixels from a missed mark** — invisible unless the
   whole buffer is compared.

**Boxed-pixel implication [V, external]:** pixels are boxed `int64_t`
(`engine2d_box_pixel`/`unbox_pixel`, `src/runtime/runtime_simd_dispatch.c:663/667`),
not packed u32. A tile copy is 8 B/pixel with per-element box/unbox, not a
`memcpy`. Skipping pixels is worth proportionally *more* than in a packed
renderer, but per-tile copy loops are expensive — merge damage into few, large,
row-contiguous spans and feed the bulk `rt_engine2d_simd_copy_span_u32`
primitive rather than copying tile by tile. **[I]**

---

## 7. Test that catches a missing mark
Suggested `test/01_unit/lib/gpu/engine2d/backend_software_damage_spec.spl`:
```
1. b_ref: init(W,H); draw S;  2. b_dmg: init(W,H); draw S; present()  # damage cleared
3. apply small-region mutation M to BOTH
4. full_expected = b_ref.read_pixels()                    # full-redraw truth
5. rects = b_dmg.take_damage_rects(); copy ONLY those rects out of b_dmg
   into a mirror seeded from the step-2 pixels
6. ASSERT mirror == full_expected for ALL W*H pixels
```
The assertion **must** span the whole buffer — one scoped to the damaged region
passes trivially when the damage set is wrong, which is exactly how this bug
class hides. Mutation cases, each failing today: `scale_alpha_in_place` (§1b-1);
a draw right after `init` with no `clear` (§1b-2); a `draw_image` straddling a
tile boundary; a 1px `sw_hline` on a tile seam; a clipped/masked slow-path draw.
Secondary oracles: rect count stays under the cap; a no-op frame yields **zero**
rects.

---

## 8. Interaction with the in-flight engine2d work
A parallel agent is adding in-place blend/blit kernels. Any new in-place kernel
writing `self.buf` **must** carry a `mark_span_dirty` — and
`scale_alpha_in_place` (§1b-1) is precisely an existing in-place kernel that
does not. Land the §1b fixes and the §7 whole-buffer test **before** consuming
damage, and re-run the §1b grep (`self.buf[..] =` in `backend_software.spl`)
after their change lands: each new in-place kernel is a new candidate hole.
Do not assume their rebase preserved marking.
