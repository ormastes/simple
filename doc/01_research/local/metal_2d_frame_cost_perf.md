# Research — Metal 2D frame cost: profile, fixes, remaining directions

Scope: the user-flagged Metal 2D frame cost ("seems perf bug"). Architecture
was ruled in-bounds and is NOT the problem; the costs were two concrete
submission/marshalling bugs plus one missing frame-clear contract. All
measurements on aarch64-apple-darwin, seed driver, `--features
gui,metal,runtime-symbol-table`, 320x240, interpreted-JIT lane (the
2026-09-02 `rt_struct_alloc` table fix active).

## Measured frame breakdown (before fixes)

One overview frame (59 commands, ~30 text): composition 3038ms, present
46232ms, readback ~800ms. FRAMES=3 = 212s (~62-71s/frame steady).

Present-path anatomy (measured by direct probes):
- `select_font_identity`: 11ms once per process (idempotent afterwards).
- `draw_text_with_advances` x30 direct: 3.7s total (~123ms/text incl.
  staging, batch build, device dispatch).
- **~360 per-quad Metal submissions per frame** — every glyph quad got its
  OWN command buffer + encoder + commit + `waitUntilCompleted`, ~10ms fixed
  cost each: ~36s of the 46s present. THIS was the perf bug, not TTF
  rasterization and not the architecture.
- Atlas upload: a per-pixel `rt_ptr_write_i32` loop, ~1M FFI calls per
  1024x1024 atlas upload (~1-2s per upload, once per atlas generation).
- Glyph rasterization: cached per (face, size, glyph); ~50 glyphs once per
  process, not per text and not per frame.

## Fixes landed (backend_metal_font.spl)

1. **One encoder per batch, not one command buffer per quad.** The font
   composite now binds atlas+framebuffer once, re-stages each quad's params
   with `setBytes`, dispatches in the same encoder, and does exactly ONE
   commit + ONE completion wait per batch. 360 round trips/frame -> 30.
2. **One-call atlas marshalling.** `_upload` now uses the existing
   `metal_write_u32s_to_ptr` helper (the helper's own comment documented the
   per-pixel loop as the problem it was built to kill).
3. **Per-frame framebuffer clear** in `showcase_run_gpu` and
   `showcase_run_with_backend` — matches the 2D software host's
   `surface.clear` contract; without it, screen switches left stale pixels
   visible through the glass theme's translucent surfaces (no full-window
   opaque bg rect exists).

## Measured after fixes

- FRAMES=1: 57s -> 21s. FRAMES=10: 40.4s total => steady-state ~2.9s/frame
  (**~0.34 fps, ~21x faster**), output byte-identical (same checksums).
- present 46s -> ~10s first frame (includes one-time font staging); the
  remaining steady costs are composition ~0.4s and present ~2.5s per frame.
- One-time per process: module+font loading and glyph raster (~11s).
  `showcase_hosts_spec` 24/24 still green.

## Update 2026-09-05 — the first remaining direction is now done

The first font bullet below ("batch all of a frame's text batches into ONE
encoder") landed, and went further than the bullet described: Metal now
carries the whole Vulkan shape, not just one encoder per frame.

- **Packed params.** `metal_font_packed_params` emits the same words
  `vulkan_font_packed_params` emits — 8 header words, then 7 per glyph — and
  one dispatch composites every glyph of a batch, with y of the dispatch grid
  selecting the glyph. Previously each quad got its own `setBytes` plus its
  own dispatch. The MSL twin is `font_atlas_composite_metal_packed_source`.
- **Warm pool.** Packed buffers are reused across frames, one slot per batch
  still pending in the frame. A single shared buffer is wrong here: batch N+1
  would overwrite it before batch N's dispatch ran.
- **One submission per frame.** A frame's text now rides in one deferred
  command buffer; `flush()` owns the single commit and the single wait, and
  runs before device readback, before present, in `submit_batch`, and before
  each of the six immediate command-buffer sites so paint order holds.
- **Mirror skipped in gpu-only mode.** The per-quad `font_atlas_subrect_pixels`
  extraction only ran to feed the CPU mirror, so it is now skipped when the
  mirror will not be read.

Evidence is contract-level, not a new timing: `metal_font_packed_parity_spec`
(5/5) proves the Metal packed words are byte-identical to the Vulkan packed
bytes for the same batch, that both share the header shape, glyph cap and
dispatch arithmetic, and that the frame contract accepts only one command,
one commit and one wait. **The numbers below were NOT re-measured** — this
host has no Metal-featured binary (`src/compiler_rust/target/bootstrap/simple`
is built without the `metal` feature), so the 21x figure stands as the last
real measurement and the packed path's own speedup is unmeasured. Re-measure
on a Metal host before quoting any new number.

The remaining bullets below are still open.

## Remaining directions (no arch change)

Font (~2.5s/frame steady):
- ~~Batch all of a frame's text batches into ONE encoder (currently one per
  text, ~30x10ms = 0.3s) — small win, same pattern as fix #1.~~ **DONE
  2026-09-05, see the update above.**
- Readback region-limit: read only the changed band instead of the full
  320x240 download (~0.8s -> sub-second); a region readback seam already
  exists for the parent-material path (`_engine2d_read_pixels_region`).
- If interactive rates are ever required: the 5x7 bitmap glyph-blit lane
  (no TTF staging at all). The showcase routes text through TTF by design
  today; that is a content choice, not a defect.

Composition (~0.4s/frame steady, ~2.4s first call incl. one-time font
identity resolution):
- `compute_layout` is only 3ms; `widget_tree_to_draw_ir` is ~0.4s. The
  per-frame full rebuild is the cost. The tree is mostly static between
  frames: an incremental/dirty-region composition (the repo already has
  `common/ui/dirty_region.spl`, `draw_ir_diff.spl`) would let the loop
  re-emit only changed subtrees — the largest remaining steady win without
  touching the architecture.
- `get_internal_prop` scans the global widget-props store linearly; with
  many accumulated trees (multi-build processes) it grows. A per-prefix map
  or indexed store would cap it (small, but hot in every event reducer).

## NOT the problem

- Architecture/executor design: fine.
- TTF glyph rasterization: cached properly, once per glyph per process.
- Atlas upload frequency: once per atlas generation (cache identity works).
- Device readback: ~0.8s/frame, real device pixels.
