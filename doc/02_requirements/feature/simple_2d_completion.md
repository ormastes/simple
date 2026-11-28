# Feature Requirements: Simple 2D Completion (`release/1.0.0`)

- **Date:** 2026-11-28
- **Status:** Approved by User (Option A)
- **Target Branch:** `release/1.0.0` (never `main`)
- **Worktree:** `/Users/ormastes/work/web_2d_gui_2d` (`work/simple-2d-complete`)
- **Local Research:** `doc/01_research/local/simple_2d_completion_2026_11.md`
- **Domain Research:** `doc/01_research/domain/simple_2d_completion_2026_11.md`

## Selected Scope: Focused Engine2D GPU/Damage + Skia Core Parity

| ID | Requirement | Verified Gap / Anchor | Priority |
|---|---|---|---|
| `REQ-S2D-001` | Focused themed WM window (`opacity_milli == 1000`) renders bit-identical corners on Vulkan fresh-device vs CPU (`engine2d_focused_window_corner_device_spec.spl` passes without `@tag:in-development`). | `draw_ir_adv.spl:5297-5303`, `draw_ir_box_effects.spl:1415-1555`, `backend_vulkan_glsl.spl:702-713` | P2 |
| `REQ-S2D-002` | Prepared damage plan & single-root damaged executor admit `opacity_milli < 1000` embedded batches consistently with `_engine2d_draw_ir_render_composition_damaged_with_images`. | `draw_ir_adv.spl:5014-5019`, `5639-5647` | P2 |
| `REQ-S2D-003` | Retained damage replay touching layered windows on Vulkan reuses device offscreen / device-to-device composite instead of per-replay offscreen alloc + readback. | `draw_ir_adv.spl:5409-5438` | P2 |
| `REQ-S2D-004` | Parent-sampling (`fluid_light` / `aetheric_dark`) retained damage replay passes on Vulkan/device lane (`engine2d_wm_local_lane_clock_tick_spec.spl`). | `src/os/compositor/engine2d_wm_frame_executor.spl`, `wm_retained_damage_rejects_parent_sampling_window_material_2026-11-26.md` | P2 |
| `REQ-S2D-005` | Skia CPU `SaveLayer` allocates an isolated transparent offscreen `Bitmap` and `Restore` composites it onto parent with layer `alpha` and `SkBlendMode`. | `src/lib/skia/backend/cpu/backend.spl:208-238` | P2 |
| `REQ-S2D-006` | Skia CPU `DrawRect`, `DrawRRect`, `DrawOval`, `DrawPath`, `DrawImage`, `DrawPaint`, and transformed primitives honor `SkBlendMode` with coverage-weighted compositing and real destination pixel reads (`DrawImage`). | `src/lib/skia/backend/cpu/backend.spl:149-160, 308-426, 577-578` | P2 |
| `REQ-S2D-007` | Skia `SkCanvas` / `SkPictureOp` / `CpuBackend` preserve full 3x3 affine matrices (including shear/skew) across `concat` and `set_matrix`. | `src/lib/skia/entity/canvas.spl:79-100`, `picture.spl:30-39`, `backend.spl:266-279` | P2 |
