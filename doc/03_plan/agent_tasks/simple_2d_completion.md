# Agent Tasks: Simple 2D Completion

- **Date:** 2026-11-28
- **Target Branch:** `release/1.0.0` (never `main`)
- **Worktree:** `/Users/ormastes/work/web_2d_gui_2d`
- **Merge Owner:** Simple 2D Research/Impl Lead (branch `work/simple-2d-complete` / slice `work/*` branches)
- **Final Reviewer:** Separate self-review on `gh pr diff <n>` before `--admin --merge`

---

## Task Breakdown & Slice Plan

| Slice / PR | Scope | Files Owned | Sidecar Lane | Status |
|---|---|---|---|---|
| **Slice 0 (Docs)** | Step 1 Research + Step 2 Design / Test Plan / Agent Tasks | `doc/01_research/**`, `doc/02_requirements/**`, `doc/04_architecture/simple_2d_completion.md`, `doc/05_design/simple_2d_completion.md`, `doc/03_plan/**` | `N/A` | In Progress |
| **Slice 1 (PR 1)** | Engine2D corner AA parity, `opacity_milli < 1000` prepared/single-root admission, Vulkan pooled offscreen & device-to-device composite, specs + `doc/06_spec/` manuals | `src/lib/gc_async_mut/gpu/engine2d/{draw_ir_adv.spl,backend_vulkan.spl,engine.spl}`, `test/02_integration/rendering/engine2d_focused_window_corner_device_spec.spl`, `test/01_unit/lib/gc_async_mut/gpu/engine2d/{draw_ir_damage_plan_rejection_spec.spl,draw_ir_adv_spec.spl}`, `doc/06_spec/02_integration/rendering/**` | `N/A` (single focused lane) | Pending |
| **Slice 2 (PR 2)** | Skia CPU `SaveLayer` offscreen isolation, unified coverage-weighted Porter-Duff/W3C blend modes (`Screen` fix, `DrawImage` dst read, `DrawRRect`/`DrawOval`/`DrawPath`/`DrawPaint`/transformed `DrawRect`), lossless 3x3 affine matrices (`SkCanvas` + `CpuBackend`), SSpec + `doc/06_spec/` manuals | `src/lib/skia/entity/canvas.spl`, `src/lib/skia/feature/blend/blend_compose.spl`, `src/lib/skia/backend/cpu/backend.spl`, `test/01_unit/lib/skia/cpu_backend_blend_layer_matrix_spec.spl`, `doc/06_spec/01_unit/lib/skia/**`, `doc/06_spec/03_system/gui/reftest/parity/reftest_spec.md` | `N/A` (single focused lane) | Pending |
