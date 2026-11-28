# Non-Functional Requirements: Simple 2D Completion (`release/1.0.0`)

- **Date:** 2026-11-28
- **Status:** Approved by User (Option 1)
- **Target Branch:** `release/1.0.0` (never `main`)
- **Worktree:** `/Users/ormastes/work/web_2d_gui_2d` (`work/simple-2d-complete`)

## Selected NFR Targets: Balanced Release Quality

| ID | Category | Target / Acceptance Metric | Verification Mechanism |
|---|---|---|---|
| `NFR-S2D-001` | Pixel Parity (Engine2D) | `0` differing pixels (bit-exact `RGBA8`) between CPU and Vulkan/MoltenVK on `engine2d_focused_window_corner_device_spec.spl`, `engine2d_themed_wm_fresh_device_spec.spl`, and `engine2d_retained_group_opacity_damage_spec.spl`. | `bin/simple test --no-session-daemon` |
| `NFR-S2D-002` | Pixel Parity (Skia CPU) | `11/11` scenes in `test/03_system/gui/reftest/parity/reftest_spec.spl` within `+-2` LSB per channel vs analytical goldens, plus shear/skew & `DrawImage` blend probe coverage. | `bin/simple test --no-session-daemon` |
| `NFR-S2D-003` | Zero Whole-Frame Readback | `0` whole-frame readback bytes in `emu_draw_rect_blend`, `VulkanBackend` staged-damage readbacks (`present_readback_bytes == damaged_area * 4`), and steady-state `present()` (`readback_bytes == 0` when `readback_frame == false`). | `rect_blend_reads_region_spec.spl` + Vulkan readback checks |
| `NFR-S2D-004` | Throughput / Latency | Selected Vulkan comparison `Simple p95 / C p95 <= 2.0x` on `check-vulkan-2d-c-compare.shs`; retained clock-tick damage replay `< 0.25x` full-frame duration on GPU. | `scripts/check/check-vulkan-2d-c-compare.shs` |
| `NFR-S2D-005` | MoltenVK Stability | Bounded `VkBufferImageCopy` 4-byte row alignment & explicit `TRANSFER_SRC_OPTIMAL` barriers; zero `completion_unknown` cascades across `>= 20` sequential frames. | MoltenVK/Vulkan frame sequence spec |
| `NFR-S2D-006` | Memory & Ownership | All offscreen layer `Bitmap`s (Skia `SaveLayer`) and Vulkan offscreen targets (`draw_ir_adv.spl`) have deterministic teardown/pool release. | SSpec allocation/teardown receipt check |
