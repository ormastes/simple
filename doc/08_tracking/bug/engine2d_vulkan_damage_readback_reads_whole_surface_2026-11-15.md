# Engine2D Vulkan: damaged-rect composition reads back the whole surface

**Date:** 2026-11-15
**Status:** RESOLVED (2026-11-22)
**Severity:** P3
**Found by:** re-verifying `gui_content_renderer_parser_expected_pattern_found_use_2026-08-12`

## Symptom

`test/01_unit/lib/gc_async_mut/gpu/engine2d/draw_ir_adv_spec.spl`, case "stages
retained Vulkan composition damage for a partial host refresh": after
`engine2d_draw_ir_render_composition_damaged(engine, composition, [2, 1, 1, 1], true)`
on a 4x3 Vulkan engine, `engine.vulkan_present_readback_bytes()` is 48 (4x3x4,
the whole surface) where the spec's oracle is 4 (the one damaged pixel).
The pixel content is correct; only the readback size is wrong.

## Where seen

DGX Spark aarch64, real Vulkan backend, seed built from release/1.0.0 on
2026-11-15. The case is skipped on hosts whose backend is not "vulkan".

## Not established

Whether the damage rect is dropped before present, or the readback ignores it.

## Root Cause & Fix (2026-11-22)

### Root Cause
`engine2d_draw_ir_render_damaged_with_images` (`draw_ir_adv.spl`) stages disjoint dirty rects via `eng.stage_present_damage(damage_rects)` (`present_damage_valid = true`), renders under `set_clip(...)`, and then calls `eng.read_pixels_with_source()` **before** `eng.present()`.

Three interacting defects in `src/lib/gc_async_mut/gpu/engine2d/backend_vulkan.spl` caused full-surface readback (`48` bytes instead of `4` bytes on `4x3`):
1. `VulkanBackend.read_pixels_with_source()` checked `self._refresh_host_frame_damage()` (which requires `SIMPLE_VK_READBACK=native` and uses `frame_damage_*`) and **never checked `self.present_damage_valid and self.host_mirror_valid`** (`self._refresh_host_damage()`). It therefore fell through to full-surface download (`w * h * 4` bytes), set `host_mirror_frame_fresh = true` and `readback_frame_bytes = w * h * 4`, and then `present()` hit the `host_mirror_frame_fresh` dedup arm and copied `readback_frame_bytes` (`48`) into `present_readback_bytes`, bypassing `present()`'s own `_refresh_host_damage()` branch.
2. `_refresh_host_damage()` patched `self.host_buf` in place from `vulkan_sffi_read_buffer_regions_bytes` / `vulkan_sffi_readback_u32_alloc` without updating `self.last_host_checksum`.
3. `consume_damage_hint()` clamped draw damage hints to `[0, w) x [0, h)` without intersecting against `[clip_x, clip_x + clip_w) x [clip_y, clip_y + clip_h)` when `self.clip_enabled` was active, allowing clipped full-surface background rects to inflate `frame_damage`.

### Fix
- `src/lib/gc_async_mut/gpu/engine2d/backend_vulkan.spl`:
  - `read_pixels_with_source()`: when `self.present_damage_valid and self.host_mirror_valid`, invokes `self._refresh_host_damage()`, records `host_mirror_frame_fresh = true`, `readback_frame_bytes = self.present_readback_bytes`, and `readback_frame_rects = self.present_readback_rect_count`, and returns `Engine2DReadback` backed by the patched `host_buf`.
  - `_refresh_host_damage()`: incrementally updates `self.last_host_checksum` modulo `2147483647` as each damaged pixel overwrites `self.host_buf`.
  - `consume_damage_hint()`: intersects incoming draw hints with the active clip rectangle when `self.clip_enabled` is true.
- Regression spec added and verified: `test/01_unit/lib/gc_async_mut/gpu/engine2d/vulkan_clear_and_damage_readback_spec.spl` (7/7 passed).
