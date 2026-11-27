# Vulkan web lane demotes to cpu_fallback on the tall/full-page render (800x2600), passes at <=800x1600

- **ID:** vulkan_web_fullpage_cpu_fallback_demotion_2026-08-10
- **Status:** OPEN
- **Found by:** gui/web/2D vulkan showcase sweep, 2026-08-10
- **Area:** `src/lib/gc_async_mut/gpu/engine2d/backend_vulkan*.spl` × the
  simple_web engine2d render path
- **Severity:** medium — the strict provenance gate fails closed (as
  designed), so this never publishes a false device claim; but the Vulkan
  lane silently does no device work for full-page-height renders

## Symptom

`SIMPLE_GUI_BACKEND=vulkan SHOWCASE_RESOLUTION=800x2600 simple run
examples/06_io/ui/web_standards_showcase_gui.spl` (seed binary, interpreted):

```
web_standards_showcase status=fail reason=backend-provenance requested=vulkan resolved=vulkan source=cpu_fallback handle=0
```

The same run at 320x240 and 800x600 passes the provenance gate with
`source=device_readback` (after the 2026-08-09 readback-order fix in
`draw_ir_adv.spl`); it then fails only the vector-font-evidence gate, which
needs the end-of-document witness in view — i.e. a TALL viewport — so the
tall run is precisely the config the gate flow needs, and it is the one that
demotes.

## What is ruled out

- **Framebuffer size.** A direct `VulkanBackend` probe (create/init/clear/
  rect/readback per size) returns `source=device_readback` with a live handle
  at 320x240, 800x600, 800x1200, 800x1600 AND 800x2600. The backend core
  serves the tall size on-device; the demotion comes from an operation in the
  page render (more text rows/glyph work and glass materials become visible
  at taller viewports), not from dimensions.
- **The witness/glyph-corruption suspects.** Glyph rendering was numerically
  verified correct (see
  `engine2d_font_glyph_stem_truncation_preview_artifact_2026-08-10.md`).

## Next diagnostic step

Surface `VulkanBackend.cpu_fallback_reason` in the web render result (it is
recorded but not printed by the showcase status line) and re-run the tall
config: the first `mark_cpu_fallback(...)` reason names the op that demotes
the lane. Likely suspects by code inspection: the image-copy host fallback
(`draw_image` native-status-0 path) or the font batch staging path once the
visible glyph count grows.

## 2026-08-10 update — traced: the 32nd command buffer's dispatch fails

An env-gated trace was added to `mark_cpu_fallback`
(`SIMPLE_VK_ORDER_TRACE=1` now prints the FIRST fallback reason) and the tall
run re-executed. Result:

```
[vk-order] dispatch pipe=24 batched=true rc=1 pending_cmd=31 ...   (ok)
[vk-order] dispatch pipe=24 batched=true rc=0 pending_cmd=31 pending_n=1
[vk-order] cpu-fallback-first reason=framebuffer-dispatch-failed
```

31 command buffers complete successfully; the follow-on dispatch on the 31st
returns rc=0 from the batched enqueue path
(`backend_vulkan_helpers.spl:_enqueue_framebuffer_compute` → one of
bind_pipeline/bind_descriptors/push_constants/dispatch returning false, or a
descriptor-create failure flushing to the CPU fallback). The backend core
serves 800x2600 and even 3840x2160 fine in a direct clear/rect probe (few
command buffers), so the trip point is the ~31st command buffer within one
session on this host — consistent with llvmpipe/host memory pressure (7.5 GB
RAM host that OOM-killed an interpreted 4K run earlier the same day), not a
hardcoded pool cap (descriptor pools are max_sets=1-per-set; the command
buffer Vec is unbounded).

## 2026-08-11 update — retry hardening landed; residual boundary is command-buffer creation

`_dispatch_framebuffer_checked` (backend_vulkan_helpers.spl) now retries a
failed batched dispatch ONCE on a fresh command buffer before latching the
CPU fallback. Traced tall-page run with the hardening armed:

- 43 dispatches that previously demoted the lane were recovered by the retry
  (`dispatch-retry pipe=24 after flush rc=1`).
- The eventual latch happens later and deeper: after ~31 successful command
  buffers, `vulkan_sffi_begin_compute` itself fails (the retry line shows
  `pending_cmd=0 pending_n=0` — no new command buffer could be started).
  The per-buffer lifecycle (one-shot free after fenced submit, quarantine
  drain on wait_idle) is intact by inspection, so this points at
  llvmpipe/host resource pressure on this 7.5 GB host (which OOM-killed an
  interpreted 4K render the same day), not an obvious leak. Needs a
  real-hardware or bigger-RAM host to confirm.
- The gate then failed with `reason=wrong-pixel-count expected=2080000
  actual=0` — after the fallback latched, the readback returned EMPTY
  instead of the host_cache/cpu_fallback pixels. Fail-closed either way, but
  the empty readback means the CPU fallback surface never got the frame;
  that secondary gap (fallback surface not populated on the demotion path)
  is the next thing to fix if this lane matters on this host class.

## 2026-11-27 W5-3 Fix (`fix-implemented-verification-pending`)

- **Source (`src/lib/gc_async_mut/gpu/engine2d/backend_vulkan.spl`, `src/lib/gc_async_mut/gpu/engine2d/backend_vulkan_font.spl`)**:
  - Added `_demote_to_cpu_fallback_host(reason)` and `_prepare_host_fallback_op(...)` to flush pending GPU compute if queued, sync `host_buf` from `d_framebuffer` cleanly via `_fallback_ensure_host_buf_synced() -> bool`, and transition `cpu_fallback_host_surface = true`, `host_mirror_valid = true`, `host_mirror_frame_fresh = true`, and `dirty = false` ONLY when synced without `completion_unknown` or readback errors (failing closed otherwise without forging freshness or delegating `completion_unknown` when `d_framebuffer > 0`).
  - Wired clean mid-frame demotion + `cpu_fallback_host_surface` gating across `clear` (ordering `cpu_fallback_host_surface = true` before `_fallback_clear_host` after pending flush), `draw_rect`, `draw_rect_filled` (`_draw_rect_filled_impl` via `_demote_to_cpu_fallback_host`), `draw_line`, `draw_circle_filled`, `draw_triangle_filled`, `draw_gradient_rect`, `draw_image`, `_draw_image_blend_impl` (`_fallback_image_blend_host`), `draw_image_scaled`, `draw_image_scaled_blend`, `draw_image_blend_checked`, `draw_affine_rect_coverage`, `draw_ir_apply_glass_material_device`, `_draw_blur_rect_device`/`draw_blur_rect`, `_draw_shadow_rect_device`/`draw_shadow_rect`, `draw_css_group_restore_device`, `draw_gradient_layer_device`, `draw_rect_blend`, `draw_rect_blend_mode`, and font-atlas routes (`_bitmap_text_atlas_path`, `_bitmap_text_bg_atlas_path`, `composite_font_batch`, `_composite_font_batch_impl`) so mixed-frame ops preserve earlier host-demoted pixels and return `w * h` pixels from `read_pixels_with_source()` with `source == "cpu_fallback"`.
  - Guarded `_fallback_sync_device_from_host()` against redundant per-rect full-surface device uploads once `cpu_fallback_host_surface` is active, checking `completion_unknown` and `vulkan_sffi_copy_to_buffer`, updating `present()` to handle clean `cpu_fallback_host_surface` frames (`dirty == false`) without noop/clobber, and syncing once in `_present_device()` if swapchain-presented.
- **Host verification (`SIMPLE_LIB=src`, `--mode=interpreter` on Windows)**:
  - `test/01_unit/lib/gc_async_mut/gpu/engine2d/backend_vulkan_demotion_recovery_spec.spl`: 7/7 PASS (covers mid-frame demotion, mixed-frame composite/blur/shadow/glass/gradient/font preservation, dirty readback / `completion_unknown` fail-closed, `present()` clean host-surface handling, and `_present_device()` `-host-upload-failed`).
  - `test/01_unit/lib/gpu/engine2d/vulkan_fallback_read_pixels_spec.spl`: 4/4 PASS.
  - `test/01_unit/lib/gpu/engine2d/backend_vulkan_text_fallback_spec.spl`: 4/4 PASS.
  - `test/01_unit/lib/gc_async_mut/gpu/engine2d/backend_vulkan_drawing_spec.spl`: 44/44 PASS.
  - `test/01_unit/lib/gc_async_mut/gpu/engine2d/backend_vulkan_bitmap_text_atlas_spec.spl`: 6/6 PASS.
  - `test/01_unit/lib/gc_async_mut/gpu/engine2d/backend_vulkan_batch_and_clip_boundary_spec.spl`: 7/7 PASS.
  - `test/01_unit/lib/gc_async_mut/gpu/engine2d/vulkan_clear_and_damage_readback_spec.spl`: 7/7 PASS.
- **Pending**: live Linux Vulkan / lavapipe full-page run (`waiting-for: Linux Vulkan / lavapipe verification`).
