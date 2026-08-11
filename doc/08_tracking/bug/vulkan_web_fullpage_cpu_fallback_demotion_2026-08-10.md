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

Unverified whether the same trip exists on a real-hardware / larger-RAM
host. If it reproduces there, the suspect list is
`vulkan_sffi_begin_compute`/descriptor-create error handling in
`backend_vulkan_helpers.spl` and the `rt_vulkan_*` wrappers in
`src/compiler_rust/compiler/src/interpreter_extern/gpu.rs`.
