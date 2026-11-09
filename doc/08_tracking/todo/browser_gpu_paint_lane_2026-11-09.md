# TODO: browser GPU paint lane (non-essential, assert-only)

Bug: browser_has_no_vulkan_render_lane_2026-08-15
Spec: test/01_unit/app/browser/browser_gpu_paint_lane_spec.spl (@tag:in-development, RED by design)

Status of the original record on release/1.0.0:
- Gap 1 (no vulkan lane) is partly closed: `src/app/browser/render_lane.spl` has
  `BROWSER_RENDER_LANE_VULKAN` and defaults to it (live CPU paint + engine2d
  VulkanBackend present/readback).
- Remaining: a fully-GPU paint lane (browser draw IR through
  `std.gc_async_mut.gpu.engine2d` primitives).
- Gap 2: deployed seed lacks the vulkan feature; `simple-compiler/vulkan` blocked
  by incomplete vendored rspirv (E0583 missing `build` module).

Per owner rule (non-essential = assert-only + todo row), no implementation now.
