# CompositorBackend declared three times; Engine2D.submit_batch_for_present calls a missing method

- **Date:** 2026-11-07
- **Severity:** P1 (Stage 2 `compiler_cli_build`, bootstrap run 13)
- **Status:** fix-implemented

## 1. Duplicate trait owner

`os/compositor/display_backend.spl` redeclared `CompositorGlassCapable` and
`CompositorBackend` twice. Neither copy had `report_damage`. The canonical
declaration is in `common.ui.compositor_backend_core`, and
`display_backend_core` already re-exports it.

Implementors that imported the traits through `display_backend` therefore
implemented a different native trait owner from the one the shared executor
accepts (`common.ui.window_scene_draw_ir`). Stage 2 reported:

> missing native trait implementation:
> lib.common.ui.compositor_backend_core::CompositorBackend for
> os.compositor.shared_mdi_framebuffer_scene::SharedMdiFramebufferBackend

**Fix:**

- `display_backend.spl` now uses `export use` of the canonical traits.
- `report_damage` gets the no-op default that its doc comment already describes:
  "backends with no damage consumer implement this as a no-op". With the default,
  `GpuCompositorBackend`, `shell_baremetal`, and the test doubles that never
  declared it keep working.

Spec: `test/01_unit/os/compositor/compositor_backend_single_trait_owner_spec.spl`.
It passed 0 of 2 before the fix and 2 of 2 after.

## 2. `Engine2D.submit_batch_for_present` (removed)

`8a87db7d9eb` added this wrapper, but it calls
`VulkanBackend.submit_batch_for_present()`, which never existed in this tree. Its
docstring promises an "exclusive one-shot presenter-read receipt". The Vulkan
backend has `submit_batch()`, `present_*_device()` and frame receipts, but no
presenter-read receipt, so it cannot be built honestly from the existing
primitives.

**Fix:** the dead wrapper and its two calls in `engine_branch_coverage_spec.spl`
are removed. Both calls ran on the cpu backend and asserted nothing.
