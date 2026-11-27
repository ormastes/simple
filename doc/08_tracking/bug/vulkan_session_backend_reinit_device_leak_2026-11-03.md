# Repeated Vulkan session adapter initialization loses the owned device

Status: RESOLVED & VERIFIED (2026-11-22).

`VulkanSessionBackend.init_device()` created a new provider device on every
call, then overwrote `self.handle`. Calling it twice successfully orphaned
the first handle: `cleanup()` could release only the replacement. If the
second create failed, the caller received an initialization error despite
the adapter still owning its earlier live device.

Sibling `VulkanSession.init()` (`src/lib/gc_async_mut/gpu/engine2d/vulkan_session.spl`)
had the same class of defect: calling `init()` again on an already-initialized
session recompiled all 17 SPIR-V shaders and 17 compute pipelines, overwriting
`self.shader_*` and `self.pipe_*` handles without releasing the previous ones
and resetting `self.ref_count = 1`.

Both `VulkanSessionBackend.init_device()` (`if self.initialized and self.handle != 0`)
and `VulkanSession.init()` (`if self.is_initialized and self.device > 0`, short-circuiting
for device-free mock sessions with `selected_device_index < 0` and verifying
`vulkan_get_device() == self.device` for runtime-bound sessions; on mismatch it
calls `_reset_local_handles()` without `vulkan_sffi_destroy_*` so a replacement
device's 1-based shader/pipeline slots are never destroyed) are now idempotent,
preserving live handles, pipeline state, and reference counts while clearing
stale error strings until explicit cleanup/release.

Verified by executing `test/01_unit/lib/gc_async_mut/gpu/engine2d/vulkan_session_backend_reinit_spec.spl`
(3/3 examples passed).
