# Engine2D Vulkan Font Routing Specification

**Status:** manually synchronized; canonical docgen and native execution pending
**Executable:** `test/01_unit/lib/gc_async_mut/gpu/engine2d/engine_vulkan_font_route_spec.spl`

Four active scenarios prove the canonical Vulkan constructor boundary and CPU
replay behavior. A poisoned Vulkan surface switches to `SoftwareBackend`, skips
later GPU attempts, seeds the replacement from the pre-dispatch framebuffer,
replays the same immutable `FontRenderBatch` from quad zero, preserves its
atlas-cache identity and earlier scene pixels, and produces the expected font pixel.
Plans without a successful native route still use CPU when policy includes it;
required plans without CPU fail closed.

The source contract also requires `device-lost` to use the same poison-and-replay
path as unknown completion and cleanup failures. This hardware-free unit proof
does not replace retained native device-loss or post-loss p95 evidence.
