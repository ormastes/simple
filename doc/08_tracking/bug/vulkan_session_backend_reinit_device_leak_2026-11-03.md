# Repeated Vulkan session adapter initialization loses the owned device

Status: source repair prepared; runtime verification not performed (user waiver).

`VulkanSessionBackend.init_device()` created a new provider device on every
call, then overwrote `self.handle`. Calling it twice successfully orphaned
the first handle: `cleanup()` could release only the replacement. If the
second create failed, the caller received an initialization error despite
the adapter still owning its earlier live device.

Initialization is now idempotent while `initialized` is true. The existing
handle, metadata, and counters remain owned by the adapter until cleanup.
The initial creation and post-cleanup creation paths remain available.

`test/01_unit/lib/gc_async_mut/gpu/engine2d/vulkan_session_backend_reinit_spec.spl`
constructs an already-initialized adapter with a sentinel handle and checks
the repeated-init branch preserves ownership and counters without calling
the provider. It is not a live GPU test and has not been executed.
The leak diagnosis is static source evidence, not a reproduced GPU failure.
