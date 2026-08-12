# Engine2D Vulkan swapchain registry split

Status: partial — same-device headless bridge implemented; visible-window adapter open

Engine2D's Vulkan backend renders into `vulkan_graphics_runtime_core::STATE`
storage buffers. The implemented window/swapchain SFFI instead owns devices,
surfaces, and swapchains in `value::gpu_vulkan::vulkan_sffi` registries. Handles
from either family are not valid in the other family, so the existing
`rt_vulkan_present` entry point cannot present `VulkanBackend.d_framebuffer`.
The current backend `present()` is correctly a device-to-host cache refresh.

This blocks honest device-present and end-to-end 8K/80 claims even when the
isolated compute frame meets 12.5 ms. A host readback followed by an upload to a
second presentation device is not an acceptable optimized bridge.

The canonical runtime now has an opt-in initialization path that creates a
`VK_EXT_headless_surface` before device selection, allocates the Engine2D
storage buffer on that presentation-capable device, copies it directly to an
acquired BGRA8 swapchain image, and completes `vkQueuePresentKHR`. This removes
the registry split for headless evidence without claiming a visible screen.
The visible winit/window surface must next enter the same pre-device owner.

Acceptance:

- One canonical Vulkan owner creates the window surface before selecting a
  compute/graphics/present-capable device.
- Engine2D storage-buffer work and swapchain acquisition use that same device
  and queue-family-compatible command ownership.
- A fenced device-side transfer converts/copies the ARGB framebuffer into the
  acquired swapchain image without device-to-host traffic.
- The transfer handles swapchain layout transitions, format conversion,
  resize/out-of-date/suboptimal results, and completion failure conservatively.
- A frame receipt reports nonzero surface/swapchain/device identities, exact
  dispatch/submission/present counts, zero readback bytes, known completion,
  fallback state, and whether presentation actually completed.
- Native llvmpipe correctness uses an exact post-presentation oracle; physical
  GPU promotion separately records 8K p50/p95, RSS/device memory, checksum,
  fallback, and swapchain present mode.
