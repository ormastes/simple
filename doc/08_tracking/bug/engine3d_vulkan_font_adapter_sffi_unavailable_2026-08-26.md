# Engine3D Vulkan font adapter SFFI unavailable in pure-Simple test child

The focused adapter suite imports the canonical Engine3D Vulkan backend, but the
pure-Simple child reports that Vulkan initialization, device, buffer, shader,
pipeline, fence, and wait symbols are not provided through the selected module
family. `VulkanFontAdapter3D.create(16, 16)` therefore returns
`vulkan-font-adapter-init-failed` and native adapter branches cannot execute.

Impact: `engine3d_hud_vulkan` and `engine3d_world_vulkan` coverage and joint
time/memory receipts cannot be produced through this runner. Fix the module
family/export closure, then run on a Vulkan-capable device with forced backend,
queue/fence timing, readback, atlas/upload accounting, VRAM HWM, and cleanup
retention. Do not replace this with source-text assertions or CPU fallback.
