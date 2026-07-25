# Engine3D Font HUD and World Material Contract

**Status:** manually synchronized; executable docgen refresh pending
**Executable:** `test/01_unit/lib/gpu/engine3d/font_hud_material_spec.spl`

The unit scenarios cover transient `FontRenderBatch` conversion for Engine3D
HUD and world pipelines. HUD vertices retain the backend-neutral 20-byte
contract. World vertices use the separate 24-byte contract and map OpenGL
clip-space depth `[-1, 1]` to Vulkan device depth `[0, 1]` before packing.

The executable assertions cover the midpoint (`0.25 -> 0.625`), both depth
boundaries, atlas coordinates, color, and fail-closed invalid batches. This
manual makes no native submission or device-readback claim.
