# Engine3D Vulkan world font depth write is disabled

Status: source fixed; native execution pending

The native Vulkan world-font pipeline previously enabled depth testing but
disabled depth writes. It now uses the tested `(depth_test, depth_write) =
(true, true)` contract. The fragment shader discards zero-coverage atlas texels
before depth output so transparent glyph padding cannot become an invisible
occluder; the embedded SPIR-V is pinned to the regenerated validated bytes.

The system gate now renders near-only, far-only, and both draw orders under a
translated perspective camera. Every fully opaque overlap pixel must keep the
near color in both orders. The Simple CPU comparator still has no depth buffer,
so depth authority comes only from device-image readback. Promotion remains
fail-closed until that native scenario executes successfully.
