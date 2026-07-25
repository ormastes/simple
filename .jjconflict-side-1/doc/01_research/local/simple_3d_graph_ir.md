<!-- codex-research -->
# Simple 3D Graph IR Local Research

## Findings

- No existing `GraphIr`/`graph_ir` implementation exists in `src/`, `test/`, or
  `doc/` by exact name.
- The sync-mut 3D render layer already has the right backend-neutral contract:
  `src/lib/nogc_sync_mut/engine/render/backend3d.spl` defines
  `RenderBackend3D`, resource handles, render-pass handles, pipeline
  descriptors, and indexed draw commands.
- `src/lib/nogc_sync_mut/engine/render/gpu_mesh3d.spl` already converts mesh
  data into `GpuMeshHandle` values and exposes `gpu_mesh_draw` helpers that bind
  vertex, index, uniform, and pipeline state before `draw_indexed`.
- Vulkan and WebGPU siblings already record flat command objects:
  `vulkan_commands.spl`, `webgpu_commands.spl`, `vulkan_backend3d.spl`, and
  `webgpu_backend3d.spl`. A shared graph IR should therefore sit above
  `RenderBackend3D` instead of replacing those backend recorders.
- The software backend has enough `RenderBackend3D` behavior for deterministic
  unit coverage, but raw float/index serialization remains a pre-existing
  limitation in mesh upload paths.
- Verification found the software 3D replay path also depended on missing
  `Mat4`/`Vec3` compatibility methods and nested renderer mutation propagation.
  Those are part of the hardening lane because Graph IR replay should work
  through the real software backend, not only a test recorder.

## Implementation Implication

The smallest aligned hardening slice is a pure `graph_ir3d.spl` module that
records resources, passes, and draws; dedupes resource references; sorts
pass-local draws by pipeline/texture/mesh state; and replays through
`RenderBackend3D`.
