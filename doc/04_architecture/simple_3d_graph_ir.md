<!-- codex-design -->
# Simple 3D Graph IR Architecture

## Position

`graph_ir3d.spl` lives in `std.nogc_sync_mut.engine.render` above
`RenderBackend3D` and beside `gpu_mesh3d.spl`. It is a virtual capsule for
backend-neutral 3D draw scheduling.

## Layers

1. Existing resource layer: `GpuMeshHandle`, `BufferHandle`, `TextureHandle`,
   `PipelineHandle`.
2. Graph IR layer: resource table, pass list, draw list, deterministic optimizer.
3. Backend replay layer: converts graph nodes back into `RenderBackend3D` calls.
4. Backend-specific command recorders: Vulkan/WebGPU/software remain unchanged.

## Rules

- Graph optimization never moves draws across pass boundaries.
- Resource dedupe is by kind, id, and slot.
- Invalid mesh or pipeline handles are rejected at record time.
- Backend-specific synchronization and descriptor/bind-group lowering remains a
  backend responsibility.
