# engine3d: `*_ext.spl` plain impl blocks are never imported — trait impls incomplete

Date: 2026-07-02
Status: open (CPU backend fixed; same latent bug in all other 3D backends)
Severity: P2
Found by: W6 lane agent

## Symptom

`error: semantic: type 'CpuBackend3D' does not implement required method
'create_texture_ex' from trait 'RenderBackend3D'`

The 3D backends split trait-required methods into sibling `*_ext.spl`
files containing plain `impl Backend:` blocks. Nothing imports those
files, so the methods never attach and the backend fails trait checking —
`std.gpu.engine3d` was completely uncompilable.

## Fixed

`gc_async_mut/gpu/engine3d/backend_cpu.spl`: 26 methods moved from
`backend_cpu_ext.spl` (deleted) into the real
`impl RenderBackend3D for CpuBackend3D` block.

## Still latent (same pattern, unverified/broken)

- `gc_async_mut/gpu/engine3d/backend_software.spl` / `backend_vulkan.spl`
  / cuda/rocm backends and their `*_ext.spl` siblings
- `gc_sync_mut/gpu/engine3d/backend_cpu_ext.spl`
- `nogc_sync_mut/engine/render/gpu_mesh3d.spl` also still declares the
  nonexistent `rt_f64_*` externs (fixed elsewhere as `rt_math_*`).
