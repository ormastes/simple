---
name: CUDA/GPU/SIMD Reference
description: GPU kernel syntax, intrinsics, SIMD types, 3-tier API layers, backend config for Simple
type: reference
---

## GPU Kernel Syntax
- `@gpu_kernel` or `#[gpu]` for CUDA, `@vulkan_kernel` for Vulkan, `@simd` for CPU SIMD
- Launch: `fn<<<grid: (N,1,1), block: (256,1,1)>>>(args)` or `ctx.launch(kernel, config, args)`

## GPU Intrinsics (kernel context only)
- Thread IDs: `gpu_global_id_x/y/z()`, `gpu_local_id_x()`, `gpu_block_id_x()`, `gpu_block_dim_x()`, `gpu_grid_dim_x()`
- Sync: `gpu_syncthreads()`, `gpu_barrier()`, `gpu_mem_fence()`
- Atomics: `gpu_atomic_add/sub/min/max/and/or/xor/exchange/cas(ptr, value)`
- Shared mem: `gpu_shared_mem<f32>(size)`
- SIMD: `this.index()`, `this.thread_index()`, `this.group_index()`

## 3-Tier API
| Tier | Module | Mode | Location |
|------|--------|------|----------|
| 1 Runtime | `std.gpu_runtime` | Interpreter OK | `src/lib/nogc_sync_mut/gpu_runtime/` |
| 2 Full | `std.gpu` | Compiled only | `src/lib/gc_async_mut/gpu.spl` |
| 3 FFI | `std.cuda` | Direct driver | `src/compiler/70.backend/backend/cuda/cuda_ffi.spl` |

## SIMD Types (`std.simd`)
- `Vec4f` (4×f32), `Vec4i` (4×i32), `Vec4d` (4×f64, AVX only)
- `Vec8f` (8×f32, AVX2), `Vec8i` (8×i32, AVX2)
- Platform: `has_sse()`, `has_avx()`, `has_avx2()`, `has_neon()`, `simd_width()`
- Ops: `simd_add/sub/mul/div/fma_f32x4()`, `..._f32x8()`, `..._i32x4()`

## Backend Targets
| Backend | Output | Decorator |
|---------|--------|-----------|
| CUDA | PTX | `@gpu_kernel` |
| Vulkan | SPIR-V | `@vulkan_kernel` |
| Native | AVX2/NEON | `@simd` |
| C | Scalar | `@simd` fallback |

Compile: `bin/simple compile --backend=cuda|vulkan|native kernel.spl`
Env: `SIMPLE_GPU_BACKEND`, `SIMPLE_GPU_DEVICE`, `SIMPLE_GPU_DEBUG`

## Key Files
- `src/compiler/70.backend/gpu_intrinsics.spl` — GPU intrinsic validation
- `src/compiler/70.backend/backend/cuda_backend.spl` — CUDA→PTX compiler
- `src/compiler/70.backend/backend/vulkan_backend.spl` — Vulkan→SPIR-V
- `src/lib/nogc_sync_mut/simd.spl` — SIMD vector types
- `doc/06_spec/gpu_simd/gpu.md` — GPU/SIMD specification
