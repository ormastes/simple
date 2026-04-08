# GPU Acceleration Plan for Browser Engine Effects

Status: PLAN
Date: 2026-04-08

## Overview

This document describes the GPU backend expansion roadmap for the browser engine's
paint effect modules (shadow, gradient, filter). The goal is to dispatch
compute-intensive per-pixel work to GPU hardware while keeping the CPU integer/float
variants as fallback paths.

## Current Architecture

```
PaintOp stream
    |
    v
+-------------------+
| EffectEngine      |  (trait: shadow, gradient, filter methods)
+-------------------+
    |         |          |
    v         v          v
  CPU-Int   CPU-Float   GPU  (backend selection at init time)
```

The CPU-Int and CPU-Float variants are implemented in:
- `examples/browser/feature/paint/shadow_int.spl` / `shadow_float.spl`
- `examples/browser/feature/paint/gradient_int.spl` / `gradient_float.spl`
- `examples/browser/feature/paint/filter_int.spl` / `filter_float.spl`

## GPU Backend Targets

### 1. CUDA (NVIDIA)

Existing infrastructure: `src/lib/gc_async_mut/gpu/engine2d/backend_cuda.spl`

**Extension plan:**
- Add compute shaders for each effect kernel:
  - `shadow_blur_kernel`: parallel ring expansion, one thread per output pixel
  - `gradient_sample_kernel`: parallel gradient evaluation along gradient line
  - `filter_chain_kernel`: per-pixel filter chain (brightness, contrast, hue-rotate, etc.)
- Use shared memory for the sin/cos lookup table in hue-rotate
- Tile-based dispatch: 16x16 thread blocks for spatial locality

**Kernel dispatch pattern:**
```
fn dispatch_shadow_cuda(shadow: ShadowValueFloat, box: Rect, framebuffer: GpuBuffer):
    val grid = compute_grid(box.w, box.h, 16, 16)
    cuda_launch(shadow_blur_kernel, grid, shadow, framebuffer)
```

### 2. AMD ROCm / HIP

Mirror the CUDA kernels via the HIP API, which provides source-level compatibility.

**Approach:**
- HIP source files generated from CUDA kernels via `hipify` or manual porting
- Same thread block geometry (16x16 tiles)
- Shared memory layout identical to CUDA path
- Runtime detection: check for ROCm runtime at init, fall back to CPU

**Files to create:**
- `src/lib/gc_async_mut/gpu/engine2d/backend_rocm.spl`
- Kernel source: `src/lib/gc_async_mut/gpu/kernels/effects_hip.spl`

### 3. Intel oneAPI / SYCL (DPC++)

Target integrated GPUs on Intel platforms (common in laptops/desktops).

**Approach:**
- DPC++ kernels using SYCL parallel_for with nd_range
- USM (Unified Shared Memory) for framebuffer access -- avoids explicit copies
- Sub-group operations for efficient reduction in blur kernels
- Fallback to OpenCL SPIR-V if DPC++ unavailable

**Files to create:**
- `src/lib/gc_async_mut/gpu/engine2d/backend_sycl.spl`
- Kernel source: `src/lib/gc_async_mut/gpu/kernels/effects_sycl.spl`

### 4. Apple Metal

Target macOS and iOS via Metal Performance Shaders and custom compute kernels.

**Approach:**
- Metal compute pipelines compiled from .metal shader source
- Use MTLComputeCommandEncoder for kernel dispatch
- ThreadgroupMemory for shared sin/cos table
- MetalPerformanceShaders framework for Gaussian blur (MPSImageGaussianBlur)
  as an optimized fast path for shadow blur
- Tile shading for gradient fills on Apple Silicon

**Files to create:**
- `src/lib/gc_async_mut/gpu/engine2d/backend_metal.spl`
- Shader source: `src/lib/gc_async_mut/gpu/kernels/effects_metal.spl`

## EffectEngine Trait Mapping

The EffectEngine trait provides the abstraction layer. Each GPU backend implements
these methods by dispatching to the appropriate compute kernel:

| Trait Method | CPU-Int Kernel | CPU-Float Kernel | GPU Kernel |
|---|---|---|---|
| `render_shadow(shadow, box)` | `generate_shadow_commands_int` | `generate_shadow_commands_float` | `shadow_blur_kernel` |
| `sample_gradient(stops, pos)` | `sample_gradient_int` | `sample_gradient_float` | `gradient_sample_kernel` |
| `apply_filter(pixel, filters)` | `apply_color_filter_int` | `apply_color_filter_float` | `filter_chain_kernel` |

## Dispatch Architecture

```
                          +------------------+
                          | EffectDispatcher |
                          +------------------+
                                  |
                    +-------------+-------------+
                    |             |             |
              +-----v----+ +-----v----+ +-----v----+
              | CPU-Int   | | CPU-Float| | GPU      |
              | Backend   | | Backend  | | Backend  |
              +----------+ +----------+ +----------+
                                              |
                              +---------------+---------------+
                              |        |         |            |
                         +----v--+ +--v---+ +---v---+ +------v---+
                         | CUDA  | | HIP  | | SYCL  | | Metal    |
                         +-------+ +------+ +-------+ +----------+
```

**Selection logic:**
1. Check for GPU at init time (CUDA -> ROCm -> Metal -> SYCL -> CPU)
2. For small regions (< 64x64 pixels), use CPU path (kernel launch overhead dominates)
3. For filter chains with only color transforms, prefer CPU-Int (no memory transfer needed)
4. For blur/shadow with large radii, prefer GPU (massively parallel)

## Memory Transfer Strategy

- **Shadow/Gradient**: GPU writes directly to framebuffer (device-resident)
- **Filter chain**: If framebuffer is on GPU, apply in-place. If CPU-resident, batch
  pixels into a transfer buffer, process on GPU, copy back.
- **Zero-copy path**: On unified memory architectures (Apple Silicon, Intel integrated),
  use shared memory mappings to avoid explicit transfers.

## Performance Targets

| Operation | CPU-Int | CPU-Float | GPU Target |
|---|---|---|---|
| Shadow 20px blur, 200x200 box | 2ms | 3ms | 0.3ms |
| Linear gradient 1000 pixels | 0.5ms | 0.8ms | 0.05ms |
| Filter chain (5 filters) per pixel | 50ns | 80ns | 5ns (batched) |

## Implementation Phases

1. **Phase 1 (current)**: CPU-Int and CPU-Float variants complete
2. **Phase 2**: CUDA compute shader kernels for all three effect types
3. **Phase 3**: Metal backend for macOS/iOS
4. **Phase 4**: HIP backend (source-port from CUDA)
5. **Phase 5**: SYCL backend for Intel integrated GPUs
6. **Phase 6**: Auto-selection heuristics and benchmarking framework
