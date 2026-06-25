# std.compute — CPU/GPU Compute Stdlib & ExecTarget

**Module:** `src/lib/nogc_async_mut/compute/` · **Backend kernels:**
`src/compiler/70.backend/backend/gpu_compute_algorithm_kernels.spl`

A single generic, config-selectable container + algorithm surface that runs on CPU or a GPU
backend chosen by policy — modeled on SYCL `device_type` (you tag the **device class**, the
runtime resolves the **backend**). See glossary → "ExecTarget (Compute Target Mode)".

## Two-level target model

- **Level 1 — device class (you tag/configure):** `default · cpu · simd_cpu · gpu · fpga · simd`
  (`simd` = umbrella that lowers to whichever of gpu/fpga/simd_cpu is present).
- **Level 2 — backend (auto-resolved):** `cuda/hip/opencl/vulkan/metal/webgpu · vhdl ·
  neon/sve2/rvv · scalar`. Never tagged directly.

Two independent **domains**: *drawing* (render, `SIMPLE_2D_BACKEND`) and *processing*
(compute, this module) — each resolves its own best backend.

```simple
use std.nogc_async_mut.compute.exec_target.{
    DeviceClass, ComputeBackend, EnforceMode, BackendCaps, resolve_exec_target }

# Resolve "gpu, prefer best available; require it"
val caps = BackendCaps.none()      # probe real machine; here: nothing available
val t = resolve_exec_target(DeviceClass.Gpu, ComputeBackend.NoneBackend, EnforceMode.Require, caps)
# t.resolved == false  -> caller fail-closes (rt_exit 70). Suggest mode would fall back.
```

### Config selection
- Env: `SIMPLE_COMPUTE_TARGET` (class) · `SIMPLE_COMPUTE_BACKEND` (optional backend) ·
  `SIMPLE_COMPUTE_ENFORCE` = `suggest` (soft, falls back) | `require` (hard, fail-closed).
- `default` honors the landed order `vulkan,metal,cuda,hip,opencl → cpu`.

## Algorithm surface (generic over `T`, takes an `ExecTarget`)

`compute_ops`: `compute_reduce / transform / inclusive_scan / count / filter / find / sort`.
`compute_algo_ext`: `min_element / max_element / transform_reduce / unique / lower_bound /
binary_search / exclusive_scan`.

The pure-Simple CPU path is the **differential oracle**. Comparators are
`less: fn(T,T)->bool` (single relational `a < b`); derive equality as
`!(a<b) && !(b<a)` — **avoid generic `!=`/2-arg `==` on `[T]`** (interpreter bug,
`doc/08_tracking/bug/interp_generic_eq_callback_2026-06-16.md`).

```simple
fn less_i64(a: i64, b: i64) -> bool: a < b
val sorted = compute_sort([5,3,8,1], less_i64, t)        # [1,3,5,8]
val idx    = compute_lower_bound(sorted, 5, less_i64, t) # 2
```

## Containers
`Span<T>` (view), `FixedArray<T>` (fixed cap), `InplaceVector<T>` (bounded push) in
`containers.spl`.

## Backend "backed" kernels
`gpu_compute_algorithm_kernels.spl` emits real per-backend kernel source for `transform-scale`
and `saxpy` (CUDA/HIP/OpenCL/Metal/WebGPU), consistent with `gpu_portable_compute`. Runtime
GPU *execution* on hardware (compile → launch → readback) is the remaining open step.

## Testing (no GPU needed)
- **Resolver**: assert backend name via `compute_backend_name(t.backend)` and `t.resolved`.
- **Dispatch honesty (payload-gating)**: a device target with NO payload → `ran_on_cpu=true`
  (CPU fallback, no masquerade); with payload → `ran_on_cpu=false`, value == CPU reference.
- **Kernel emission**: assert backend markers — CUDA `__global__ void`, OpenCL `__kernel void`,
  Metal `kernel void` + `[[thread_position_in_grid]]`, WebGPU `@compute @workgroup_size`.

Run: `SIMPLE_BOOTSTRAP_DRIVER=…/simple_seed bin/simple test test/01_unit/lib/nogc_async_mut/compute/`
