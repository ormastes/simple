# 2D Rendering Optimization Plan — CUDA / HIP / OpenCL / SIMD Shared Interface

**Date:** 2026-05-30
**Status:** Draft
**Goal:** Unify the four compute backends behind one trait, fix broken runtime paths, and deliver real SIMD acceleration.

---

## Current State

### What exists

| Layer | File(s) | Status |
|-------|---------|--------|
| **Portable compute emitter** | `compiler/70.backend/backend/gpu_portable_compute.spl` (420 LOC) | Emits CUDA/HIP/OpenCL C/Metal source for fill/add/copy/alpha/scroll/2D-opt kernels. Works. |
| **SFFI dispatch** | `gpu/engine2d/sffi_dispatch.spl` | GpuFfiMode enum (Static/Dynamic), FfiDispatchBase trait, try_load_gpu_lib helper. |
| **CUDA** | `sffi_cuda.spl` + `cuda_session.spl` (177 LOC) | Session with context retain/release, PTX module cache, kernel launch. Most complete. |
| **HIP/ROCm** | `sffi_rocm.spl` (161 LOC) + `backend_rocm_kernels.spl` (324 LOC) | SFFI wrapper only — **no session class**. HIP C++ kernel source inlined. Test `C-3: hipLaunchKernel` RED. |
| **OpenCL** | `sffi_intel.spl` (211 LOC) — Level Zero, NOT OpenCL ICD | SFFI wrapper for `ze_loader` only — **no session class**, no generic OpenCL ICD path. Emitter produces OpenCL C but SFFI talks Level Zero. |
| **CPU SIMD** | `cpu_simd_session.spl` (162 LOC) + `simd_kernels.spl` (409 LOC) | Session exists. Kernels are **pure Simple scalar loops** with SIMD detection but no actual SIMD intrinsics ("before native Rust/NEON kernels"). |
| **ARM/RISC-V** | `arm_riscv_session.spl` (189 LOC) | Validation/capability checks only — not a render backend. |
| **Backend probe** | `backend_probe.spl` | `BackendProber` with `probe_*` per backend + `StrictBackendFactory`. |
| **Session contract** | `backend_session.spl` (270 LOC) | Data types only (Mode, Kind, Policy, Handle, Error, Frame, FrameStats). **No session trait.** Each session is a standalone class. |
| **SimdProvider** | `simd_provider.spl` | Trait + hit-count accumulator for optimization plugin metadata. |

### Key problems

1. **No shared session trait** — CUDA, CPU-SIMD each define their own API; HIP and OpenCL have no session at all.
2. **HIP runtime broken** — `C-3: hipLaunchKernel dispatches compute kernel` RED. `sffi_rocm.launch_kernel` passes `0` as first arg to `hipLaunchKernel` instead of the loaded module/kernel handle.
3. **OpenCL is Level Zero only** — `sffi_intel.spl` wraps Intel `ze_loader`, not a generic OpenCL ICD (`libOpenCL.so`). The emitter produces OpenCL C source but there's no runtime path to compile/dispatch it.
4. **SIMD kernels are scalar** — `simd_kernels.spl` doc says "first pass keeps row operations in Simple … before native Rust/NEON kernels are introduced." Detection works; acceleration doesn't.
5. **No auto-selection** — `BackendProber` detects availability and `StrictBackendFactory` creates probe results, but nothing chains probe → session creation → dispatch.
6. **CUDA selector broken** — `C-2: cuda backend still selectable` RED. `BackendSessionKind` lacks `hip`/`rocm`/`opencl` entries.

---

## Design: ComputeSession Trait

All four backends implement one trait. GPU backends manage device context + kernel compilation; CPU-SIMD is no-op for device lifecycle and dispatches directly to buffer ops.

### Trait definition (in `backend_session.spl`)

```
trait ComputeSession:
    # Lifecycle
    fn kind() -> BackendSessionKind
    fn init() -> ComputeError?
    fn is_available() -> bool
    fn shutdown()
    fn synchronize()

    # 2D pixel operations (the five core ops)
    fn fill(dst: any, offset: i64, count: i64, color: u32) -> ComputeError?
    fn copy(dst: any, dst_off: i64, src: any, src_off: i64, count: i64) -> ComputeError?
    fn alpha_blend(dst: any, src: [u32], offset: i64, count: i64) -> ComputeError?
    fn blit_rect(dst: any, dst_stride: i64, dx: i64, dy: i64, src: any, src_stride: i64, sx: i64, sy: i64, w: i64, h: i64) -> ComputeError?
    fn scroll(buf: any, stride: i64, x: i64, y: i64, w: i64, h: i64, delta_y: i64) -> ComputeError?

    # GPU-only (no-op on CPU-SIMD)
    fn load_module(name: text, source: text) -> ComputeError?
    fn launch_kernel(name: text, gx: i64, gy: i64, bx: i64, by: i64) -> ComputeError?

    # Stats
    fn hit_counts() -> SimdHitCounts
```

### GPU vs CPU lifecycle

| Op | CUDA/HIP/OpenCL | CPU-SIMD |
|----|-----------------|----------|
| `init()` | Retain context, create queue/stream | `detect_simd_level()` |
| `load_module()` | cuModuleLoad / hipModuleLoad / clCreateProgramWithSource | No-op (returns nil) |
| `launch_kernel()` | cuLaunchKernel / hipLaunchKernel / clEnqueueNDRangeKernel | No-op (returns nil) |
| `fill()` | Launch fill kernel on device | `simd_fill_row()` on host buffer |
| `synchronize()` | cuStreamSynchronize / hipDeviceSynchronize / clFinish | No-op |
| `shutdown()` | Release context, free modules | Reset detection cache |

---

## Phases

### Phase 1: Shared trait + CUDA conformance (foundation)

**Files:** `backend_session.spl`, `cuda_session.spl`

1. Add `ComputeSession` trait and `ComputeError` to `backend_session.spl`
2. Add missing `BackendSessionKind` entries: `hip`, `rocm`, `opencl`
3. Retrofit `CudaSession` to implement `ComputeSession`
   - Map existing `init_context → init`, `load_ptx → load_module`, `launch → launch_kernel`
   - Add the 5 pixel ops as kernel-dispatch wrappers using existing PTX from `gpu_portable_compute`
4. Verify and fix test `C-2: cuda backend still selectable`

**AC:** CudaSession conforms to ComputeSession, C-2 test GREEN.

Progress 2026-05-30:
- Added the public shared `ComputeSession` contract surface and `ComputeError`
  helper in the canonical no-GC backend-session module.
- Added missing backend kind names for CPU-SIMD, HIP, ROCm, OpenCL, and
  Qualcomm in both the canonical session contract and the GC async Engine2D API
  resolver.
- Added focused coverage in
  `test/unit/lib/gpu/engine2d/backend_session_contract_spec.spl`.
- Added `CudaSession` contract helpers for backend kind, availability,
  shutdown/synchronize aliases, and fail-closed cached-module kernel launch,
  covered by `test/unit/lib/gpu/engine2d/cuda_session_contract_spec.spl`.
- Added generated 2D CUDA launch wrappers for fill/copy/alpha/scroll that use
  `generated_2d_launch_plan(...)` and fail closed when no cached module,
  argument buffer, or valid plan exists.
- Routed the existing CUDA backend surface's prepared argument buffers through
  `CudaSession.launch_kernel_args(...)`, removing direct
  `cuda_launch_kernel(self.session.module_cache, ...)` calls from the surface
  draw paths.
- Replaced the `BackendProber.probe_cuda()` placeholder with live CUDA
  runtime/device/context evidence. On this host `cuda_available=true` and
  `StrictBackendFactory.strict().create_backend("cuda")` reports
  `status=Initialized`, `feature_gate=cuda_context`.
- Remaining Phase 1 decision: whether the legacy renderer PTX should be
  replaced by the portable `simple_2d_*` kernel module in this phase or in the
  Phase 6 integration pass.

### Phase 2: CPU-SIMD conformance + native acceleration

**Files:** `cpu_simd_session.spl`, `simd_kernels.spl`, runtime C

1. Retrofit `CpuSimdSession` to implement `ComputeSession`
   - Pixel ops delegate to existing `fill_span`/`copy_span`/`alpha_blend_span`/`blit_rect`/`scroll_region`
   - GPU-only ops return nil (no-op)
   - Done: `CpuSimdSession` now reports `cpu_simd`, initializes from the
     working SIMD detector, delegates fill/copy/alpha/blit/scroll to the
     span/rect kernels, exposes hit counts, and treats module/kernel hooks as
     CPU no-ops. Legacy geometry-shaped methods remain as `*_geometry` aliases.
   - Covered by `test/unit/lib/gpu/engine2d/cpu_simd_session_contract_spec.spl`.
2. Add native SIMD kernels behind the existing scalar functions:
   - x86: AVX2 `_mm256_set1_epi32` fill, `_mm256_loadu_si256`/`_mm256_storeu_si256` copy, Porter-Duff blend
   - ARM: NEON `vdupq_n_u32` fill, `vld1q_u32`/`vst1q_u32` copy, `vmulq_u32` blend
   - RISC-V: RVV `vse32` fill, `vle32`/`vse32` copy (when available)
   - In progress: hosted C runtime entrypoints now exist for native fill/copy
     spans (`rt_engine2d_simd_fill_u32`, `rt_engine2d_simd_copy_u32`) with AVX2
     64-bit lane stores/loads and scalar fallback.
   - Wiring into `simd_kernels.spl` is intentionally blocked until mutable
     `[u32]` extern dispatch is proven for interpreter parity; tracked in
     `doc/08_tracking/bug/cpu_simd_mutable_array_extern_wiring_2026-05-31.md`.
3. Wire native kernels via `rt_simd_fill_avx2`, `rt_simd_fill_neon`, etc. externs
4. Benchmark: fill 1920×1080 framebuffer, scalar vs native, report speedup

**AC:** CpuSimdSession conforms, native kernels >2× scalar on x86 fill benchmark.

### Phase 3: HIP/ROCm session (new)

**Files:** new `rocm_session.spl`, fix `sffi_rocm.spl`

1. Create `RocmSession` implementing `ComputeSession`
   - Pattern: mirror `CudaSession` — context init, HIP module cache, kernel launch
   - Pixel ops: compile HIP kernels from `backend_rocm_kernels.spl` source via `hipModuleLoadData`
2. Fix `sffi_rocm.launch_kernel` — currently passes `0` as kernel handle; must load module + get function first
3. Verify and fix test `C-3: hipLaunchKernel dispatches compute kernel`

**AC:** RocmSession conforms, C-3 test GREEN on AMD GPU (or correctly returns `Unavailable` when no AMD GPU).

### Phase 4: OpenCL session (new) — generic ICD path

**Files:** new `opencl_session.spl`, new `sffi_opencl.spl`

1. Decision: **add a generic OpenCL ICD SFFI** (`libOpenCL.so`) alongside the existing Level Zero (`sffi_intel.spl`)
   - Level Zero stays for Intel-specific optimizations
   - `sffi_opencl.spl` wraps: `clGetPlatformIDs`, `clCreateContext`, `clCreateCommandQueue`, `clCreateProgramWithSource`, `clBuildProgram`, `clCreateKernel`, `clEnqueueNDRangeKernel`, `clEnqueueReadBuffer`, `clFinish`
2. Create `OpenClSession` implementing `ComputeSession`
   - `load_module` → `clCreateProgramWithSource` + `clBuildProgram` using OpenCL C from `gpu_portable_compute`
   - `launch_kernel` → `clEnqueueNDRangeKernel`
   - Pixel ops: kernel dispatch (same pattern as CUDA/HIP)
3. Add `BackendProber.probe_opencl` real detection via `clGetPlatformIDs`

**AC:** OpenClSession conforms, passes fill-kernel round-trip test on any OpenCL-capable device.

### Phase 5: Auto-selection + dispatch layer

**Files:** new `compute_dispatch.spl`, update `backend_probe.spl`

1. Create `ComputeDispatch` — probes available backends, selects fastest:
   ```
   CUDA > HIP > OpenCL > CPU-SIMD(AVX2) > CPU-SIMD(NEON) > CPU-SIMD(RVV) > Scalar
   ```
2. Wire through `StrictBackendFactory` — `create_backend` returns a `ComputeSession`
3. Connect to `BackendFrame` — frame lifecycle calls `session.synchronize()` per frame
4. Export `SimdHitCounts` from all backends (GPU backends count kernel launches, CPU-SIMD counts span ops)

**AC:** `ComputeDispatch.auto()` returns best available session. Frame loop dispatches through trait.

### Phase 6: Integration + benchmarks

1. Wire game2d render pipeline through `ComputeSession` trait instead of direct backend calls
2. End-to-end benchmark: 1920×1080 fill+blit+scroll frame at 60fps target
   - Measure per-backend: CUDA, HIP, OpenCL, AVX2, NEON, scalar
3. Update `BackendProber.probe_all_summary` with runtime evidence from real session init
4. Update specs: `gpu_portable_compute_spec.spl`, `engine_platform_spec.spl`, `ffi_rocm_spec.spl`

**AC:** All 4 backends pass through shared trait. Benchmark report shows per-backend throughput.

---

## File Map

| Phase | New files | Modified files |
|-------|-----------|---------------|
| 1 | — | `backend_session.spl`, `cuda_session.spl` |
| 2 | Runtime C: `rt_simd_avx2.c`, `rt_simd_neon.c`, `rt_simd_rvv.c` | `cpu_simd_session.spl`, `simd_kernels.spl` |
| 3 | `rocm_session.spl` | `sffi_rocm.spl` |
| 4 | `opencl_session.spl`, `sffi_opencl.spl` | `backend_probe.spl` |
| 5 | `compute_dispatch.spl` | `backend_probe.spl`, `backend_session.spl` |
| 6 | — | game2d pipeline, specs |

## Risks

- **OpenCL C vs Level Zero:** Maintaining two Intel paths (ICD + L0) adds surface area. Mitigate: L0 stays as-is, generic ICD is the new shared path.
- **SIMD native kernels need runtime C:** Three new C files in `src/runtime/`. Must pass bootstrap (`scripts/bootstrap/bootstrap-from-scratch.sh --deploy`) after adding externs.
- **HIP fix is untestable without AMD GPU:** Guard with `probe_rocm().available` check in tests; skip gracefully.
- **Scalar SIMD kernels may be "good enough":** Benchmark first (Phase 2 step 4) before investing in RVV, which has limited hardware.

## Non-goals

- Vulkan/Metal/WebGPU session conformance (already have session files; future work)
- 3D rendering (separate engine3d path)
- Compiler auto-vectorization of Simple → SIMD (separate MIR pass in `simd_lowering.spl`)
