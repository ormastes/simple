<!-- codex-design -->
# Accelerated Shared UI Backend Architecture - Agent Task Plan

Date: 2026-06-03

## Team Slices

### Agent A: Shared UI Contract

Files:
- `doc/04_architecture/shared_ui_contract.md`
- `src/app/ui*/`
- `src/lib/common/ui/`
- `test/01_unit/app/ui/`

Tasks:
1. Promote native TUI, Tauri, Electron, pure Simple GUI, and pure Simple web
   from adapter-only descriptions into a staged shared semantic UI contract.
2. Preserve existing transport-specific adapters.
3. Add tests that prove the same semantic tree and event command map across at
   least TUI, web, Electron, and Tauri helpers.

### Agent B: OpenCL Runtime Evidence

Files:
- `src/runtime/runtime_simd_dispatch.c`
- `src/lib/nogc_sync_mut/gpu/engine2d/sffi_opencl.spl`
- `src/lib/gc_async_mut/gpu/engine2d/opencl_session.spl`
- `src/lib/gc_async_mut/gpu/engine2d/sffi_opencl.spl`
- `src/lib/gc_async_mut/gpu/engine2d/generated_kernel_dispatch.spl`
- `src/lib/gc_async_mut/gpu/engine2d/backend_probe.spl`
- `src/lib/gc_async_mut/gpu/engine2d/engine.spl`
- `test/01_unit/lib/gpu/engine2d/`

Tasks:
1. Replace stub-like OpenCL ICD calls with real context, queue, program build,
   kernel creation, enqueue, finish, and error reporting.
2. Prove OpenCL unavailable, available, module-load, kernel-submit, sync, and
   readback paths with typed evidence.
3. Keep OpenCL unavailable distinct from compiler-artifact unavailable.
4. Integrate OpenCL into Engine2D backend probing/selection only after typed
   runtime proof exists.
5. Add generated 2D kernel fixture coverage for fill/copy/alpha/scroll launch
   plans.

### Agent C: Compiler CUDA/OpenCL Offload

Files:
- `src/compiler_rust/compiler/src/codegen/llvm/gpu.rs`
- `src/compiler_rust/runtime/src/cuda_runtime.rs`
- `src/compiler_rust/compiler/src/codegen/runtime_sffi.rs`
- `src/compiler/35.semantics/gpu_checker.spl`
- `src/compiler/30.types/`
- `test/03_system/feature/app/compiler/`

Tasks:
1. Add a target-neutral GPU artifact model for CUDA PTX and OpenCL SPIR-V or
   OpenCL C.
2. Extend tag/attribute validation for explicit `cuda`, `opencl`, and `auto`.
3. Add tests that reject CUDA-only intrinsics on OpenCL and preserve diagnostic
   reasons.

### Agent D: Performance And Size Evidence

Files:
- `test/05_perf/`
- `test/05_perf/tauri_equiv/gui_vs_tauri_spec.spl`
- `test/05_perf/tauri_equiv/perf_tauri_runner.spl`
- `test/05_perf/graphics_2d/`
- `doc/09_report/`
- `scripts/check/check-*`
- `scripts/check/check-startup-size-performance-audit.shs`
- `scripts/check/check-web-baremetal-size-audit.shs`
- `doc/03_plan/sys_test/`

Tasks:
1. Add a normalized backend comparison harness for startup, binary size, frame
   latency, RSS, artifact build/load/submit/sync/readback.
2. Convert existing focused startup, web/bare-metal size, Tauri-equivalent,
   Electron/Node bitmap, and graphics_2d benchmark outputs into one schema.
3. Replace simulated Tauri comparison values with real Tauri app/runner
   evidence before claiming parity.
4. Cover pure Simple, Tauri, Electron, NodeJS/browser, CPU scalar/SIMD, CUDA,
   OpenCL, Vulkan, Metal, and WebGPU where available.
5. Make unavailable hardware a report state, not a pass or failure hidden inside
   rendering equality.

## Sequencing

1. Finish requirements selection for feature and NFR options.
2. Run Agent A and Agent B first; they are mostly runtime/contract scoped.
3. Start Agent C after B confirms the OpenCL runtime artifact contract.
4. Start Agent D in parallel once the first runtime evidence shape is stable.
5. Run verification with `find doc/06_spec -name '*_spec.spl' | wc -l` and
   focused Simple checks before release handoff.
