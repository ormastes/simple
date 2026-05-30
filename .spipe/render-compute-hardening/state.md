# Feature: render-compute-hardening

## Raw Request
Harden vulkan, metal, optix, rocm, cpu simd(riskv,arm,x86) 2d rendering harden. 3d partial
cuda, hip, opencl, metal compute. make common simple programming like cuda/hip like. and generate cuda/hip/opencl/metal codes or binary.
make 2d optimization codes in simple and optimize the 2d rendering using it.
make gui rendering(include text) faster than gtk.

## Task Type
feature

## Refined Goal
Implement a hardened cross-backend rendering and compute stack that provides strict 2D backend diagnostics/parity, partial 3D coverage, portable CUDA/HIP/OpenCL/Metal-style compute code generation, Simple-authored 2D optimization kernels, and measured GUI/text rendering performance beyond the GTK baseline.

## Acceptance Criteria
- AC-1: Vulkan, Metal, ROCm, CUDA, WebGPU, and CPU SIMD Engine2D paths expose strict typed probe diagnostics and do not silently fall back in strict mode.
- AC-2: Core 2D primitives and text readback have parity coverage across available hardware backends and CPU/software references.
- AC-3: Partial 3D rendering has session-managed backend coverage and strict diagnostics for unsupported backend capabilities.
- AC-4: A common Simple compute surface can emit target-specific CUDA, HIP, OpenCL C, and Metal Shading Language code or a typed binary-format artifact.
- AC-5: Simple-authored 2D optimization kernels are wired into Engine2D provider metadata with hit/change counters.
- AC-6: CPU SIMD coverage includes x86, ARM, and RISC-V capability-gated paths or typed unavailable diagnostics.
- AC-7: GUI rendering, including text, has benchmark evidence showing faster frame/text throughput than a GTK baseline on comparable scenes.

## Scope Exclusions
None for the overall persistent goal. Individual turns may land smaller verified slices while this state remains active.

## Phase
implementation-in-progress

## Log
- dev: Created state file with 7 acceptance criteria (type: feature).
- implementation: Continued from the crash/session worktree scan in the main worktree; no separate registered git worktree existed, and latest crash logs were watchdog timeouts with older interpreter overflow reports.
- implementation: Extended `src/compiler/70.backend/backend/gpu_portable_compute.spl` with explicit source-to-binary compile plans plus Simple-authored portable 2D copy, alpha-blend, and scroll kernels for CUDA, HIP, OpenCL C, and Metal targets.
- verification: Focused codegen spec `test/unit/compiler/codegen/gpu_portable_compute_spec.spl --mode=interpreter` passes with 9 scenarios, covering AC-4 source/binary artifact planning and AC-5 portable 2D optimization kernel emission.
- implementation: Wired Engine2D SIMD hit/change counters into `RenderingOptProvider` metadata and frame reports via `rendering_opt_provider_from_simd_counts`, `current_simd_rendering_opt_provider`, and `rendering_opt_report_from_simd`; added `record_simd_vectorize_change` for optimization change events.
- verification: `test/unit/lib/gpu/engine2d/rendering_opt_provider_spec.spl`, `simd_kernels_spec.spl`, and `backend_software_simd_spec.spl` pass in interpreter mode; touched SIMD provider/rendering provider files pass `bin/simple check`.
- implementation: Extended `common.ui.web_render_api` with explicit generated-WASM/no-JavaScript targets for Android, iOS, host WM, and SimpleOS WM, including target ABI mapping, validation, and binary artifact metadata.
- verification: `test/unit/lib/common/ui/web_render_api_spec.spl`, `test/unit/app/ui/web_render_backend_api_spec.spl`, `test/unit/app/ui/web_render_cache_spec.spl`, `test/unit/compiler/codegen/gpu_portable_compute_spec.spl`, `test/unit/lib/gpu/engine2d/rendering_opt_provider_spec.spl`, `test/unit/os/kernel/loader/disk_launch_manifest_spec.spl`, and `test/system/os/simpleos_ai_cli_js_node_port_spec.spl` pass in interpreter mode.
- implementation: Extended the Engine2D strict backend probe contract with typed ROCm/HIP, CPU SIMD, and OptiX diagnostics, status/backend constants, hardware classification, and no-fallback validation while preserving Vulkan, CUDA, Metal, and WebGPU shader-format diagnostics.
- verification: `test/unit/lib/gpu/engine2d/backend_probe_strict_spec.spl --mode=interpreter --clean` passes with 5 scenarios; `bin/simple check src/lib/gc_async_mut/gpu/engine2d/backend_probe.spl` passes.
- implementation: Added Engine2D generated 2D kernel dispatch metadata that maps compiler-emitted fill/copy/alpha/scroll kernels to CUDA/PTX, HIP/HSACO, OpenCL/SPIR-V, and Metal/metallib artifacts, and exposes the dispatch table as rendering optimization provider metadata.
- verification: `test/unit/lib/gpu/engine2d/generated_kernel_dispatch_spec.spl --mode=interpreter --clean` passes with 5 scenarios; `test/unit/compiler/codegen/gpu_portable_compute_spec.spl --mode=interpreter --clean` remains passing with 9 scenarios; `generated_kernel_dispatch.spl` checks cleanly.
- implementation: Extended `common.ui.window_scene` with backend-neutral WM chrome geometry for background, top command lane, content area, bottom taskbar, clock/right-icon metadata, taskbar icon metadata, DPI scaling, and inner-window drag clamping.
- verification: `test/unit/lib/common/ui/window_scene_spec.spl`, `test/unit/lib/common/ui/web_render_api_spec.spl`, `test/unit/app/ui/web_render_backend_api_spec.spl`, `test/unit/app/ui/web_render_cache_spec.spl`, `test/unit/compiler/codegen/gpu_portable_compute_spec.spl`, `test/unit/lib/gpu/engine2d/rendering_opt_provider_spec.spl`, and `test/system/os/simpleos_ai_cli_js_node_port_spec.spl` pass in interpreter mode; `bin/simple check src/lib/common/ui/window_scene.spl` passes.
- implementation: Added backend-neutral WM pointer dispatch for command-lane clock/right-icon hits, bottom taskbar pinned-app launch, running-window focus, titlebar drag start, body focus, and desktop-background clicks with focused-scene projection.
- verification: `test/unit/lib/common/ui/window_scene_spec.spl` now passes with 7 scenarios; adjacent web/WASM/render-cache, portable compute, Engine2D provider/probe/dispatch, and SimpleOS AI CLI contract specs pass in interpreter mode.
- implementation: Extended generated 2D kernel dispatch with runtime launch-plan metadata for CUDA, ROCm/HIP, OpenCL, and Metal, including entry/artifact names, launch API, grid/block geometry, argument layouts, and fail-closed unavailable plans for unsupported backends or invalid dimensions.
- verification: `test/unit/lib/gpu/engine2d/generated_kernel_dispatch_spec.spl --mode=interpreter --clean` passes with 8 scenarios; `test/unit/compiler/codegen/gpu_portable_compute_spec.spl --mode=interpreter --clean` remains passing with 9 scenarios; `bin/simple check src/lib/gc_async_mut/gpu/engine2d/generated_kernel_dispatch.spl src/lib/gc_async_mut/gpu/engine2d/mod.spl` passes with only pre-existing aggregate import warnings in `mod.spl` when checked without a source root.
- implementation: Added `common.ui.wm_runtime_dispatch` to convert shared WM dispatch results into stable runtime commands for launcher launch, window focus, drag-begin, command-lane clock/icon, and desktop-background handling.
- verification: `test/unit/lib/common/ui/wm_runtime_dispatch_spec.spl` passes with 4 scenarios; focused WM scene, web/WASM/render-cache, portable compute, Engine2D provider/probe/dispatch, and SimpleOS AI CLI contract specs pass in interpreter mode.
- implementation: Extended `common.ui.wm_runtime_dispatch` with a shared shell-state applier for launcher launches, window focus, drag-begin state, command-lane target state, desktop-background clearing/counting, and fail-closed ignored commands.
- verification: `test/unit/lib/common/ui/wm_runtime_dispatch_spec.spl` now passes with 7 scenarios; focused WM scene, web/WASM/render-cache, portable compute, Engine2D provider/probe/dispatch, and SimpleOS AI CLI contract specs pass in interpreter mode.
- implementation: Added generated 2D kernel execution-request binding that connects launch plans to prepared runtime handles for CUDA, ROCm/HIP, OpenCL, and Metal, exposes backend-specific call shapes, and rejects missing kernel, args, queue, or encoder handles before submission.
- verification: `test/unit/lib/gpu/engine2d/generated_kernel_dispatch_spec.spl --mode=interpreter --clean` passes with 11 scenarios; `test/unit/compiler/codegen/gpu_portable_compute_spec.spl --mode=interpreter --clean` remains passing with 9 scenarios; `bin/simple check src/lib/gc_async_mut/gpu/engine2d/generated_kernel_dispatch.spl src/lib/gc_async_mut/gpu/engine2d/mod.spl` passes with only the known aggregate import warnings in `mod.spl`; `sh scripts/install-spipe-dev-command.shs --check` reports `STATUS: PASS`.

## Current Blocker
The persistent goal remains incomplete: backend parity/readback evidence on real hardware, broader CPU SIMD x86/ARM/RISC-V runtime evidence, partial 3D hardening, actual runtime execution of generated kernel artifacts on real backend devices beyond prepared-call binding, direct binding of the shared WM shell-state applier into host/SimpleOS shell loops, real generated-WASM GUI artifacts, WM/QEMU/iOS/Mac/Metal capture evidence, and GTK comparison benchmarks still need implementation and verification.
