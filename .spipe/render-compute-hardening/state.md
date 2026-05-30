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
dev-done

## Log
- dev: Created state file with 7 acceptance criteria (type: feature).
