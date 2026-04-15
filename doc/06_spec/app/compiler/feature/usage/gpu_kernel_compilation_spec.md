# GPU Kernel Compilation

Tests that @gpu_kernel functions are properly lowered through HIR -> MIR and compiled to PTX with .entry directives. Validates GPU intrinsic name recognition (thread ID, synchronization, memory, atomic operations), PTX output structure (version, target, address size, directives), special register mappings, and the full compilation pipeline from Simple source to GPU-ready output. No GPU hardware required.

## At a Glance

| Field | Value |
|-------|-------|
| Category | GPU & SIMD |
| Status | In Progress |
| Source | `test/feature/usage/gpu_kernel_compilation_spec.spl` |
| Updated | 2026-04-07 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 23 |
| Active scenarios | 23 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

## Overview

Tests that @gpu_kernel functions are properly lowered through HIR -> MIR and compiled
to PTX with .entry directives. Validates GPU intrinsic name recognition (thread ID,
synchronization, memory, atomic operations), PTX output structure (version, target,
address size, directives), special register mappings, and the full compilation pipeline
from Simple source to GPU-ready output. No GPU hardware required.

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `target/test-artifacts/feature/usage/gpu_kernel_compilation/result.json` |

## Scenarios

- recognizes all thread ID intrinsic names
- recognizes all synchronization intrinsic names
- recognizes all atomic operation intrinsic names
- recognizes all memory intrinsic names
- load intrinsics produce global memory PTX
- store intrinsics produce global memory PTX
- all intrinsic names start with gpu_ prefix
- emits correct PTX version header
- emits correct target for SM 8.6 (Ada Lovelace)
- emits correct target for SM 7.5 (Turing)
- uses 64-bit address size
- uses .entry directive for kernel functions
- uses .func directive for device functions
- maps gpu_local_id_x to %tid.x
- maps gpu_block_id_x to %ctaid.x
- maps gpu_block_dim_x to %ntid.x
- maps gpu_grid_dim_x to %nctaid.x
- @gpu_kernel attribute is recognized by parser
- pipeline has 5 stages from source to PTX
- MIR instructions include GPU-specific operations
- CudaBackend can be created with compute capability
- GpuBarrierScope has Workgroup variant
- GpuMemFence has device and system scopes
