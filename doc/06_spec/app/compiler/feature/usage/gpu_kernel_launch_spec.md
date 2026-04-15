# GPU Kernel Launch

Tests actual GPU kernel launch, device memory allocation, data transfer, and result verification. Covers CUDA device availability checks, runtime API completeness, memory allocation/free operations, and kernel execution pipeline validation. Uses stub functions in interpreter mode; actual GPU testing requires compiled binary with CUDA runtime linked and a compatible GPU.

## At a Glance

| Field | Value |
|-------|-------|
| Category | GPU & SIMD |
| Status | In Progress |
| Source | `test/feature/usage/gpu_kernel_launch_spec.spl` |
| Updated | 2026-04-07 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

## Overview

Tests actual GPU kernel launch, device memory allocation, data transfer, and result
verification. Covers CUDA device availability checks, runtime API completeness,
memory allocation/free operations, and kernel execution pipeline validation. Uses stub
functions in interpreter mode; actual GPU testing requires compiled binary with CUDA
runtime linked and a compatible GPU.

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `target/test-artifacts/feature/usage/gpu_kernel_launch/result.json` |

## Scenarios

- checks CUDA device availability
- reports GPU availability
- has complete function set for kernel execution
- allocates device memory
- frees device memory
- initializes CUDA runtime
- skips kernel launch without GPU
- validates kernel compilation pipeline
