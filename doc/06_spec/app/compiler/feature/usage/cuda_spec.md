# CUDA Backend

Tests NVIDIA CUDA backend functionality including device detection and selection, memory allocation and transfer operations (host-to-device, device-to-host, device-to-device), PTX kernel compilation and function loading, stream creation and synchronization, and error handling. Most tests require CUDA hardware.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #GPU-001 |
| Category | Runtime |
| Status | In Progress |
| Source | `test/feature/usage/cuda_spec.spl` |
| Updated | 2026-04-07 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 18 |
| Active scenarios | 18 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

## Overview

Tests NVIDIA CUDA backend functionality including device detection and selection,
memory allocation and transfer operations (host-to-device, device-to-host,
device-to-device), PTX kernel compilation and function loading, stream creation
and synchronization, and error handling. Most tests require CUDA hardware.

## Syntax

```simple
val available = cuda_available()
val ptr = cuda_alloc(1024)
cuda_copy_to_device(ptr, data)
val module = cuda_compile(VECTOR_ADD_PTX)
```
CUDA Backend Tests

Tests specific to CUDA backend functionality.
These tests require NVIDIA CUDA to be available.

Note: The CUDA extern functions (rt_cuda_*) are not available in interpreter mode.
These tests are structured to load without errors; actual CUDA testing requires
a compiled binary with CUDA runtime linked.

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `target/test-artifacts/feature/usage/cuda/result.json` |

## Scenarios

- checks CUDA availability
- reports CUDA not available in interpreter mode
- requires CUDA for device selection
- requires CUDA for device info
- requires CUDA for compute capability
- requires CUDA for memory allocation
- requires CUDA for memset
- requires CUDA for host to device copy
- requires CUDA for device to host copy
- requires CUDA for device to device copy
- requires CUDA for PTX compilation
- requires CUDA for kernel function loading
- requires CUDA for stream creation
- requires CUDA for stream synchronization
- requires CUDA for error reporting
- requires CUDA for error peeking
- requires CUDA for device synchronization
- requires CUDA for gpu_cuda wrapper
