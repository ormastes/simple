# Vulkan Compute Backend

Tests Vulkan compute backend functionality including initialization and shutdown, device selection and info retrieval, storage buffer allocation and data transfers, GLSL compute shader compilation and pipeline creation, descriptor set management, command recording and submission, synchronization, error handling, and the gpu_vulkan device wrapper. Requires Vulkan SDK to be available.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #GPU-003 |
| Category | Runtime |
| Status | In Progress |
| Source | `test/feature/usage/vulkan_spec.spl` |
| Updated | 2026-04-07 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 22 |
| Active scenarios | 22 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

## Overview

Tests Vulkan compute backend functionality including initialization and shutdown,
device selection and info retrieval, storage buffer allocation and data transfers,
GLSL compute shader compilation and pipeline creation, descriptor set management,
command recording and submission, synchronization, error handling, and the
gpu_vulkan device wrapper. Requires Vulkan SDK to be available.

## Syntax

```simple
vulkan_init()
vulkan_select_device(0)
val buf = vulkan_alloc_storage(1024)
val shader = vulkan_compile_glsl(VECTOR_ADD_GLSL)
```
Vulkan Compute Backend Tests

Tests specific to Vulkan compute functionality.
These tests require Vulkan SDK to be available.

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `target/test-artifacts/feature/usage/vulkan/result.json` |

## Scenarios

- checks Vulkan availability
- initializes Vulkan
- reports device count
- shuts down cleanly
- selects device
- gets device info
- reports device type
- gets API version
- allocates storage buffer
- allocates different buffer types
- copies data to buffer
- copies data from buffer
- copies between buffers
- compiles GLSL compute shader
- creates compute pipeline
- creates descriptor set
- binds buffers to descriptors
- records and submits commands
- waits for device idle
- gets last error message
- creates gpu_vulkan device wrapper
- synchronizes via wrapper
