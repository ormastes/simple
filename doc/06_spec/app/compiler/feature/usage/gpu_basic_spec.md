# GPU Basic Operations

Tests GPU device detection and basic operations across all backends. Validates backend detection, preferred backend selection, device listing, memory allocation and deallocation (including typed f32 arrays), host-to-device and device-to-host data transfers, device synchronization, and GPU info reporting. Most tests require GPU hardware to be available.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #GPU-002 |
| Category | Runtime |
| Status | In Progress |
| Source | `test/feature/usage/gpu_basic_spec.spl` |
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

Tests GPU device detection and basic operations across all backends. Validates
backend detection, preferred backend selection, device listing, memory allocation
and deallocation (including typed f32 arrays), host-to-device and device-to-host
data transfers, device synchronization, and GPU info reporting. Most tests
require GPU hardware to be available.

## Syntax

```simple
val backends = detect_backends()
val device = gpu_default()
val buffer = gpu_alloc(device, 1024)
gpu_copy_to(buffer, data)
```
GPU Basic Tests

Tests for GPU device detection and basic operations.

Note: The GPU functions (detect_backends, gpu_default, etc.) are not available
in interpreter mode. These tests are structured to load without errors;
actual GPU testing requires a compiled binary with GPU runtime linked.

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `target/test-artifacts/feature/usage/gpu_basic/result.json` |

## Scenarios

- detects available backends
- gets preferred backend
- lists all GPUs
- reports GPU availability consistently
- creates default GPU device
- reports device validity correctly
- gets device name
- gets device memory
- allocates and frees buffer
- handles zero-size allocation
- allocates typed arrays
- copies data to device
- copies data from device
- synchronizes device
- synchronizes all devices
- generates GPU info string
- runs GPU smoke test
- reports GPU is ready
