# GPU Basic Operations

**Feature ID:** #GPU-002 | **Category:** Runtime | **Status:** In Progress

_Source: `test/feature/usage/gpu_basic_spec.spl`_

---

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

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 18 |

## Test Structure

### GPU Device Management

- ✅ detects available backends
- ✅ gets preferred backend
- ✅ lists all GPUs
- ✅ reports GPU availability consistently
### GPU Default Device

- ✅ creates default GPU device
- ✅ reports device validity correctly
- ✅ gets device name
- ✅ gets device memory
### GPU Memory Allocation

- ✅ allocates and frees buffer
- ✅ handles zero-size allocation
- ✅ allocates typed arrays
### GPU Data Transfer

- ✅ copies data to device
- ✅ copies data from device
### GPU Synchronization

- ✅ synchronizes device
- ✅ synchronizes all devices
### GPU Info

- ✅ generates GPU info string
- ✅ runs GPU smoke test
- ✅ reports GPU is ready

