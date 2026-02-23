# CUDA Backend

**Feature ID:** #GPU-001 | **Category:** Runtime | **Status:** In Progress

_Source: `test/feature/usage/cuda_spec.spl`_

---

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

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 18 |

## Test Structure

### CUDA Availability

- ✅ checks CUDA availability
- ✅ reports device count
### CUDA Device Selection

- ✅ sets and gets current device
- ✅ gets device info
- ✅ gets compute capability
### CUDA Memory Operations

- ✅ allocates CUDA memory
- ✅ performs memset
- ✅ copies host to device
- ✅ copies device to host
- ✅ copies device to device
### CUDA Kernel Compilation

- ✅ compiles PTX module
- ✅ gets kernel function from module
### CUDA Streams

- ✅ creates and destroys stream
- ✅ synchronizes stream
### CUDA Error Handling

- ✅ gets last error
- ✅ peeks at error without clearing
### CUDA Synchronization

- ✅ synchronizes device
- ✅ creates gpu_cuda device wrapper

