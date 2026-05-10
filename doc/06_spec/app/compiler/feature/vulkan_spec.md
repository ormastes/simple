# Vulkan Compute Backend

**Feature ID:** #GPU-003 | **Category:** Runtime | **Status:** In Progress

_Source: `test/feature/usage/vulkan_spec.spl`_

---

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

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 22 |

## Test Structure

### Vulkan Availability

- ✅ checks Vulkan availability
### Vulkan Initialization

- ✅ initializes Vulkan
- ✅ reports device count
- ✅ shuts down cleanly
### Vulkan Device Selection

- ✅ selects device
- ✅ gets device info
- ✅ reports device type
- ✅ gets API version
### Vulkan Buffer Operations

- ✅ allocates storage buffer
- ✅ allocates different buffer types
- ✅ copies data to buffer
- ✅ copies data from buffer
- ✅ copies between buffers
### Vulkan Shader Compilation

- ✅ compiles GLSL compute shader
- ✅ creates compute pipeline
### Vulkan Descriptor Sets

- ✅ creates descriptor set
- ✅ binds buffers to descriptors
### Vulkan Command Execution

- ✅ records and submits commands
- ✅ waits for device idle
### Vulkan Error Handling

- ✅ gets last error message
### Vulkan GPU Wrapper

- ✅ creates gpu_vulkan device wrapper
- ✅ synchronizes via wrapper

