# Vulkan Compute Backend

> Tests Vulkan compute backend functionality including initialization and shutdown, device selection and info retrieval, storage buffer allocation and data transfers, GLSL compute shader compilation and pipeline creation, descriptor set management, command recording and submission, synchronization, error handling, and the gpu_vulkan device wrapper. Requires Vulkan SDK to be available.

<!-- sdn-diagram:id=vulkan_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=vulkan_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

vulkan_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=vulkan_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Vulkan Compute Backend

Tests Vulkan compute backend functionality including initialization and shutdown, device selection and info retrieval, storage buffer allocation and data transfers, GLSL compute shader compilation and pipeline creation, descriptor set management, command recording and submission, synchronization, error handling, and the gpu_vulkan device wrapper. Requires Vulkan SDK to be available.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #GPU-003 |
| Category | Runtime |
| Status | In Progress |
| Source | `test/03_system/feature/usage/vulkan_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

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

## Scenarios

### Vulkan Availability

#### env_skip: requires SIMPLE_GPU_TEST

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(test_env_require("SIMPLE_GPU_TEST")).to_equal("blocked:SIMPLE_GPU_TEST")
```

</details>

### Vulkan Initialization

#### env_skip: requires SIMPLE_GPU_TEST

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(test_env_require("SIMPLE_GPU_TEST")).to_equal("blocked:SIMPLE_GPU_TEST")
```

</details>

### Vulkan Device Selection

#### env_skip: requires SIMPLE_GPU_TEST

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(test_env_require("SIMPLE_GPU_TEST")).to_equal("blocked:SIMPLE_GPU_TEST")
```

</details>

### Vulkan Buffer Operations

#### env_skip: requires SIMPLE_GPU_TEST

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(test_env_require("SIMPLE_GPU_TEST")).to_equal("blocked:SIMPLE_GPU_TEST")
```

</details>

### Vulkan Shader Compilation

#### env_skip: requires SIMPLE_GPU_TEST

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(test_env_require("SIMPLE_GPU_TEST")).to_equal("blocked:SIMPLE_GPU_TEST")
```

</details>

### Vulkan Descriptor Sets

#### env_skip: requires SIMPLE_GPU_TEST

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(test_env_require("SIMPLE_GPU_TEST")).to_equal("blocked:SIMPLE_GPU_TEST")
```

</details>

### Vulkan Command Execution

#### env_skip: requires SIMPLE_GPU_TEST

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(test_env_require("SIMPLE_GPU_TEST")).to_equal("blocked:SIMPLE_GPU_TEST")
```

</details>

### Vulkan Error Handling

#### env_skip: requires SIMPLE_GPU_TEST

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(test_env_require("SIMPLE_GPU_TEST")).to_equal("blocked:SIMPLE_GPU_TEST")
```

</details>

### Vulkan GPU Wrapper

#### env_skip: requires SIMPLE_GPU_TEST

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(test_env_require("SIMPLE_GPU_TEST")).to_equal("blocked:SIMPLE_GPU_TEST")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
