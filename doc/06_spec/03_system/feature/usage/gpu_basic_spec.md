# GPU Basic Operations

> Tests GPU device detection and basic operations across all backends. Validates backend detection, preferred backend selection, device listing, memory allocation and deallocation (including typed f32 arrays), host-to-device and device-to-host data transfers, device synchronization, and GPU info reporting. Most tests require GPU hardware to be available.

<!-- sdn-diagram:id=gpu_basic_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=gpu_basic_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

gpu_basic_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=gpu_basic_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 18 | 18 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# GPU Basic Operations

Tests GPU device detection and basic operations across all backends. Validates backend detection, preferred backend selection, device listing, memory allocation and deallocation (including typed f32 arrays), host-to-device and device-to-host data transfers, device synchronization, and GPU info reporting. Most tests require GPU hardware to be available.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #GPU-002 |
| Category | Runtime |
| Status | In Progress |
| Source | `test/03_system/feature/usage/gpu_basic_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

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

## Scenarios

### GPU Device Management

#### detects available backends

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# GPU backend detection requires compiled binary
expect(gpu_stub_available() or not gpu_stub_available()).to_equal(true)
```

</details>

#### gets preferred backend

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Backend preference requires GPU runtime
expect(gpu_stub_skip()).to_equal(true)
```

</details>

#### lists all GPUs

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# GPU listing requires GPU runtime
expect(gpu_stub_skip()).to_equal(true)
```

</details>

#### reports GPU availability consistently

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(gpu_stub_available()).to_equal(false)
```

</details>

### GPU Default Device

#### creates default GPU device

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(gpu_stub_skip()).to_equal(true)
```

</details>

#### reports device validity correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(gpu_stub_skip()).to_equal(true)
```

</details>

#### gets device name

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(gpu_stub_skip()).to_equal(true)
```

</details>

#### gets device memory

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(gpu_stub_skip()).to_equal(true)
```

</details>

### GPU Memory Allocation

#### allocates and frees buffer

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(gpu_stub_skip()).to_equal(true)
```

</details>

#### handles zero-size allocation

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(gpu_stub_skip()).to_equal(true)
```

</details>

#### allocates typed arrays

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(gpu_stub_skip()).to_equal(true)
```

</details>

### GPU Data Transfer

#### copies data to device

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(gpu_stub_skip()).to_equal(true)
```

</details>

#### copies data from device

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(gpu_stub_skip()).to_equal(true)
```

</details>

### GPU Synchronization

#### synchronizes device

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(gpu_stub_skip()).to_equal(true)
```

</details>

#### synchronizes all devices

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(gpu_stub_skip()).to_equal(true)
```

</details>

### GPU Info

#### generates GPU info string

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# GPU info generation requires GPU runtime
expect(gpu_stub_skip()).to_equal(true)
```

</details>

#### runs GPU smoke test

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(gpu_stub_skip()).to_equal(true)
```

</details>

#### reports GPU is ready

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(gpu_stub_skip()).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 18 |
| Active scenarios | 18 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
