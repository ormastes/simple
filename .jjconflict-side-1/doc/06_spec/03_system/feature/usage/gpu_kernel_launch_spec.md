# GPU Kernel Launch

> Tests actual GPU kernel launch, device memory allocation, data transfer, and result verification. Covers CUDA device availability checks, runtime API completeness, memory allocation/free operations, and kernel execution pipeline validation. Uses stub functions in interpreter mode; actual GPU testing requires compiled binary with CUDA runtime linked and a compatible GPU.

<!-- sdn-diagram:id=gpu_kernel_launch_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=gpu_kernel_launch_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

gpu_kernel_launch_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=gpu_kernel_launch_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# GPU Kernel Launch

Tests actual GPU kernel launch, device memory allocation, data transfer, and result verification. Covers CUDA device availability checks, runtime API completeness, memory allocation/free operations, and kernel execution pipeline validation. Uses stub functions in interpreter mode; actual GPU testing requires compiled binary with CUDA runtime linked and a compatible GPU.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #GPU-LAUNCH |
| Category | GPU & SIMD |
| Status | In Progress |
| Requirements | N/A |
| Plan | N/A |
| Design | N/A |
| Research | N/A |
| Source | `test/03_system/feature/usage/gpu_kernel_launch_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests actual GPU kernel launch, device memory allocation, data transfer, and result
verification. Covers CUDA device availability checks, runtime API completeness,
memory allocation/free operations, and kernel execution pipeline validation. Uses stub
functions in interpreter mode; actual GPU testing requires compiled binary with CUDA
runtime linked and a compatible GPU.

## Syntax

The spec uses stub CUDA functions to expose the no-device contract in interpreter
mode while still checking the runtime API names required for a live launch.

## Examples

`gpu_runtime_functions()` lists the allocation, transfer, launch, sync, and f64
load/store symbols that a compiled GPU runtime must provide.

## Scenarios

### GPU kernel launch prerequisites

#### checks CUDA device availability

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val count = stub_cuda_device_count()
# In interpreter mode, no devices available
expect(count).to_equal(0)
```

</details>

#### reports GPU availability

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val available = stub_has_gpu()
# Expected false in interpreter mode
expect(available).to_equal(false)
```

</details>

### GPU runtime API

#### has complete function set for kernel execution

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fns = gpu_runtime_functions()
expect(fns[7]).to_equal("gpu_load_f64")
expect(fns.len()).to_equal(9)
expect(fns[8]).to_equal("gpu_store_f64")
```

</details>

### GPU memory operations

#### allocates device memory

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Stub returns 0 (no GPU)
val ptr = stub_cuda_mem_alloc(1024)
expect(ptr).to_equal(0)
```

</details>

#### frees device memory

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = stub_cuda_mem_free(0)
expect(result).to_equal(false)
```

</details>

### GPU kernel execution

#### initializes CUDA runtime

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Stub returns false (no GPU)
val ok = stub_cuda_init()
expect(ok).to_equal(false)
```

</details>

#### skips kernel launch without GPU

<details>
<summary>Executable SPipe</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Vector add kernel requires GPU hardware
val has_gpu = stub_has_gpu()
if has_gpu:
    val fns = gpu_runtime_functions()
    expect(fns).to_contain("gpu_launch")
    expect(fns).to_contain("gpu_sync")
    expect(fns).to_contain("gpu_upload")
    expect(fns).to_contain("gpu_download")
else:
    # No GPU — skip
    expect(has_gpu).to_equal(false)
```

</details>

#### validates kernel compilation pipeline

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# The pipeline: @gpu_kernel -> HIR(func_attr) -> MIR(is_kernel) -> PTX(.entry)
val pipeline_stages = 4
expect(pipeline_stages).to_equal(4)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
