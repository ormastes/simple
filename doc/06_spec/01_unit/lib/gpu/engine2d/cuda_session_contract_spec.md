# Cuda Session Contract Specification

> <details>

<!-- sdn-diagram:id=cuda_session_contract_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=cuda_session_contract_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

cuda_session_contract_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=cuda_session_contract_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Cuda Session Contract Specification

## Scenarios

### CudaSession compute contract

#### reports CUDA kind and availability without initializing hardware

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val session = CudaSession.create()

expect(session.kind() == BackendSessionKind.Cuda).to_equal(true)
expect(session.is_available()).to_equal(cuda_available())
expect(session.is_valid()).to_equal(false)
```

</details>

#### fails closed when launching without a loaded module

<details>
<summary>Executable SPipe</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val session = CudaSession.create()

expect(session.launch_kernel("kernel_clear", 1, 1, 1, 1)).to_equal(1)
expect(session.launch_kernel_args("kernel_clear", 1, 1, 1, 1, 1, 1, 4096)).to_equal(1)
expect(session.fill_kernel(64, 64, 4096)).to_equal(1)
expect(session.copy_kernel(64, 64, 4096)).to_equal(1)
expect(session.alpha_blend_kernel(64, 64, 4096)).to_equal(1)
expect(session.scroll_kernel(64, 64, 4096)).to_equal(1)
```

</details>

#### fails generated 2D launches closed for invalid argument buffers

1. var session = CudaSession create
   - Expected: session.launch_kernel_args("kernel_clear", 1, 1, 1, 1, 1, 1, 0) equals `1`
   - Expected: session.fill_kernel(64, 64, 0) equals `1`
   - Expected: session.fill_kernel(0, 64, 4096) equals `1`
   - Expected: session.launch_generated_2d("unsupported", 64, 64, 4096) equals `1`


<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = CudaSession.create()
session.module_cache = 1234

expect(session.launch_kernel_args("kernel_clear", 1, 1, 1, 1, 1, 1, 0)).to_equal(1)
expect(session.fill_kernel(64, 64, 0)).to_equal(1)
expect(session.fill_kernel(0, 64, 4096)).to_equal(1)
expect(session.launch_generated_2d("unsupported", 64, 64, 4096)).to_equal(1)
```

</details>

#### shutdown is safe on an uninitialized session

1. var session = CudaSession create

2. session shutdown
   - Expected: session.is_valid() is false
   - Expected: session.ref_count equals `0`


<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = CudaSession.create()

session.shutdown()
expect(session.is_valid()).to_equal(false)
expect(session.ref_count).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gpu/engine2d/cuda_session_contract_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- CudaSession compute contract

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
