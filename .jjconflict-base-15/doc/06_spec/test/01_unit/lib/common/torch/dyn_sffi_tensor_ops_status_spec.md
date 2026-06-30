# Dyn Sffi Tensor Ops Status Specification

> <details>

<!-- sdn-diagram:id=dyn_sffi_tensor_ops_status_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=dyn_sffi_tensor_ops_status_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

dyn_sffi_tensor_ops_status_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=dyn_sffi_tensor_ops_status_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Dyn Sffi Tensor Ops Status Specification

## Scenarios

### dynamic torch tensor value status surface

#### keeps legacy 1d construction handle compatible while exposing status

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = dyn_torch_tensor_from_values_1d_result([1.0, 2.0])
val legacy = dyn_torch_tensor_from_values_1d([1.0, 2.0])

if dyn_torch_available():
    expect(result.status == "ready" or result.status == "error").to_equal(true)
else:
    expect(result.status).to_equal("unavailable")
    expect(result.reason).to_equal("libtorch_unavailable")
    expect(result.handle).to_equal(0)
    expect(legacy).to_equal(0)
```

</details>

#### reports invalid 2d tensor shapes without calling the runtime

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = dyn_torch_tensor_from_values_2d_result([1.0, 2.0, 3.0], 2, 2)
val legacy = dyn_torch_tensor_from_values_2d([1.0, 2.0, 3.0], 2, 2)

if dyn_torch_available():
    expect(result.status).to_equal("invalid")
    expect(result.reason).to_equal("invalid_shape")
    expect(result.handle).to_equal(0)
    expect(legacy).to_equal(0)
else:
    expect(result.status).to_equal("unavailable")
    expect(result.reason).to_equal("libtorch_unavailable")
    expect(result.handle).to_equal(0)
```

</details>

#### reports value-copy status for unavailable or invalid tensor handles

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = dyn_torch_tensor_copy_values_result(0, 4)
val legacy = dyn_torch_tensor_copy_values(0, 4)

expect(result.values.len()).to_equal(0)
expect(legacy.len()).to_equal(0)
if dyn_torch_available():
    expect(result.status).to_equal("invalid")
    expect(result.reason).to_equal("invalid_handle")
else:
    expect(result.status).to_equal("unavailable")
    expect(result.reason).to_equal("libtorch_unavailable")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/torch/dyn_sffi_tensor_ops_status_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- dynamic torch tensor value status surface

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
