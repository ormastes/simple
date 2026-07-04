# Conv Specification

> <details>

<!-- sdn-diagram:id=conv_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=conv_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

conv_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=conv_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Conv Specification

## Scenarios

### Conv

#### keeps Conv2d layer construction and forward path available

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = torch_mod_source()

expect(source).to_contain("class Conv2d:")
expect(source).to_contain("static fn create(in_channels: i64, out_channels: i64, kernel_size: i64, stride: i64, padding: i64) -> Conv2d")
expect(source).to_contain("Tensor.randn([out_channels, in_channels, kernel_size, kernel_size])")
expect(source).to_contain("rt_torch_nn_conv2d(x.handle, self.weight.handle, self.bias.handle, stride_arr, padding_arr, dilation_arr, 1)")
```

</details>

#### keeps Conv2d parameter exposure available

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = torch_mod_source()

expect(source).to_contain("fn parameters() -> [Tensor]")
expect(source).to_contain("[self.weight, self.bias]")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/pure/nn/conv_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Conv

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
