# Compute Run Specification

> <details>

<!-- sdn-diagram:id=compute_run_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=compute_run_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

compute_run_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=compute_run_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Compute Run Specification

## Scenarios

### compute_run end-to-end pipeline

#### launch plan: grid = ceil(n / 256)

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(compute_grid_for(0)).to_equal(0)
expect(compute_grid_for(1)).to_equal(1)
expect(compute_grid_for(256)).to_equal(1)
expect(compute_grid_for(257)).to_equal(2)
expect(compute_grid_for(512)).to_equal(2)
expect(compute_grid_for(513)).to_equal(3)
```

</details>

#### cpu reference scales each element

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val out = cpu_transform_scale_f32([2.0, 3.0, 4.0], 2.0)
expect(out.len()).to_equal(3)
expect(out[0]).to_equal(4.0)
expect(out[1]).to_equal(6.0)
expect(out[2]).to_equal(8.0)
```

</details>

#### cpu target runs on CPU with scalar backend

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = run_transform_scale_f32([2.0, 3.0, 4.0], 2.0, cpu_target())
expect(r.ran_on_cpu).to_be(true)
expect(r.backend).to_equal("scalar")
expect(r.grid_x).to_equal(1)
expect(r.block_x).to_equal(256)
expect(r.data[1]).to_equal(6.0)
```

</details>

#### cuda target with NO device falls back to CPU (no false gpu-ran claim)

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = run_transform_scale_f32([2.0, 3.0, 4.0], 2.0, cuda_target())
expect(r.backend).to_equal("cuda")
expect(r.device_count).to_equal(0)
expect(r.ran_on_cpu).to_be(true)
expect(r.data[2]).to_equal(8.0)
```

</details>

#### result preserves input length

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = run_transform_scale_f32([1.0, 1.0, 1.0, 1.0, 1.0], 3.0, cpu_target())
expect(r.data.len()).to_equal(5)
expect(r.data[4]).to_equal(3.0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/compute/compute_run_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- compute_run end-to-end pipeline

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
