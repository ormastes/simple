# Host Gpu Lane Codegen Marker Specification

> <details>

<!-- sdn-diagram:id=host_gpu_lane_codegen_marker_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=host_gpu_lane_codegen_marker_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

host_gpu_lane_codegen_marker_spec -> std
host_gpu_lane_codegen_marker_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=host_gpu_lane_codegen_marker_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Host Gpu Lane Codegen Marker Specification

## Scenarios

### Host/GPU lane native codegen markers

#### consumes lane markers as queue-boundary accounting instead of unsupported instructions

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(marker_codegen_score()).to_equal(1111111)
```

</details>

#### diagnoses an unmatched host GPU lane end marker

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(unmatched_end_error_count()).to_equal(1)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/codegen/host_gpu_lane_codegen_marker_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Host/GPU lane native codegen markers

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
