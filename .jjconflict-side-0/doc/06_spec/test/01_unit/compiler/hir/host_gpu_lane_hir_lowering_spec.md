# Host Gpu Lane Hir Lowering Specification

> <details>

<!-- sdn-diagram:id=host_gpu_lane_hir_lowering_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=host_gpu_lane_hir_lowering_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

host_gpu_lane_hir_lowering_spec -> std
host_gpu_lane_hir_lowering_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=host_gpu_lane_hir_lowering_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Host Gpu Lane Hir Lowering Specification

## Scenarios

### Host/GPU lane HIR lowering

#### preserves target.later gpu lane metadata in HIR

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = "fn f():\n    target.later(max_packet: 512) gpu \\:\n        val draw_ir_batch = \"batch\"\n"
expect(host_gpu_hir_lane_score(src, "f")).to_equal(112)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/hir/host_gpu_lane_hir_lowering_spec.spl` |
| Updated | 2026-07-06 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Host/GPU lane HIR lowering

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
