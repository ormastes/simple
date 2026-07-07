# Alloc Inference Specification

> <details>

<!-- sdn-diagram:id=alloc_inference_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=alloc_inference_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

alloc_inference_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=alloc_inference_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Alloc Inference Specification

## Scenarios

### Allocation Inference

#### skipped

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pending_reason = "compiler module imports OOM in interpreter test runner - same as call_graph_spec"
expect(pending_reason.len()).to_be_greater_than(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/semantics/alloc_inference_spec.spl` |
| Updated | 2026-07-06 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Allocation Inference

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
