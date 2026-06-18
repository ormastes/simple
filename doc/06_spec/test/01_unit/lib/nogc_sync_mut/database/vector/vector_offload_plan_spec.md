# Vector Offload Plan Specification

> <details>

<!-- sdn-diagram:id=vector_offload_plan_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=vector_offload_plan_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

vector_offload_plan_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=vector_offload_plan_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Vector Offload Plan Specification

## Scenarios

### vector search GPU offload planner

#### should estimate vector search batch bytes

- Estimate candidate matrix plus query vector bytes
   - Expected: bytes equals `1024`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Estimate candidate matrix plus query vector bytes")
val bytes = vector_search_estimated_batch_bytes(7, 16)
expect(bytes).to_equal(1024)
```

</details>

#### should plan eligible coarse vector search for GPU batch execution

- Plan a large vector search batch with current generation and GPU available
- vector snapshot
   - Expected: plan.batch.execution.decision.path equals `GpuWdbDecisionPath.GpuEvidence`
   - Expected: plan.batch.execution.target equals `gpu_db_vector_search_batch`
   - Expected: plan.batch.queue_depth_after equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Plan a large vector search batch with current generation and GPU available")
val budget = gpu_wdb_default_budget()
val plan = plan_vector_search_offload(
    DistanceMetric.Cosine,
    128,
    16,
    true,
    vector_snapshot(2, true, true, true),
    budget
)
expect(plan.batch.execution.decision.path).to_equal(GpuWdbDecisionPath.GpuEvidence)
expect(plan.batch.execution.target).to_equal("gpu_db_vector_search_batch")
expect(plan.batch.queue_depth_after).to_equal(3)
expect(vector_search_plan_uses_gpu(plan)).to_be(true)
```

</details>

#### should keep small vector search batches on CPU

- Plan a small batch that cannot justify GPU overhead
- vector snapshot
   - Expected: plan.batch.execution.decision.path equals `GpuWdbDecisionPath.CpuFallback`
   - Expected: plan.batch.execution.decision.reason equals `batch-too-small`
   - Expected: plan.batch.queue_depth_after equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Plan a small batch that cannot justify GPU overhead")
val budget = gpu_wdb_default_budget()
val plan = plan_vector_search_offload(
    DistanceMetric.Euclidean,
    4,
    8,
    true,
    vector_snapshot(0, true, true, true),
    budget
)
expect(plan.batch.execution.decision.path).to_equal(GpuWdbDecisionPath.CpuFallback)
expect(plan.batch.execution.decision.reason).to_equal("batch-too-small")
expect(plan.batch.queue_depth_after).to_equal(0)
```

</details>

#### should fall back when the GPU runtime is unavailable

- Plan a large vector search batch while GPU is unavailable
- vector snapshot
   - Expected: plan.batch.execution.decision.path equals `GpuWdbDecisionPath.CpuFallback`
   - Expected: plan.batch.execution.decision.reason equals `gpu-unavailable`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Plan a large vector search batch while GPU is unavailable")
val budget = gpu_wdb_default_budget()
val plan = plan_vector_search_offload(
    DistanceMetric.DotProduct,
    128,
    16,
    true,
    vector_snapshot(0, false, true, true),
    budget
)
expect(plan.batch.execution.decision.path).to_equal(GpuWdbDecisionPath.CpuFallback)
expect(plan.batch.execution.decision.reason).to_equal("gpu-unavailable")
```

</details>

#### should reject metadata filtering that is not CPU-owned

- Plan a NoSQL-style metadata filtered vector search
- vector snapshot
   - Expected: plan.batch.execution.decision.path equals `GpuWdbDecisionPath.Reject`
   - Expected: plan.batch.execution.decision.reason equals `metadata-filter-must-stay-cpu-owned`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Plan a NoSQL-style metadata filtered vector search")
val plan = plan_vector_search_offload_default(
    DistanceMetric.Cosine,
    128,
    16,
    false,
    vector_snapshot(0, true, true, true)
)
expect(plan.batch.execution.decision.path).to_equal(GpuWdbDecisionPath.Reject)
expect(plan.batch.execution.decision.reason).to_equal("metadata-filter-must-stay-cpu-owned")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_sync_mut/database/vector/vector_offload_plan_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- vector search GPU offload planner

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
