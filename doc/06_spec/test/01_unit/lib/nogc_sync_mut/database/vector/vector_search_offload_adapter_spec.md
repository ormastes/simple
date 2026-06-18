# Vector Search GPU Offload Adapter

> These scenarios connect vector-search planning to the reusable web/database GPU queue and target registry. CPU search results remain authoritative until a real GPU target implementation can be called and compared.

<!-- sdn-diagram:id=vector_search_offload_adapter_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=vector_search_offload_adapter_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

vector_search_offload_adapter_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=vector_search_offload_adapter_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Vector Search GPU Offload Adapter

These scenarios connect vector-search planning to the reusable web/database GPU queue and target registry. CPU search results remain authoritative until a real GPU target implementation can be called and compared.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Requirements | doc/02_requirements/feature/gpu_web_db_offload.md |
| Plan | doc/03_plan/agent_tasks/gpu_web_db_offload_impl_status.md |
| Design | doc/05_design/gpu_web_db_offload.md |
| Research | N/A |
| Source | `test/01_unit/lib/nogc_sync_mut/database/vector/vector_search_offload_adapter_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

These scenarios connect vector-search planning to the reusable web/database GPU
queue and target registry. CPU search results remain authoritative until a real
GPU target implementation can be called and compared.

## Requirements

**Requirements:** doc/02_requirements/feature/gpu_web_db_offload.md

- Vector search may dispatch coarse batches through `gpu_db_vector_search_batch`.
- Metadata filtering must remain CPU-owned before GPU vector search accounting.
- CPU vector search results remain authoritative.

## Plan

**Plan:** doc/03_plan/agent_tasks/gpu_web_db_offload_impl_status.md

## Design

**Design:** doc/05_design/gpu_web_db_offload.md

## Research

**Research:** N/A

## Examples

Call `vector_search_offload_execute` after CPU vector search has produced
authoritative `SearchResult` values, then inspect the offload evidence.

## Scenarios

### vector search offload adapter

#### should dispatch coarse vector search when the GPU target is registered

- Submit vector search through registry and queue accounting
- sample results
   - Expected: execution.submission.dispatch_target equals `gpu_db_vector_search_batch`
   - Expected: execution.submission.stream_id equals `0`
   - Expected: execution.state_after.queue_depth equals `0`
   - Expected: execution.state_after.completed_count equals `1`
   - Expected: execution.results.len() equals `2`
   - Expected: execution.profile.data_path equals `GpuWdbCoarseDataPath.GpuIndexBatch`


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Submit vector search through registry and queue accounting")
val budget = gpu_wdb_default_budget()
val state = gpu_wdb_queue_initial(2)
val registry = gpu_wdb_library_with_targets("cuda", 1, ["gpu_db_vector_search_batch"])
val execution = vector_search_offload_execute(
    DistanceMetric.Cosine,
    128,
    16,
    true,
    state,
    registry,
    true,
    true,
    true,
    budget,
    sample_results()
)
expect(vector_search_offload_used_gpu(execution)).to_be(true)
expect(execution.submission.dispatch_target).to_equal("gpu_db_vector_search_batch")
expect(execution.submission.stream_id).to_equal(0)
expect(execution.state_after.queue_depth).to_equal(0)
expect(execution.state_after.completed_count).to_equal(1)
expect(execution.results.len()).to_equal(2)
expect(execution.cpu_authoritative).to_be(true)
expect(execution.profile.data_path).to_equal(GpuWdbCoarseDataPath.GpuIndexBatch)
expect(vector_search_profile_allows_gpu(execution)).to_be(true)
```

</details>

#### should validate matching vector GPU candidates before replacing CPU results

- Accept vector result replacement only after CPU-oracle ID agreement
- gpu wdb queue initial
- sample results
- sample results
   - Expected: execution.validation_reason equals `gpu-cpu-vector-match`
   - Expected: execution.results[1].id equals `b`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Accept vector result replacement only after CPU-oracle ID agreement")
val budget = gpu_wdb_default_budget()
val registry = gpu_wdb_library_with_targets("cuda", 1, ["gpu_db_vector_search_batch"])
val execution = vector_search_offload_execute_validated(
    DistanceMetric.Cosine,
    128,
    16,
    true,
    gpu_wdb_queue_initial(2),
    registry,
    true,
    true,
    true,
    budget,
    sample_results(),
    sample_results()
)
expect(vector_search_offload_used_gpu(execution)).to_be(true)
expect(execution.cpu_authoritative).to_be(false)
expect(execution.gpu_candidate_validated).to_be(true)
expect(execution.validation_reason).to_equal("gpu-cpu-vector-match")
expect(execution.results[1].id).to_equal("b")
```

</details>

#### should keep CPU vector results authoritative when GPU candidates mismatch

- Reject vector result replacement when candidate IDs disagree
- gpu wdb queue initial
- sample results
- mismatched results
   - Expected: execution.submission.dispatch_target equals `cpu_fallback`
   - Expected: execution.validation_reason equals `gpu-cpu-vector-mismatch`
   - Expected: execution.results[1].id equals `b`


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Reject vector result replacement when candidate IDs disagree")
val budget = gpu_wdb_default_budget()
val registry = gpu_wdb_library_with_targets("cuda", 1, ["gpu_db_vector_search_batch"])
val execution = vector_search_offload_execute_validated(
    DistanceMetric.Cosine,
    128,
    16,
    true,
    gpu_wdb_queue_initial(2),
    registry,
    true,
    true,
    true,
    budget,
    sample_results(),
    mismatched_results()
)
expect(vector_search_offload_used_gpu(execution)).to_be(false)
expect(execution.submission.dispatch_target).to_equal("cpu_fallback")
expect(execution.cpu_authoritative).to_be(true)
expect(execution.gpu_candidate_validated).to_be(false)
expect(execution.validation_reason).to_equal("gpu-cpu-vector-mismatch")
expect(execution.results[1].id).to_equal("b")
```

</details>

#### should replace CPU vector results only after native candidates match

- Require measured native vector candidates to match CPU result IDs
- gpu wdb queue initial
- gpu wdb device backend
- gpu wdb default budget
- sample results
- sample results
   - Expected: execution.execution.validation_reason equals `production-gpu-vector-match`
   - Expected: execution.execution.results[1].id equals `b`


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Require measured native vector candidates to match CPU result IDs")
val execution = vector_search_offload_execute_device_validated(
    DistanceMetric.Cosine,
    128,
    16,
    true,
    gpu_wdb_queue_initial(2),
    gpu_wdb_device_backend("cuda", 7, ["gpu_db_vector_search_batch"], true, "cuda-device-0"),
    true,
    7,
    true,
    gpu_wdb_default_budget(),
    sample_results(),
    sample_results(),
    100,
    210,
    64,
    "cuda-event"
)
expect(vector_search_offload_used_gpu(execution.execution)).to_be(true)
expect(execution.execution.cpu_authoritative).to_be(false)
expect(execution.execution.gpu_candidate_validated).to_be(true)
expect(execution.execution.validation_reason).to_equal("production-gpu-vector-match")
expect(execution.execution.results[1].id).to_equal("b")
expect(execution.device_result.production_device_claim).to_be(true)
```

</details>

#### should keep CPU vector results authoritative when native candidates mismatch

- Reject measured native vector candidates that disagree with CPU IDs
- gpu wdb queue initial
- gpu wdb device backend
- gpu wdb default budget
- sample results
- mismatched results
   - Expected: execution.execution.validation_reason equals `production-gpu-vector-mismatch`
   - Expected: execution.execution.submission.dispatch_target equals `cpu_fallback`
   - Expected: execution.execution.results[1].id equals `b`


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Reject measured native vector candidates that disagree with CPU IDs")
val execution = vector_search_offload_execute_device_validated(
    DistanceMetric.Cosine,
    128,
    16,
    true,
    gpu_wdb_queue_initial(2),
    gpu_wdb_device_backend("cuda", 7, ["gpu_db_vector_search_batch"], true, "cuda-device-0"),
    true,
    7,
    true,
    gpu_wdb_default_budget(),
    sample_results(),
    mismatched_results(),
    100,
    210,
    64,
    "cuda-event"
)
expect(vector_search_offload_used_gpu(execution.execution)).to_be(false)
expect(execution.execution.cpu_authoritative).to_be(true)
expect(execution.execution.gpu_candidate_validated).to_be(false)
expect(execution.execution.validation_reason).to_equal("production-gpu-vector-mismatch")
expect(execution.execution.submission.dispatch_target).to_equal("cpu_fallback")
expect(execution.execution.results[1].id).to_equal("b")
expect(execution.device_result.production_device_claim).to_be(true)
```

</details>

#### should keep perf-only vector device runs from replacing CPU results

- Require production native vector timing before replacing CPU result IDs
- gpu wdb queue initial
- gpu wdb device backend
- gpu wdb default budget
- sample results
- sample results
   - Expected: execution.execution.validation_reason equals `production-device-not-measured`
   - Expected: execution.execution.results[0].id equals `a`


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Require production native vector timing before replacing CPU result IDs")
val execution = vector_search_offload_execute_device_validated(
    DistanceMetric.Cosine,
    128,
    16,
    true,
    gpu_wdb_queue_initial(2),
    gpu_wdb_device_backend("mock", 7, ["gpu_db_vector_search_batch"], false, "mock-device"),
    true,
    7,
    true,
    gpu_wdb_default_budget(),
    sample_results(),
    sample_results(),
    100,
    210,
    64,
    "mock-clock"
)
expect(vector_search_offload_used_gpu(execution.execution)).to_be(false)
expect(execution.execution.cpu_authoritative).to_be(true)
expect(execution.execution.gpu_candidate_validated).to_be(false)
expect(execution.execution.validation_reason).to_equal("production-device-not-measured")
expect(execution.execution.results[0].id).to_equal("a")
expect(execution.device_result.production_device_claim).to_be(false)
```

</details>

#### should keep vector search on CPU when the registered GPU target is missing

- Avoid fake GPU evidence when registry lacks vector target
- sample results
   - Expected: execution.submission.dispatch_target equals `cpu_fallback`
   - Expected: execution.submission.reason equals `gpu-unavailable`
   - Expected: execution.state_after.queue_depth equals `0`
   - Expected: execution.state_after.cpu_fallback_count equals `1`
   - Expected: execution.results[0].id equals `a`
   - Expected: execution.profile.data_path equals `GpuWdbCoarseDataPath.GpuIndexBatch`


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Avoid fake GPU evidence when registry lacks vector target")
val budget = gpu_wdb_default_budget()
val state = gpu_wdb_queue_initial(2)
val registry = gpu_wdb_library_empty()
val execution = vector_search_offload_execute(
    DistanceMetric.Cosine,
    128,
    16,
    true,
    state,
    registry,
    true,
    true,
    true,
    budget,
    sample_results()
)
expect(vector_search_offload_used_gpu(execution)).to_be(false)
expect(execution.submission.dispatch_target).to_equal("cpu_fallback")
expect(execution.submission.reason).to_equal("gpu-unavailable")
expect(execution.state_after.queue_depth).to_equal(0)
expect(execution.state_after.cpu_fallback_count).to_equal(1)
expect(execution.results[0].id).to_equal("a")
expect(execution.profile.data_path).to_equal(GpuWdbCoarseDataPath.GpuIndexBatch)
expect(vector_search_profile_allows_gpu(execution)).to_be(false)
```

</details>

#### should keep stale vector GPU target generations on CPU

- Require current registry generation before vector GPU evidence
- sample results
   - Expected: execution.plan.batch.execution.decision.path equals `GpuWdbDecisionPath.GpuEvidence`
   - Expected: execution.submission.dispatch_target equals `cpu_fallback`
   - Expected: execution.submission.reason equals `stale-generation`
   - Expected: execution.state_after.cpu_fallback_count equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Require current registry generation before vector GPU evidence")
val budget = gpu_wdb_default_budget()
val state = gpu_wdb_queue_initial(2)
val registry = gpu_wdb_library_with_targets("cuda", 1, ["gpu_db_vector_search_batch"])
val execution = vector_search_offload_execute_for_generation(
    DistanceMetric.Cosine,
    128,
    16,
    true,
    state,
    registry,
    true,
    true,
    2,
    true,
    budget,
    sample_results()
)
expect(vector_search_offload_used_gpu(execution)).to_be(false)
expect(execution.plan.batch.execution.decision.path).to_equal(GpuWdbDecisionPath.GpuEvidence)
expect(execution.submission.dispatch_target).to_equal("cpu_fallback")
expect(execution.submission.reason).to_equal("stale-generation")
expect(execution.state_after.cpu_fallback_count).to_equal(1)
expect(vector_search_profile_allows_gpu(execution)).to_be(false)
```

</details>

#### should reject metadata-filtered vector search when metadata is not CPU-owned

- Keep metadata filtering on CPU-owned control path
- sample results
   - Expected: execution.plan.batch.execution.decision.path equals `GpuWdbDecisionPath.Reject`
   - Expected: execution.plan.batch.execution.decision.reason equals `metadata-filter-must-stay-cpu-owned`
   - Expected: execution.profile.data_path equals `GpuWdbCoarseDataPath.GpuIndexBatch`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Keep metadata filtering on CPU-owned control path")
val budget = gpu_wdb_default_budget()
val state = gpu_wdb_queue_initial(2)
val registry = gpu_wdb_library_with_targets("cuda", 1, ["gpu_db_vector_search_batch"])
val execution = vector_search_offload_execute(
    DistanceMetric.Cosine,
    128,
    16,
    false,
    state,
    registry,
    true,
    true,
    true,
    budget,
    sample_results()
)
expect(vector_search_offload_used_gpu(execution)).to_be(false)
expect(execution.plan.batch.execution.decision.path).to_equal(GpuWdbDecisionPath.Reject)
expect(execution.plan.batch.execution.decision.reason).to_equal("metadata-filter-must-stay-cpu-owned")
expect(execution.profile.data_path).to_equal(GpuWdbCoarseDataPath.GpuIndexBatch)
expect(vector_search_profile_allows_gpu(execution)).to_be(false)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** [doc/02_requirements/feature/gpu_web_db_offload.md](doc/02_requirements/feature/gpu_web_db_offload.md)
- **Plan:** [doc/03_plan/agent_tasks/gpu_web_db_offload_impl_status.md](doc/03_plan/agent_tasks/gpu_web_db_offload_impl_status.md)
- **Design:** [doc/05_design/gpu_web_db_offload.md](doc/05_design/gpu_web_db_offload.md)


</details>
