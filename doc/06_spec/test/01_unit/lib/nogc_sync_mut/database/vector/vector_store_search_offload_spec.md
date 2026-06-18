# Vector Store Search Offload

> These scenarios prove the vector store remains CPU-authoritative by default while exposing opt-in GPU queue accounting for coarse vector search batches.

<!-- sdn-diagram:id=vector_store_search_offload_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=vector_store_search_offload_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

vector_store_search_offload_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=vector_store_search_offload_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Vector Store Search Offload

These scenarios prove the vector store remains CPU-authoritative by default while exposing opt-in GPU queue accounting for coarse vector search batches.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Requirements | doc/02_requirements/feature/gpu_web_db_offload.md |
| Plan | doc/03_plan/agent_tasks/gpu_web_db_offload_impl_status.md |
| Design | doc/05_design/gpu_web_db_offload.md |
| Research | N/A |
| Source | `test/01_unit/lib/nogc_sync_mut/database/vector/vector_store_search_offload_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

These scenarios prove the vector store remains CPU-authoritative by default
while exposing opt-in GPU queue accounting for coarse vector search batches.

## Requirements

**Requirements:** doc/02_requirements/feature/gpu_web_db_offload.md

- Vector store search remains CPU-authoritative by default.
- Coarse vector search batches can report registered GPU dispatch evidence.
- Small background vector searches can defer into the shared accumulator.
- Metadata filtering remains CPU-owned before offload accounting.

## Plan

**Plan:** doc/03_plan/agent_tasks/gpu_web_db_offload_impl_status.md

## Design

**Design:** doc/05_design/gpu_web_db_offload.md

## Research

**Research:** N/A

## Examples

Call `search_with_offload_accumulating` after normal CPU vector search. The
returned results remain the CPU-authoritative nearest neighbors while the
offload record can defer small batches into `GpuWdbWorkKind.DbVectorSearch`.

## Scenarios

### vector store search offload

#### should preserve normal CPU search as the default behavior

- Run ordinary search without any GPU queue or registry config
   - Expected: results.len() equals `2`
   - Expected: results[0].id equals `a`
   - Expected: results[1].id equals `c`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Run ordinary search without any GPU queue or registry config")
val db = sample_store("/tmp/simple_vector_store_default")
val results = db.search([0.0, 0.0], 2).unwrap()
expect(results.len()).to_equal(2)
expect(results[0].id).to_equal("a")
expect(results[1].id).to_equal("c")
```

</details>

#### should return CPU-authoritative results when GPU target is missing

- Opt into offload accounting with an empty target registry
- gpu wdb queue initial
- gpu wdb library empty
- offload test budget
   - Expected: execution.results.len() equals `cpu.len()`
   - Expected: execution.results[0].id equals `cpu[0].id`
   - Expected: execution.submission.dispatch_target equals `cpu_fallback`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Opt into offload accounting with an empty target registry")
val db = sample_store("/tmp/simple_vector_store_missing_gpu")
val cpu = db.search([0.0, 0.0], 2).unwrap()
val execution = db.search_with_offload(
    [0.0, 0.0],
    2,
    gpu_wdb_queue_initial(2),
    gpu_wdb_library_empty(),
    true,
    true,
    true,
    offload_test_budget()
).unwrap()
expect(vector_search_offload_used_gpu(execution)).to_be(false)
expect(execution.results.len()).to_equal(cpu.len())
expect(execution.results[0].id).to_equal(cpu[0].id)
expect(execution.submission.dispatch_target).to_equal("cpu_fallback")
expect(execution.cpu_authoritative).to_be(true)
```

</details>

#### should record GPU dispatch for coarse registered vector search

- Opt into a registered vector GPU target while preserving CPU results
- gpu wdb queue initial
- offload test budget
   - Expected: execution.submission.dispatch_target equals `gpu_db_vector_search_batch`
   - Expected: execution.results[0].id equals `a`
   - Expected: execution.results[1].id equals `c`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Opt into a registered vector GPU target while preserving CPU results")
val db = sample_store("/tmp/simple_vector_store_registered_gpu")
val registry = gpu_wdb_library_with_targets("cuda", 1, ["gpu_db_vector_search_batch"])
val execution = db.search_with_offload(
    [0.0, 0.0],
    2,
    gpu_wdb_queue_initial(2),
    registry,
    true,
    true,
    true,
    offload_test_budget()
).unwrap()
expect(vector_search_profile_allows_gpu(execution)).to_be(true)
expect(vector_search_offload_used_gpu(execution)).to_be(true)
expect(execution.submission.dispatch_target).to_equal("gpu_db_vector_search_batch")
expect(execution.results[0].id).to_equal("a")
expect(execution.results[1].id).to_equal("c")
expect(execution.cpu_authoritative).to_be(true)
```

</details>

#### should replace vector store search results after native candidates match

- Validate native vector candidates against live vector store CPU search
- gpu wdb queue initial
- gpu wdb device backend
- offload test budget
   - Expected: execution.execution.validation_reason equals `production-gpu-vector-match`
   - Expected: execution.execution.results[0].id equals `a`
   - Expected: execution.execution.results[1].id equals `c`


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Validate native vector candidates against live vector store CPU search")
val db = sample_store("/tmp/simple_vector_store_native_vector_match")
val cpu = db.search([0.0, 0.0], 2).unwrap()
val execution = db.search_with_device_backend_validated(
    [0.0, 0.0],
    2,
    gpu_wdb_queue_initial(2),
    gpu_wdb_device_backend("cuda", 9, ["gpu_db_vector_search_batch"], true, "cuda-device-0"),
    true,
    9,
    true,
    offload_test_budget(),
    cpu,
    100,
    220,
    71,
    "cuda-event"
).unwrap()
expect(vector_search_offload_used_gpu(execution.execution)).to_be(true)
expect(execution.execution.cpu_authoritative).to_be(false)
expect(execution.execution.gpu_candidate_validated).to_be(true)
expect(execution.execution.validation_reason).to_equal("production-gpu-vector-match")
expect(execution.execution.results[0].id).to_equal("a")
expect(execution.execution.results[1].id).to_equal("c")
expect(execution.device_result.production_device_claim).to_be(true)
```

</details>

#### should expose query-level device validation for vector store search

- Reuse the DB query offload facade from the vector store boundary
- gpu wdb queue initial
- gpu wdb device backend
- offload test budget
   - Expected: execution.results[0].id equals `a`
   - Expected: execution.results[1].id equals `c`
   - Expected: query_execution.execution.workload equals `DbStorageOffloadWorkload.VectorSearch`
   - Expected: query_execution.execution.validation_reason equals `production-gpu-vector-match`
   - Expected: query_execution.execution.vector_ids[0] equals `a`
   - Expected: query_execution.execution.vector_ids[1] equals `c`
- db query vector
- gpu wdb queue initial
- gpu wdb device backend
- offload test budget
   - Expected: direct_query_execution.execution.validation_reason equals `production-gpu-vector-match`


<details>
<summary>Executable SSpec</summary>

Runnable source: 43 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Reuse the DB query offload facade from the vector store boundary")
val db = sample_store("/tmp/simple_vector_store_query_native_match")
val cpu = db.search([0.0, 0.0], 2).unwrap()
val execution = db.search_with_query_device_backend_validated(
    [0.0, 0.0],
    2,
    gpu_wdb_queue_initial(2),
    gpu_wdb_device_backend("cuda", 10, ["gpu_db_vector_search_batch"], true, "cuda-device-0"),
    true,
    10,
    true,
    offload_test_budget(),
    cpu,
    120,
    260,
    82,
    "cuda-event"
).unwrap()
val query_execution: DbStorageVectorDeviceOffloadExecution = execution.query_execution
expect(execution.results[0].id).to_equal("a")
expect(execution.results[1].id).to_equal("c")
expect(query_execution.execution.workload).to_equal(DbStorageOffloadWorkload.VectorSearch)
expect(query_execution.execution.cpu_authoritative).to_be(false)
expect(query_execution.execution.gpu_candidate_validated).to_be(true)
expect(query_execution.execution.validation_reason).to_equal("production-gpu-vector-match")
expect(query_execution.execution.vector_ids[0]).to_equal("a")
expect(query_execution.execution.vector_ids[1]).to_equal("c")
expect(query_execution.device_result.production_device_claim).to_be(true)
val direct_query_execution: DbStorageVectorDeviceOffloadExecution = db_query_offload_execute_vector_device_validated(
    db_query_vector(DistanceMetric.Euclidean, 3, 2, true, true, cpu),
    gpu_wdb_queue_initial(2),
    gpu_wdb_device_backend("cuda", 10, ["gpu_db_vector_search_batch"], true, "cuda-device-0"),
    10,
    true,
    offload_test_budget(),
    cpu,
    120,
    260,
    82,
    "cuda-event"
)
expect(direct_query_execution.execution.gpu_candidate_validated).to_be(true)
expect(direct_query_execution.execution.validation_reason).to_equal("production-gpu-vector-match")
```

</details>

#### should keep query-level vector store results CPU-authoritative on GPU mismatch

- Reject mismatched native vector candidates at the query facade boundary
- gpu wdb queue initial
- gpu wdb device backend
- offload test budget
   - Expected: execution.results[0].id equals `cpu[0].id`
   - Expected: execution.results[1].id equals `cpu[1].id`
   - Expected: query_execution.execution.validation_reason equals `production-gpu-vector-mismatch`
   - Expected: query_execution.execution.vector_ids[0] equals `cpu[0].id`
   - Expected: query_execution.execution.vector_ids[1] equals `cpu[1].id`


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Reject mismatched native vector candidates at the query facade boundary")
val db = sample_store("/tmp/simple_vector_store_query_native_mismatch")
val cpu = db.search([0.0, 0.0], 2).unwrap()
val gpu_candidate = db.search([10.0, 0.0], 2).unwrap()
val execution = db.search_with_query_device_backend_validated(
    [0.0, 0.0],
    2,
    gpu_wdb_queue_initial(2),
    gpu_wdb_device_backend("cuda", 10, ["gpu_db_vector_search_batch"], true, "cuda-device-0"),
    true,
    10,
    true,
    offload_test_budget(),
    gpu_candidate,
    120,
    260,
    82,
    "cuda-event"
).unwrap()
val query_execution: DbStorageVectorDeviceOffloadExecution = execution.query_execution
expect(execution.results[0].id).to_equal(cpu[0].id)
expect(execution.results[1].id).to_equal(cpu[1].id)
expect(query_execution.execution.cpu_authoritative).to_be(true)
expect(query_execution.execution.gpu_candidate_validated).to_be(false)
expect(query_execution.execution.validation_reason).to_equal("production-gpu-vector-mismatch")
expect(query_execution.execution.vector_ids[0]).to_equal(cpu[0].id)
expect(query_execution.execution.vector_ids[1]).to_equal(cpu[1].id)
```

</details>

#### should keep metadata filtering CPU-owned in offload-aware search

- Apply metadata filtering before returning CPU-authoritative results
- gpu wdb queue initial
- offload test budget
   - Expected: execution.results.len() equals `2`
   - Expected: execution.results[0].metadata.get("tenant") equals `t1`
   - Expected: execution.results[1].metadata.get("tenant") equals `t1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Apply metadata filtering before returning CPU-authoritative results")
val db = sample_store("/tmp/simple_vector_store_filter_gpu")
val registry = gpu_wdb_library_with_targets("cuda", 1, ["gpu_db_vector_search_batch"])
val execution = db.search_with_filter_offload(
    [0.0, 0.0],
    2,
    {"tenant": "t1"},
    gpu_wdb_queue_initial(2),
    registry,
    true,
    true,
    true,
    offload_test_budget()
).unwrap()
expect(execution.results.len()).to_equal(2)
expect(execution.results[0].metadata.get("tenant")).to_equal("t1")
expect(execution.results[1].metadata.get("tenant")).to_equal("t1")
expect(execution.cpu_authoritative).to_be(true)
```

</details>

#### should accumulate small vector searches through the vector store

- Defer tiny background vector search batches into the shared accumulator
- gpu wdb queue initial
- gpu wdb batch accumulator
   - Expected: execution.results[0].id equals `a`
   - Expected: execution.results[1].id equals `c`
   - Expected: execution.accumulated.execution.workload equals `DbStorageOffloadWorkload.VectorSearch`
   - Expected: execution.accumulated.execution.dispatch_target equals `gpu_batch_accumulator`
   - Expected: execution.accumulated.accumulator_result.accumulator.item_count equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Defer tiny background vector search batches into the shared accumulator")
val db = sample_store("/tmp/simple_vector_store_accumulate")
val registry = gpu_wdb_library_with_targets("cuda", 1, ["gpu_db_vector_search_batch"])
val execution = db.search_with_offload_accumulating(
    [0.0, 0.0],
    2,
    gpu_wdb_queue_initial(2),
    registry,
    true,
    true,
    true,
    GpuWdbBudget(
        max_queue_depth: 64,
        max_batch_bytes: 1024,
        min_gpu_batch_bytes: 1024
    ),
    GpuWdbScheduleClass.Background,
    gpu_wdb_batch_accumulator(GpuWdbWorkKind.DbVectorSearch)
).unwrap()
expect(execution.results[0].id).to_equal("a")
expect(execution.results[1].id).to_equal("c")
expect(execution.accumulated.execution.workload).to_equal(DbStorageOffloadWorkload.VectorSearch)
expect(execution.accumulated.execution.dispatch_target).to_equal("gpu_batch_accumulator")
expect(execution.accumulated.accumulator_result.accepted).to_be(true)
expect(execution.accumulated.accumulator_result.accumulator.item_count).to_equal(3)
```

</details>

#### should keep filtered vector accumulation CPU-owned

- Apply metadata filters before accumulating vector offload evidence
- gpu wdb queue initial
- gpu wdb batch accumulator
   - Expected: execution.results.len() equals `2`
   - Expected: execution.results[0].metadata.get("tenant") equals `t1`
   - Expected: execution.results[1].metadata.get("tenant") equals `t1`
   - Expected: execution.accumulated.execution.vector_ids[0] equals `a`
   - Expected: execution.accumulated.execution.vector_ids[1] equals `c`


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Apply metadata filters before accumulating vector offload evidence")
val db = sample_store("/tmp/simple_vector_store_filter_accumulate")
val registry = gpu_wdb_library_with_targets("cuda", 1, ["gpu_db_vector_search_batch"])
val execution = db.search_with_filter_offload_accumulating(
    [0.0, 0.0],
    2,
    {"tenant": "t1"},
    gpu_wdb_queue_initial(2),
    registry,
    true,
    true,
    true,
    GpuWdbBudget(
        max_queue_depth: 64,
        max_batch_bytes: 1024,
        min_gpu_batch_bytes: 1024
    ),
    GpuWdbScheduleClass.Background,
    gpu_wdb_batch_accumulator(GpuWdbWorkKind.DbVectorSearch)
).unwrap()
expect(execution.results.len()).to_equal(2)
expect(execution.results[0].metadata.get("tenant")).to_equal("t1")
expect(execution.results[1].metadata.get("tenant")).to_equal("t1")
expect(execution.accumulated.execution.vector_ids[0]).to_equal("a")
expect(execution.accumulated.execution.vector_ids[1]).to_equal("c")
expect(execution.accumulated.accumulator_result.accepted).to_be(true)
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
