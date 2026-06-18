# RAM and SSD DB GPU Batch Offload

> These scenarios verify the reusable coarse DB batch adapter for RAM-only and SSD-accelerated database modes. The adapter is an offload boundary, not a GPU query engine: CPU row IDs remain authoritative, and GPU dispatch is only reported when the required GPU library target is registered.

<!-- sdn-diagram:id=db_gpu_batch_offload_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=db_gpu_batch_offload_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

db_gpu_batch_offload_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=db_gpu_batch_offload_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# RAM and SSD DB GPU Batch Offload

These scenarios verify the reusable coarse DB batch adapter for RAM-only and SSD-accelerated database modes. The adapter is an offload boundary, not a GPU query engine: CPU row IDs remain authoritative, and GPU dispatch is only reported when the required GPU library target is registered.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Requirements | doc/02_requirements/feature/gpu_web_db_offload.md |
| Plan | doc/03_plan/agent_tasks/gpu_web_db_offload_impl_status.md |
| Design | doc/05_design/gpu_web_db_offload.md |
| Research | N/A |
| Source | `test/01_unit/lib/nogc_sync_mut/database/db_gpu_batch_offload_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

These scenarios verify the reusable coarse DB batch adapter for RAM-only and
SSD-accelerated database modes. The adapter is an offload boundary, not a GPU
query engine: CPU row IDs remain authoritative, and GPU dispatch is only
reported when the required GPU library target is registered.

## Requirements

**Requirements:** doc/02_requirements/feature/gpu_web_db_offload.md

- RAM scan/filter/project batches may use `gpu_db_columnar_scan_batch`.
- Join/aggregate batches may use `gpu_db_join_aggregate_batch`.
- Missing GPU library targets must fall back to CPU instead of reporting fake
  GPU evidence.
- SSD accelerated batches require current WAL generation evidence.

## Plan

**Plan:** doc/03_plan/agent_tasks/gpu_web_db_offload_impl_status.md

## Design

**Design:** doc/05_design/gpu_web_db_offload.md

The adapter reuses `std.web_db_offload.queue` and
`std.web_db_offload.library` so RAM, SSD, NoSQL, vector, and web route offload
share the same queue accounting and target registry.

## Research

**Research:** N/A

## Examples

Register `gpu_db_columnar_scan_batch` for coarse RAM scan/filter/project work.
Register `gpu_db_join_aggregate_batch` for aggregate batches. Leave the target
unregistered to force CPU fallback while preserving authoritative CPU results.

## Scenarios

### DB GPU batch offload adapter

#### should map scan and aggregate batch kinds to reusable GPU work kinds

- Map public batch kinds to shared web/db offload work kinds
   - Expected: db_gpu_batch_work_kind(DbGpuBatchKind.ScanFilterProject) equals `GpuWdbWorkKind.DbScanFilterProject`
   - Expected: db_gpu_batch_work_kind(DbGpuBatchKind.JoinAggregate) equals `GpuWdbWorkKind.DbJoinAggregate`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Map public batch kinds to shared web/db offload work kinds")
expect(db_gpu_batch_work_kind(DbGpuBatchKind.ScanFilterProject)).to_equal(GpuWdbWorkKind.DbScanFilterProject)
expect(db_gpu_batch_work_kind(DbGpuBatchKind.JoinAggregate)).to_equal(GpuWdbWorkKind.DbJoinAggregate)
```

</details>

#### should dispatch RAM scan batches when the columnar target is registered

- Submit a RAM-only scan/filter/project batch through the shared queue
- gpu wdb queue initial
- db batch budget
   - Expected: execution.submission.dispatch_target equals `gpu_db_columnar_scan_batch`
   - Expected: execution.state_after.completed_count equals `1`
   - Expected: execution.result_row_ids.len() equals `3`
   - Expected: execution.plan.profile.data_path equals `GpuWdbCoarseDataPath.GpuResidentBatch`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Submit a RAM-only scan/filter/project batch through the shared queue")
val registry = gpu_wdb_library_with_targets("cuda", 1, ["gpu_db_columnar_scan_batch"])
val execution = db_gpu_batch_offload_execute(
    DbGpuMode.RamOnly,
    DbGpuBatchKind.ScanFilterProject,
    128,
    64,
    gpu_wdb_queue_initial(4),
    registry,
    true,
    true,
    true,
    db_batch_budget(),
    [1, 2, 3]
)
expect(db_gpu_batch_offload_used_gpu(execution)).to_be(true)
expect(execution.submission.dispatch_target).to_equal("gpu_db_columnar_scan_batch")
expect(execution.state_after.completed_count).to_equal(1)
expect(execution.result_row_ids.len()).to_equal(3)
expect(execution.cpu_authoritative).to_be(true)
expect(execution.plan.profile.data_path).to_equal(GpuWdbCoarseDataPath.GpuResidentBatch)
expect(db_gpu_batch_profile_allows_gpu(execution)).to_be(true)
```

</details>

#### should attach native device evidence to RAM scan batches

- Run the RAM scan/filter/project adapter through a strict native device backend
- gpu wdb queue initial
- db batch budget
   - Expected: execution.execution.result_row_ids.len() equals `3`
   - Expected: execution.device_result.submission.dispatch_target equals `gpu_db_columnar_scan_batch`
   - Expected: execution.device_result.evidence.device_time_us equals `43`


<details>
<summary>Executable SSpec</summary>

Runnable source: 31 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Run the RAM scan/filter/project adapter through a strict native device backend")
val backend = gpu_wdb_device_backend(
    "cuda",
    2,
    ["gpu_db_columnar_scan_batch"],
    true,
    "cuda-device-0"
)
val execution = db_gpu_batch_offload_execute_device_for_generation(
    DbGpuMode.RamOnly,
    DbGpuBatchKind.ScanFilterProject,
    128,
    64,
    gpu_wdb_queue_initial(4),
    backend,
    true,
    2,
    true,
    db_batch_budget(),
    [1, 2, 3],
    100,
    180,
    43,
    "cuda-event"
)
expect(db_gpu_batch_offload_used_gpu(execution.execution)).to_be(true)
expect(execution.execution.result_row_ids.len()).to_equal(3)
expect(execution.execution.cpu_authoritative).to_be(true)
expect(execution.device_result.production_device_claim).to_be(true)
expect(execution.device_result.submission.dispatch_target).to_equal("gpu_db_columnar_scan_batch")
expect(execution.device_result.evidence.device_time_us).to_equal(43)
```

</details>

#### should block DB batch production claims for perf-only backends

- Keep DB batch device evidence strict when the backend cannot execute native kernels
- gpu wdb queue initial
- db batch budget
   - Expected: execution.execution.result_row_ids[0] equals `4`
   - Expected: execution.device_result.submission.dispatch_target equals `cpu_fallback`
   - Expected: execution.device_result.reason equals `gpu-unavailable`


<details>
<summary>Executable SSpec</summary>

Runnable source: 31 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Keep DB batch device evidence strict when the backend cannot execute native kernels")
val backend = gpu_wdb_device_backend(
    "host-safe-mock",
    2,
    ["gpu_db_columnar_scan_batch"],
    false,
    "mock-device"
)
val execution = db_gpu_batch_offload_execute_device_for_generation(
    DbGpuMode.RamOnly,
    DbGpuBatchKind.ScanFilterProject,
    128,
    64,
    gpu_wdb_queue_initial(4),
    backend,
    true,
    2,
    true,
    db_batch_budget(),
    [4],
    100,
    180,
    43,
    "mock-timer"
)
expect(db_gpu_batch_offload_used_gpu(execution.execution)).to_be(false)
expect(execution.execution.result_row_ids[0]).to_equal(4)
expect(execution.execution.cpu_authoritative).to_be(true)
expect(execution.device_result.production_device_claim).to_be(false)
expect(execution.device_result.submission.dispatch_target).to_equal("cpu_fallback")
expect(execution.device_result.reason).to_equal("gpu-unavailable")
```

</details>

#### should dispatch join aggregate batches through the aggregate target

- Use the join/aggregate GPU target instead of the scan target
- gpu wdb queue initial
- db batch budget
   - Expected: execution.submission.execution.kind equals `GpuWdbWorkKind.DbJoinAggregate`
   - Expected: execution.submission.dispatch_target equals `gpu_db_join_aggregate_batch`
   - Expected: execution.result_row_ids[0] equals `7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Use the join/aggregate GPU target instead of the scan target")
val registry = gpu_wdb_library_with_targets("cuda", 1, ["gpu_db_join_aggregate_batch"])
val execution = db_gpu_batch_offload_execute(
    DbGpuMode.RamOnly,
    DbGpuBatchKind.JoinAggregate,
    256,
    64,
    gpu_wdb_queue_initial(2),
    registry,
    true,
    true,
    true,
    db_batch_budget(),
    [7]
)
expect(db_gpu_batch_offload_used_gpu(execution)).to_be(true)
expect(execution.submission.execution.kind).to_equal(GpuWdbWorkKind.DbJoinAggregate)
expect(execution.submission.dispatch_target).to_equal("gpu_db_join_aggregate_batch")
expect(execution.result_row_ids[0]).to_equal(7)
```

</details>

#### should fall back when a registered RAM target is missing

- Avoid fake GPU evidence without the matching registered target
- gpu wdb queue initial
- gpu wdb library empty
- db batch budget
   - Expected: execution.submission.dispatch_target equals `cpu_fallback`
   - Expected: execution.submission.reason equals `gpu-unavailable`
   - Expected: execution.state_after.cpu_fallback_count equals `1`
   - Expected: execution.plan.profile.data_path equals `GpuWdbCoarseDataPath.GpuResidentBatch`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Avoid fake GPU evidence without the matching registered target")
val execution = db_gpu_batch_offload_execute(
    DbGpuMode.RamOnly,
    DbGpuBatchKind.ScanFilterProject,
    128,
    64,
    gpu_wdb_queue_initial(4),
    gpu_wdb_library_empty(),
    true,
    true,
    true,
    db_batch_budget(),
    [1]
)
expect(db_gpu_batch_offload_used_gpu(execution)).to_be(false)
expect(execution.submission.dispatch_target).to_equal("cpu_fallback")
expect(execution.submission.reason).to_equal("gpu-unavailable")
expect(execution.state_after.cpu_fallback_count).to_equal(1)
expect(execution.plan.profile.data_path).to_equal(GpuWdbCoarseDataPath.GpuResidentBatch)
expect(db_gpu_batch_profile_allows_gpu(execution)).to_be(false)
```

</details>

#### should keep SSD batches on CPU when WAL generation is stale

- Require current WAL generation before SSD GPU dispatch
- gpu wdb queue initial
- db batch budget
   - Expected: execution.plan.batch.execution.decision.path equals `GpuWdbDecisionPath.CpuFallback`
   - Expected: execution.submission.reason equals `stale-generation`
   - Expected: execution.state_after.cpu_fallback_count equals `1`
   - Expected: execution.plan.profile.data_path equals `GpuWdbCoarseDataPath.SsdStagedBatch`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Require current WAL generation before SSD GPU dispatch")
val registry = gpu_wdb_library_with_targets("cuda", 1, ["gpu_db_columnar_scan_batch"])
val execution = db_gpu_batch_offload_execute(
    DbGpuMode.SsdAccelerated,
    DbGpuBatchKind.ScanFilterProject,
    128,
    64,
    gpu_wdb_queue_initial(4),
    registry,
    true,
    false,
    true,
    db_batch_budget(),
    [5]
)
expect(db_gpu_batch_offload_used_gpu(execution)).to_be(false)
expect(execution.plan.batch.execution.decision.path).to_equal(GpuWdbDecisionPath.CpuFallback)
expect(execution.submission.reason).to_equal("stale-generation")
expect(execution.state_after.cpu_fallback_count).to_equal(1)
expect(execution.plan.profile.data_path).to_equal(GpuWdbCoarseDataPath.SsdStagedBatch)
expect(db_gpu_batch_profile_allows_gpu(execution)).to_be(false)
```

</details>

#### should keep DB batches on CPU when registry generation is stale

- Require current GPU target generation separately from WAL freshness
- gpu wdb queue initial
- db batch budget
   - Expected: execution.plan.batch.execution.decision.path equals `GpuWdbDecisionPath.GpuEvidence`
   - Expected: execution.submission.reason equals `stale-generation`
   - Expected: execution.submission.dispatch_target equals `cpu_fallback`
   - Expected: execution.state_after.cpu_fallback_count equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Require current GPU target generation separately from WAL freshness")
val registry = gpu_wdb_library_with_targets("cuda", 1, ["gpu_db_columnar_scan_batch"])
val execution = db_gpu_batch_offload_execute_for_generation(
    DbGpuMode.RamOnly,
    DbGpuBatchKind.ScanFilterProject,
    128,
    64,
    gpu_wdb_queue_initial(4),
    registry,
    true,
    true,
    2,
    true,
    db_batch_budget(),
    [5]
)
expect(db_gpu_batch_offload_used_gpu(execution)).to_be(false)
expect(execution.plan.batch.execution.decision.path).to_equal(GpuWdbDecisionPath.GpuEvidence)
expect(execution.submission.reason).to_equal("stale-generation")
expect(execution.submission.dispatch_target).to_equal("cpu_fallback")
expect(execution.state_after.cpu_fallback_count).to_equal(1)
expect(db_gpu_batch_profile_allows_gpu(execution)).to_be(false)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** [doc/02_requirements/feature/gpu_web_db_offload.md](doc/02_requirements/feature/gpu_web_db_offload.md)
- **Plan:** [doc/03_plan/agent_tasks/gpu_web_db_offload_impl_status.md](doc/03_plan/agent_tasks/gpu_web_db_offload_impl_status.md)
- **Design:** [doc/05_design/gpu_web_db_offload.md](doc/05_design/gpu_web_db_offload.md)


</details>
