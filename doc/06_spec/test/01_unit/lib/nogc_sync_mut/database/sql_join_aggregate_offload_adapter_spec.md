# SQL Join/Aggregate GPU Offload Adapter

> These scenarios verify the reusable SQL join/aggregate adapter. SQL rows remain CPU-authoritative; GPU dispatch is only reusable execution metadata until a validated SQL GPU kernel can replace the CPU operator.

<!-- sdn-diagram:id=sql_join_aggregate_offload_adapter_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=sql_join_aggregate_offload_adapter_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

sql_join_aggregate_offload_adapter_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=sql_join_aggregate_offload_adapter_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# SQL Join/Aggregate GPU Offload Adapter

These scenarios verify the reusable SQL join/aggregate adapter. SQL rows remain CPU-authoritative; GPU dispatch is only reusable execution metadata until a validated SQL GPU kernel can replace the CPU operator.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Requirements | doc/02_requirements/feature/gpu_web_db_offload.md |
| Plan | doc/03_plan/agent_tasks/gpu_web_db_offload_impl_status.md |
| Design | doc/05_design/gpu_web_db_offload.md |
| Research | N/A |
| Source | `test/01_unit/lib/nogc_sync_mut/database/sql_join_aggregate_offload_adapter_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

These scenarios verify the reusable SQL join/aggregate adapter. SQL rows remain
CPU-authoritative; GPU dispatch is only reusable execution metadata until a
validated SQL GPU kernel can replace the CPU operator.

## Requirements

**Requirements:** doc/02_requirements/feature/gpu_web_db_offload.md

- SQL join and aggregate callers can use one reusable offload adapter.
- Adapter dispatch metadata may use GPU targets for coarse work.
- Returned SQL rows remain CPU-authoritative until GPU kernels are validated.
- GPU candidate rows must match CPU rows before GPU dispatch evidence is
  accepted.
- No-hardware and stale-WAL cases must fall back without changing rows.

## Plan

**Plan:** doc/03_plan/agent_tasks/gpu_web_db_offload_impl_status.md

## Design

**Design:** doc/05_design/gpu_web_db_offload.md

## Research

**Research:** N/A

## Examples

Build CPU SQL result rows, pass them with CPU row IDs into
`sql_join_aggregate_offload_execute`, then inspect the offload record. The rows
returned by the adapter are the same CPU rows.

## Scenarios

### SQL join aggregate offload adapter

#### should dispatch registered join aggregate batches while preserving CPU rows

- Submit a coarse SQL aggregate through the shared DB query queue
- adapter rows
- gpu wdb queue initial
- gpu wdb library with targets
- adapter budget
   - Expected: execution.offload.dispatch_target equals `gpu_db_join_aggregate_batch`
   - Expected: execution.offload.validation_reason equals `gpu-candidate-not-evaluated`
   - Expected: execution.offload.profile.data_path equals `GpuWdbCoarseDataPath.GpuResidentBatch`
   - Expected: execution.rows.len() equals `2`
   - Expected: execution.rows[0].values[0].to_text() equals `Alice`
   - Expected: execution.offload.row_ids.len() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Submit a coarse SQL aggregate through the shared DB query queue")
val execution = sql_join_aggregate_offload_execute(
    adapter_rows(),
    [0, 1, 2],
    DbStorageOffloadMode.RamOnly,
    gpu_wdb_queue_initial(2),
    gpu_wdb_library_with_targets("cuda", 1, ["gpu_db_join_aggregate_batch"]),
    true,
    true,
    true,
    adapter_budget(),
    512
)
expect(sql_join_aggregate_offload_used_gpu(execution)).to_be(true)
expect(execution.offload.dispatch_target).to_equal("gpu_db_join_aggregate_batch")
expect(execution.cpu_authoritative).to_be(true)
expect(execution.offload.cpu_authoritative).to_be(true)
expect(execution.offload.gpu_candidate_validated).to_be(false)
expect(execution.offload.validation_reason).to_equal("gpu-candidate-not-evaluated")
expect(execution.offload.profile.data_path).to_equal(GpuWdbCoarseDataPath.GpuResidentBatch)
expect(execution.rows.len()).to_equal(2)
expect(execution.rows[0].values[0].to_text()).to_equal("Alice")
expect(execution.offload.row_ids.len()).to_equal(3)
```

</details>

#### should keep rows on CPU when GPU is unavailable

- Avoid fake GPU evidence for no-hardware execution
- adapter rows
- gpu wdb queue initial
- gpu wdb library with targets
- adapter budget
   - Expected: execution.offload.dispatch_target equals `cpu_fallback`
   - Expected: execution.offload.reason equals `gpu-unavailable`
   - Expected: execution.offload.validation_reason equals `gpu-candidate-not-evaluated`
   - Expected: execution.rows[1].values[0].to_text() equals `Bob`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Avoid fake GPU evidence for no-hardware execution")
val execution = sql_join_aggregate_offload_execute(
    adapter_rows(),
    [0, 1, 2],
    DbStorageOffloadMode.RamOnly,
    gpu_wdb_queue_initial(2),
    gpu_wdb_library_with_targets("cuda", 1, ["gpu_db_join_aggregate_batch"]),
    false,
    true,
    true,
    adapter_budget(),
    512
)
expect(sql_join_aggregate_offload_used_gpu(execution)).to_be(false)
expect(execution.offload.dispatch_target).to_equal("cpu_fallback")
expect(execution.offload.reason).to_equal("gpu-unavailable")
expect(execution.cpu_authoritative).to_be(true)
expect(execution.offload.gpu_candidate_validated).to_be(false)
expect(execution.offload.validation_reason).to_equal("gpu-candidate-not-evaluated")
expect(execution.rows[1].values[0].to_text()).to_equal("Bob")
```

</details>

#### should keep stale WAL aggregate work on CPU

- Preserve WAL freshness before SQL aggregate GPU dispatch
- adapter rows
- gpu wdb queue initial
- gpu wdb library with targets
- adapter budget
   - Expected: execution.offload.dispatch_target equals `cpu_fallback`
   - Expected: execution.offload.reason equals `stale-generation`
   - Expected: execution.offload.profile.data_path equals `GpuWdbCoarseDataPath.SsdStagedBatch`
   - Expected: execution.rows.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Preserve WAL freshness before SQL aggregate GPU dispatch")
val execution = sql_join_aggregate_offload_execute(
    adapter_rows(),
    [0, 1, 2],
    DbStorageOffloadMode.SsdAccelerated,
    gpu_wdb_queue_initial(2),
    gpu_wdb_library_with_targets("cuda", 1, ["gpu_db_join_aggregate_batch"]),
    true,
    false,
    true,
    adapter_budget(),
    512
)
expect(sql_join_aggregate_offload_used_gpu(execution)).to_be(false)
expect(execution.offload.dispatch_target).to_equal("cpu_fallback")
expect(execution.offload.reason).to_equal("stale-generation")
expect(execution.cpu_authoritative).to_be(true)
expect(execution.offload.profile.data_path).to_equal(GpuWdbCoarseDataPath.SsdStagedBatch)
expect(execution.rows.len()).to_equal(2)
```

</details>

#### should accept GPU candidate rows only when they match CPU rows

- Validate GPU SQL aggregate candidates against the CPU oracle
- adapter rows
- adapter rows
- gpu wdb queue initial
- gpu wdb library with targets
- adapter budget
   - Expected: execution.validation_reason equals `gpu-cpu-row-match`
   - Expected: execution.offload.validation_reason equals `gpu-cpu-row-match`
   - Expected: execution.offload.profile.data_path equals `GpuWdbCoarseDataPath.GpuResidentBatch`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Validate GPU SQL aggregate candidates against the CPU oracle")
val execution = sql_join_aggregate_offload_execute_validated(
    adapter_rows(),
    adapter_rows(),
    [0, 1, 2],
    DbStorageOffloadMode.RamOnly,
    gpu_wdb_queue_initial(2),
    gpu_wdb_library_with_targets("cuda", 1, ["gpu_db_join_aggregate_batch"]),
    true,
    true,
    true,
    adapter_budget(),
    512
)
expect(sql_join_aggregate_result_rows_equal(execution.rows, adapter_rows())).to_be(true)
expect(sql_join_aggregate_offload_used_gpu(execution)).to_be(true)
expect(execution.gpu_candidate_validated).to_be(true)
expect(execution.validation_reason).to_equal("gpu-cpu-row-match")
expect(execution.offload.gpu_candidate_validated).to_be(true)
expect(execution.offload.validation_reason).to_equal("gpu-cpu-row-match")
expect(execution.offload.profile.data_path).to_equal(GpuWdbCoarseDataPath.GpuResidentBatch)
```

</details>

#### should fall back to CPU when GPU candidate rows differ

- Reject mismatched GPU SQL aggregate candidates before accepting GPU evidence
- DbRow
- DbRow
- adapter rows
- gpu wdb queue initial
- gpu wdb library with targets
- gpu wdb default budget
   - Expected: execution.offload.dispatch_target equals `cpu_fallback`
   - Expected: execution.offload.reason equals `gpu-cpu-row-mismatch`
   - Expected: execution.offload.validation_reason equals `gpu-cpu-row-mismatch`
   - Expected: execution.offload.profile.data_path equals `GpuWdbCoarseDataPath.GpuResidentBatch`
   - Expected: execution.rows[0].values[1].to_text() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Reject mismatched GPU SQL aggregate candidates before accepting GPU evidence")
val bad_gpu_rows = [
    DbRow(columns: ["name", "count"], values: [DbValue.Text(value: "Alice"), DbValue.Integer(value: 3)]),
    DbRow(columns: ["name", "count"], values: [DbValue.Text(value: "Bob"), DbValue.Integer(value: 1)])
]
val execution = sql_join_aggregate_offload_execute_validated(
    adapter_rows(),
    bad_gpu_rows,
    [0, 1, 2],
    DbStorageOffloadMode.RamOnly,
    gpu_wdb_queue_initial(2),
    gpu_wdb_library_with_targets("cuda", 1, ["gpu_db_join_aggregate_batch"]),
    true,
    true,
    true,
    gpu_wdb_default_budget(),
    512
)
expect(sql_join_aggregate_result_rows_equal(adapter_rows(), bad_gpu_rows)).to_be(false)
expect(sql_join_aggregate_offload_used_gpu(execution)).to_be(false)
expect(execution.offload.dispatch_target).to_equal("cpu_fallback")
expect(execution.offload.reason).to_equal("gpu-cpu-row-mismatch")
expect(execution.gpu_candidate_validated).to_be(false)
expect(execution.offload.gpu_candidate_validated).to_be(false)
expect(execution.offload.validation_reason).to_equal("gpu-cpu-row-mismatch")
expect(execution.offload.profile.data_path).to_equal(GpuWdbCoarseDataPath.GpuResidentBatch)
expect(execution.rows[0].values[1].to_text()).to_equal("2")
```

</details>

#### should replace SQL aggregate rows only after measured device and SQL candidates match

- Require native join aggregate timing plus CPU-oracle SQL row agreement
- adapter rows
- adapter rows
- gpu wdb queue initial
- gpu wdb device backend
- adapter budget
   - Expected: execution.offload.dispatch_target equals `gpu_db_join_aggregate_batch`
   - Expected: execution.validation_reason equals `production-gpu-row-match`
   - Expected: execution.rows[0].values[1].to_text() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Require native join aggregate timing plus CPU-oracle SQL row agreement")
val execution = sql_join_aggregate_offload_execute_device_validated(
    adapter_rows(),
    adapter_rows(),
    [0, 1, 2],
    [0, 1, 2],
    DbStorageOffloadMode.RamOnly,
    gpu_wdb_queue_initial(2),
    gpu_wdb_device_backend("cuda", 9, ["gpu_db_join_aggregate_batch"], true, "cuda-device-0"),
    true,
    9,
    true,
    adapter_budget(),
    512,
    100,
    190,
    57,
    "cuda-event"
)
expect(execution.offload.dispatch_target).to_equal("gpu_db_join_aggregate_batch")
expect(execution.offload.cpu_authoritative).to_be(false)
expect(execution.cpu_authoritative).to_be(false)
expect(execution.gpu_candidate_validated).to_be(true)
expect(execution.validation_reason).to_equal("production-gpu-row-match")
expect(execution.device_offload.device_execution.device_result.production_device_claim).to_be(true)
expect(execution.rows[0].values[1].to_text()).to_equal("2")
```

</details>

#### should keep SQL aggregate rows on CPU when measured device candidates mismatch

- Reject native join aggregate replacement when SQL candidate rows differ
- adapter rows
- adapter mismatched rows
- gpu wdb queue initial
- gpu wdb device backend
- adapter budget
   - Expected: execution.offload.dispatch_target equals `cpu_fallback`
   - Expected: execution.offload.reason equals `production-gpu-sql-row-mismatch`
   - Expected: execution.rows[0].values[1].to_text() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 32 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Reject native join aggregate replacement when SQL candidate rows differ")
val execution = sql_join_aggregate_offload_execute_device_validated(
    adapter_rows(),
    adapter_mismatched_rows(),
    [0, 1, 2],
    [0, 1, 2],
    DbStorageOffloadMode.RamOnly,
    gpu_wdb_queue_initial(2),
    gpu_wdb_device_backend("cuda", 9, ["gpu_db_join_aggregate_batch"], true, "cuda-device-0"),
    true,
    9,
    true,
    adapter_budget(),
    512,
    100,
    190,
    57,
    "cuda-event"
)
expect(sql_join_aggregate_offload_used_gpu(SqlJoinAggregateOffloadExecution(
    rows: execution.rows,
    offload: execution.offload,
    cpu_authoritative: execution.cpu_authoritative,
    gpu_candidate_validated: execution.gpu_candidate_validated,
    validation_reason: execution.validation_reason
))).to_be(false)
expect(execution.offload.dispatch_target).to_equal("cpu_fallback")
expect(execution.offload.reason).to_equal("production-gpu-sql-row-mismatch")
expect(execution.cpu_authoritative).to_be(true)
expect(execution.gpu_candidate_validated).to_be(false)
expect(execution.device_offload.device_execution.device_result.production_device_claim).to_be(true)
expect(execution.rows[0].values[1].to_text()).to_equal("2")
```

</details>

#### should reject perf-only join aggregate device evidence

- Keep mock device timing from replacing SQL aggregate rows
- adapter rows
- adapter rows
- gpu wdb queue initial
- gpu wdb device backend
- adapter budget
   - Expected: execution.offload.dispatch_target equals `gpu_db_join_aggregate_batch`
   - Expected: execution.offload.validation_reason equals `production-device-not-measured`
   - Expected: execution.rows[0].values[1].to_text() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Keep mock device timing from replacing SQL aggregate rows")
val execution = sql_join_aggregate_offload_execute_device_validated(
    adapter_rows(),
    adapter_rows(),
    [0, 1, 2],
    [0, 1, 2],
    DbStorageOffloadMode.RamOnly,
    gpu_wdb_queue_initial(2),
    gpu_wdb_device_backend("mock", 9, ["gpu_db_join_aggregate_batch"], false, "mock-device"),
    true,
    9,
    true,
    adapter_budget(),
    512,
    100,
    190,
    57,
    "mock-clock"
)
expect(execution.offload.dispatch_target).to_equal("gpu_db_join_aggregate_batch")
expect(execution.offload.cpu_authoritative).to_be(true)
expect(execution.offload.validation_reason).to_equal("production-device-not-measured")
expect(execution.gpu_candidate_validated).to_be(false)
expect(execution.device_offload.device_execution.device_result.production_device_claim).to_be(false)
expect(execution.rows[0].values[1].to_text()).to_equal("2")
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
