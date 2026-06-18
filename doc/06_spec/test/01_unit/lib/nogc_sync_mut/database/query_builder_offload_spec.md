# QueryBuilder GPU Offload Integration

> These scenarios verify that the live `QueryBuilder` row operator path can feed RAM-only scan/filter/project and aggregate count work into the shared DB offload facade while keeping CPU-computed rows and row IDs authoritative.

<!-- sdn-diagram:id=query_builder_offload_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=query_builder_offload_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

query_builder_offload_spec -> std
query_builder_offload_spec -> nogc_sync_mut
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=query_builder_offload_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 31 | 31 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# QueryBuilder GPU Offload Integration

These scenarios verify that the live `QueryBuilder` row operator path can feed RAM-only scan/filter/project and aggregate count work into the shared DB offload facade while keeping CPU-computed rows and row IDs authoritative.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Requirements | doc/02_requirements/feature/gpu_web_db_offload.md |
| Plan | doc/03_plan/agent_tasks/gpu_web_db_offload_impl_status.md |
| Design | doc/05_design/gpu_web_db_offload.md |
| Research | N/A |
| Source | `test/01_unit/lib/nogc_sync_mut/database/query_builder_offload_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

These scenarios verify that the live `QueryBuilder` row operator path can feed
RAM-only scan/filter/project and aggregate count work into the shared DB
offload facade while keeping CPU-computed rows and row IDs authoritative.

## Examples

Build a normal `QueryBuilder`, call `execute_with_offload`, and inspect both
the returned CPU rows and the offload accounting record.

**Requirements:** doc/02_requirements/feature/gpu_web_db_offload.md
**Plan:** doc/03_plan/agent_tasks/gpu_web_db_offload_impl_status.md
**Design:** doc/05_design/gpu_web_db_offload.md
**Research:** N/A

## Scenarios

### QueryBuilder GPU offload integration

#### should report GPU row-query accounting while preserving CPU row order

- Run a coarse RAM-only scan/filter/project query through offload accounting
- var query = QueryBuilder for table
-  filter by
-  order by
- gpu wdb queue initial
- gpu wdb library with targets
- qo budget
   - Expected: rows.len() equals `3`
   - Expected: rows[0].get("id")? equals `3`
   - Expected: rows[1].get("id")? equals `1`
   - Expected: rows[2].get("id")? equals `4`
   - Expected: offload.mode equals `DbStorageOffloadMode.RamOnly`
   - Expected: offload.workload equals `DbStorageOffloadWorkload.ScanFilterProject`
   - Expected: offload.dispatch_target equals `gpu_db_columnar_scan_batch`
   - Expected: offload.row_ids.len() equals `3`
   - Expected: offload.row_ids[0] equals `2`
   - Expected: offload.row_ids[1] equals `0`
   - Expected: offload.row_ids[2] equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 32 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Run a coarse RAM-only scan/filter/project query through offload accounting")
var query = QueryBuilder.for_table(qo_table())
    .filter_by("status", CompareOp.Eq, "Open")
    .order_by("score", false)
val rows = query.execute()
val offload = db_storage_execute_rows(
    DbStorageOffloadMode.RamOnly,
    DbStorageOffloadWorkload.ScanFilterProject,
    4,
    512,
    gpu_wdb_queue_initial(4),
    gpu_wdb_library_with_targets("cuda", 1, ["gpu_db_columnar_scan_batch"]),
    true,
    true,
    true,
    qo_budget(),
    [2, 0, 3]
)

expect(rows.len()).to_equal(3)
expect(rows[0].get("id")?).to_equal("3")
expect(rows[1].get("id")?).to_equal("1")
expect(rows[2].get("id")?).to_equal("4")
expect(offload.mode).to_equal(DbStorageOffloadMode.RamOnly)
expect(offload.workload).to_equal(DbStorageOffloadWorkload.ScanFilterProject)
expect(offload.dispatch_target).to_equal("gpu_db_columnar_scan_batch")
expect(offload.gpu_dispatched).to_be(true)
expect(offload.cpu_authoritative).to_be(true)
expect(offload.row_ids.len()).to_equal(3)
expect(offload.row_ids[0]).to_equal(2)
expect(offload.row_ids[1]).to_equal(0)
expect(offload.row_ids[2]).to_equal(3)
```

</details>

#### should replace QueryBuilder row output only after native device candidates match

- Validate measured native columnar-scan candidates against QueryBuilder row IDs
- var query = QueryBuilder for table
-  filter by
-  order by
- gpu wdb queue initial
- gpu wdb device backend
- qo budget
   - Expected: execution.rows.len() equals `3`
   - Expected: execution.rows[0].get("id")? equals `3`
   - Expected: execution.rows[1].get("id")? equals `1`
   - Expected: execution.rows[2].get("id")? equals `4`
   - Expected: execution.offload.execution.validation_reason equals `production-gpu-row-match`
   - Expected: execution.offload.execution.row_ids[0] equals `2`
   - Expected: execution.offload.execution.row_ids[1] equals `0`
   - Expected: execution.offload.execution.row_ids[2] equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 30 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Validate measured native columnar-scan candidates against QueryBuilder row IDs")
var query = QueryBuilder.for_table(qo_table())
    .filter_by("status", CompareOp.Eq, "Open")
    .order_by("score", false)
val execution = query.execute_with_device_backend_validated(
    gpu_wdb_queue_initial(4),
    gpu_wdb_device_backend("cuda", 5, ["gpu_db_columnar_scan_batch"], true, "cuda-device-0"),
    5,
    true,
    qo_budget(),
    512,
    [2, 0, 3],
    100,
    210,
    67,
    "cuda-event"
)

expect(execution.rows.len()).to_equal(3)
expect(execution.rows[0].get("id")?).to_equal("3")
expect(execution.rows[1].get("id")?).to_equal("1")
expect(execution.rows[2].get("id")?).to_equal("4")
expect(execution.offload.execution.gpu_dispatched).to_be(true)
expect(execution.offload.execution.cpu_authoritative).to_be(false)
expect(execution.offload.execution.gpu_candidate_validated).to_be(true)
expect(execution.offload.execution.validation_reason).to_equal("production-gpu-row-match")
expect(execution.offload.execution.row_ids[0]).to_equal(2)
expect(execution.offload.execution.row_ids[1]).to_equal(0)
expect(execution.offload.execution.row_ids[2]).to_equal(3)
expect(execution.offload.device_execution.device_result.production_device_claim).to_be(true)
```

</details>

#### should return SSD materialized projected rows after candidate validation

- Consume projected SSD row values when QueryBuilder row IDs validate
- var query = QueryBuilder for table
-  filter by
-  order by
- qo ssd materialization
- gpu wdb queue initial
- gpu wdb library with targets
- qo budget
   - Expected: execution.offload.validation_reason equals `gpu-cpu-row-match`
   - Expected: execution.rows.len() equals `3`
   - Expected: execution.rows[0].get("id")? equals `ssd-3`
   - Expected: execution.rows[0].get("score")? equals `20`
   - Expected: execution.rows[1].get("id")? equals `ssd-1`
   - Expected: execution.rows[2].get("id")? equals `ssd-4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Consume projected SSD row values when QueryBuilder row IDs validate")
var query = QueryBuilder.for_table(qo_table())
    .filter_by("status", CompareOp.Eq, "Open")
    .order_by("score", false)
val execution = query.execute_with_ssd_materialized_projection(
    qo_ssd_materialization([2, 0, 3]),
    gpu_wdb_queue_initial(4),
    gpu_wdb_library_with_targets("cuda", 1, ["gpu_db_columnar_scan_batch"]),
    true,
    true,
    qo_budget(),
    [2, 0, 3]
)

expect(execution.offload.gpu_candidate_validated).to_be(true)
expect(execution.offload.validation_reason).to_equal("gpu-cpu-row-match")
expect(db_storage_offload_used_gpu(execution.offload)).to_be(true)
expect(execution.rows.len()).to_equal(3)
expect(execution.rows[0].get("id")?).to_equal("ssd-3")
expect(execution.rows[0].get("score")?).to_equal("20")
expect(execution.rows[1].get("id")?).to_equal("ssd-1")
expect(execution.rows[2].get("id")?).to_equal("ssd-4")
```

</details>

#### should fall back to CPU rows when SSD materialized candidates mismatch

- Reject projected SSD row values when GPU candidate row IDs mismatch
- var query = QueryBuilder for table
-  filter by
-  order by
- qo ssd materialization
- gpu wdb queue initial
- gpu wdb library with targets
- qo budget
   - Expected: execution.offload.dispatch_target equals `cpu_fallback`
   - Expected: execution.offload.reason equals `gpu-cpu-row-mismatch`
   - Expected: execution.rows.len() equals `3`
   - Expected: execution.rows[0].get("id")? equals `3`
   - Expected: execution.rows[1].get("id")? equals `1`
   - Expected: execution.rows[2].get("id")? equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Reject projected SSD row values when GPU candidate row IDs mismatch")
var query = QueryBuilder.for_table(qo_table())
    .filter_by("status", CompareOp.Eq, "Open")
    .order_by("score", false)
val execution = query.execute_with_ssd_materialized_projection(
    qo_ssd_materialization([2, 0, 3]),
    gpu_wdb_queue_initial(4),
    gpu_wdb_library_with_targets("cuda", 1, ["gpu_db_columnar_scan_batch"]),
    true,
    true,
    qo_budget(),
    [2, 99, 3]
)

expect(db_storage_offload_used_gpu(execution.offload)).to_be(false)
expect(execution.offload.dispatch_target).to_equal("cpu_fallback")
expect(execution.offload.reason).to_equal("gpu-cpu-row-mismatch")
expect(execution.offload.gpu_candidate_validated).to_be(false)
expect(execution.rows.len()).to_equal(3)
expect(execution.rows[0].get("id")?).to_equal("3")
expect(execution.rows[1].get("id")?).to_equal("1")
expect(execution.rows[2].get("id")?).to_equal("4")
```

</details>

#### should fall back for tiny row-query batches without changing results

- Run a tiny RAM-only query that must not claim GPU performance
- var query = QueryBuilder for table
-  filter by
- gpu wdb queue initial
- gpu wdb library with targets
- qo budget
   - Expected: rows.len() equals `1`
   - Expected: rows[0].get("id")? equals `2`
   - Expected: offload.dispatch_target equals `cpu_fallback`
   - Expected: offload.reason equals `batch-too-small`
   - Expected: offload.row_ids[0] equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Run a tiny RAM-only query that must not claim GPU performance")
var query = QueryBuilder.for_table(qo_table())
    .filter_by("status", CompareOp.Eq, "Closed")
val rows = query.execute()
val offload = db_storage_execute_rows(
    DbStorageOffloadMode.RamOnly,
    DbStorageOffloadWorkload.ScanFilterProject,
    4,
    1,
    gpu_wdb_queue_initial(4),
    gpu_wdb_library_with_targets("cuda", 1, ["gpu_db_columnar_scan_batch"]),
    true,
    true,
    true,
    qo_budget(),
    [1]
)

expect(rows.len()).to_equal(1)
expect(rows[0].get("id")?).to_equal("2")
expect(offload.gpu_dispatched).to_be(false)
expect(offload.dispatch_target).to_equal("cpu_fallback")
expect(offload.reason).to_equal("batch-too-small")
expect(offload.row_ids[0]).to_equal(1)
```

</details>

#### should keep take and missing registry behavior CPU-authoritative

- Run a sorted limited query when no GPU row target is registered
- var query = QueryBuilder for table
-  filter by
-  order by
-  take
- gpu wdb queue initial
- gpu wdb library empty
- qo budget
   - Expected: rows.len() equals `2`
   - Expected: rows[0].get("id")? equals `4`
   - Expected: rows[1].get("id")? equals `1`
   - Expected: offload.dispatch_target equals `cpu_fallback`
   - Expected: offload.reason equals `gpu-unavailable`
   - Expected: offload.row_ids.len() equals `2`
   - Expected: offload.row_ids[0] equals `3`
   - Expected: offload.row_ids[1] equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Run a sorted limited query when no GPU row target is registered")
var query = QueryBuilder.for_table(qo_table())
    .filter_by("status", CompareOp.Eq, "Open")
    .order_by("score", true)
    .take(2)
val rows = query.execute()
val offload = db_storage_execute_rows(
    DbStorageOffloadMode.RamOnly,
    DbStorageOffloadWorkload.ScanFilterProject,
    4,
    512,
    gpu_wdb_queue_initial(4),
    gpu_wdb_library_empty(),
    true,
    true,
    true,
    qo_budget(),
    [3, 0]
)

expect(rows.len()).to_equal(2)
expect(rows[0].get("id")?).to_equal("4")
expect(rows[1].get("id")?).to_equal("1")
expect(offload.gpu_dispatched).to_be(false)
expect(offload.dispatch_target).to_equal("cpu_fallback")
expect(offload.reason).to_equal("gpu-unavailable")
expect(offload.row_ids.len()).to_equal(2)
expect(offload.row_ids[0]).to_equal(3)
expect(offload.row_ids[1]).to_equal(0)
```

</details>

#### should report aggregate count work as join aggregate offload

- Run QueryBuilder count through the join/aggregate storage workload
- var query = QueryBuilder for table
-  filter by
- gpu wdb queue initial
- gpu wdb library with targets
- qo budget
   - Expected: execution.count equals `3`
   - Expected: offload.mode equals `DbStorageOffloadMode.RamOnly`
   - Expected: offload.workload equals `DbStorageOffloadWorkload.JoinAggregate`
   - Expected: offload.dispatch_target equals `gpu_db_join_aggregate_batch`
   - Expected: offload.row_ids.len() equals `3`
   - Expected: offload.row_ids[0] equals `0`
   - Expected: offload.row_ids[1] equals `2`
   - Expected: offload.row_ids[2] equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Run QueryBuilder count through the join/aggregate storage workload")
var query = QueryBuilder.for_table(qo_table())
    .filter_by("status", CompareOp.Eq, "Open")
val execution = query.count_with_storage_offload(
    DbStorageOffloadMode.RamOnly,
    gpu_wdb_queue_initial(4),
    gpu_wdb_library_with_targets("cuda", 1, ["gpu_db_join_aggregate_batch"]),
    true,
    true,
    true,
    qo_budget(),
    512
)

val offload = execution.offload
expect(execution.count).to_equal(3)
expect(offload.mode).to_equal(DbStorageOffloadMode.RamOnly)
expect(offload.workload).to_equal(DbStorageOffloadWorkload.JoinAggregate)
expect(db_storage_offload_used_gpu(offload)).to_be(true)
expect(offload.dispatch_target).to_equal("gpu_db_join_aggregate_batch")
expect(offload.cpu_authoritative).to_be(true)
expect(offload.row_ids.len()).to_equal(3)
expect(offload.row_ids[0]).to_equal(0)
expect(offload.row_ids[1]).to_equal(2)
expect(offload.row_ids[2]).to_equal(3)
```

</details>

#### should report filtered SUM work as join aggregate offload

- Run QueryBuilder SUM through the join/aggregate storage workload
- var query = QueryBuilder for table
-  filter by
- gpu wdb queue initial
- gpu wdb library with targets
- qo budget
   - Expected: execution.sum equals `90`
   - Expected: execution.offload.mode equals `DbStorageOffloadMode.RamOnly`
   - Expected: execution.offload.workload equals `DbStorageOffloadWorkload.JoinAggregate`
   - Expected: execution.offload.dispatch_target equals `gpu_db_join_aggregate_batch`
   - Expected: execution.offload.row_ids.len() equals `3`
   - Expected: execution.offload.row_ids[0] equals `0`
   - Expected: execution.offload.row_ids[1] equals `2`
   - Expected: execution.offload.row_ids[2] equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Run QueryBuilder SUM through the join/aggregate storage workload")
var query = QueryBuilder.for_table(qo_table())
    .filter_by("status", CompareOp.Eq, "Open")
val execution = query.sum_i64_with_storage_offload(
    "score",
    DbStorageOffloadMode.RamOnly,
    gpu_wdb_queue_initial(4),
    gpu_wdb_library_with_targets("cuda", 1, ["gpu_db_join_aggregate_batch"]),
    true,
    true,
    true,
    qo_budget(),
    512
)

expect(execution.sum).to_equal(90)
expect(execution.offload.mode).to_equal(DbStorageOffloadMode.RamOnly)
expect(execution.offload.workload).to_equal(DbStorageOffloadWorkload.JoinAggregate)
expect(db_storage_offload_used_gpu(execution.offload)).to_be(true)
expect(execution.offload.dispatch_target).to_equal("gpu_db_join_aggregate_batch")
expect(execution.offload.cpu_authoritative).to_be(true)
expect(execution.offload.row_ids.len()).to_equal(3)
expect(execution.offload.row_ids[0]).to_equal(0)
expect(execution.offload.row_ids[1]).to_equal(2)
expect(execution.offload.row_ids[2]).to_equal(3)
```

</details>

#### should report filtered AVG work as join aggregate offload

- Run QueryBuilder AVG through the join/aggregate storage workload
- var query = QueryBuilder for table
-  filter by
- gpu wdb queue initial
- gpu wdb library with targets
- qo budget
   - Expected: execution.value equals `30`
   - Expected: execution.offload.mode equals `DbStorageOffloadMode.RamOnly`
   - Expected: execution.offload.workload equals `DbStorageOffloadWorkload.JoinAggregate`
   - Expected: execution.offload.dispatch_target equals `gpu_db_join_aggregate_batch`
   - Expected: execution.offload.row_ids.len() equals `3`
   - Expected: execution.offload.row_ids[0] equals `0`
   - Expected: execution.offload.row_ids[1] equals `2`
   - Expected: execution.offload.row_ids[2] equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Run QueryBuilder AVG through the join/aggregate storage workload")
var query = QueryBuilder.for_table(qo_table())
    .filter_by("status", CompareOp.Eq, "Open")
val execution = query.avg_i64_with_storage_offload(
    "score",
    DbStorageOffloadMode.RamOnly,
    gpu_wdb_queue_initial(4),
    gpu_wdb_library_with_targets("cuda", 1, ["gpu_db_join_aggregate_batch"]),
    true,
    true,
    true,
    qo_budget(),
    512
)

expect(execution.value).to_equal(30)
expect(execution.offload.mode).to_equal(DbStorageOffloadMode.RamOnly)
expect(execution.offload.workload).to_equal(DbStorageOffloadWorkload.JoinAggregate)
expect(db_storage_offload_used_gpu(execution.offload)).to_be(true)
expect(execution.offload.dispatch_target).to_equal("gpu_db_join_aggregate_batch")
expect(execution.offload.cpu_authoritative).to_be(true)
expect(execution.offload.row_ids.len()).to_equal(3)
expect(execution.offload.row_ids[0]).to_equal(0)
expect(execution.offload.row_ids[1]).to_equal(2)
expect(execution.offload.row_ids[2]).to_equal(3)
```

</details>

#### should report filtered MIN and MAX work as join aggregate offload

- Run QueryBuilder MIN and MAX through the join/aggregate storage workload
- var query = QueryBuilder for table
-  filter by
- gpu wdb queue initial
- gpu wdb library with targets
- qo budget
- gpu wdb queue initial
- gpu wdb library with targets
- qo budget
   - Expected: min_execution.value equals `20`
   - Expected: max_execution.value equals `40`
   - Expected: min_execution.offload.workload equals `DbStorageOffloadWorkload.JoinAggregate`
   - Expected: max_execution.offload.workload equals `DbStorageOffloadWorkload.JoinAggregate`
   - Expected: min_execution.offload.row_ids.len() equals `3`
   - Expected: max_execution.offload.row_ids[2] equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 36 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Run QueryBuilder MIN and MAX through the join/aggregate storage workload")
var query = QueryBuilder.for_table(qo_table())
    .filter_by("status", CompareOp.Eq, "Open")
val min_execution = query.min_i64_with_storage_offload(
    "score",
    DbStorageOffloadMode.RamOnly,
    gpu_wdb_queue_initial(4),
    gpu_wdb_library_with_targets("cuda", 1, ["gpu_db_join_aggregate_batch"]),
    true,
    true,
    true,
    qo_budget(),
    512
)
val max_execution = query.max_i64_with_storage_offload(
    "score",
    DbStorageOffloadMode.RamOnly,
    gpu_wdb_queue_initial(4),
    gpu_wdb_library_with_targets("cuda", 1, ["gpu_db_join_aggregate_batch"]),
    true,
    true,
    true,
    qo_budget(),
    512
)

expect(min_execution.value).to_equal(20)
expect(max_execution.value).to_equal(40)
expect(min_execution.offload.workload).to_equal(DbStorageOffloadWorkload.JoinAggregate)
expect(max_execution.offload.workload).to_equal(DbStorageOffloadWorkload.JoinAggregate)
expect(db_storage_offload_used_gpu(min_execution.offload)).to_be(true)
expect(db_storage_offload_used_gpu(max_execution.offload)).to_be(true)
expect(min_execution.offload.cpu_authoritative).to_be(true)
expect(max_execution.offload.cpu_authoritative).to_be(true)
expect(min_execution.offload.row_ids.len()).to_equal(3)
expect(max_execution.offload.row_ids[2]).to_equal(3)
```

</details>

#### should replace QueryBuilder COUNT only after native candidates match

- Require native timing, row IDs, and scalar count agreement
- var query = QueryBuilder for table
-  filter by
- gpu wdb queue initial
- gpu wdb device backend
- qo budget
   - Expected: execution.count equals `3`
   - Expected: execution.offload.execution.validation_reason equals `production-gpu-row-match`
   - Expected: execution.offload.execution.dispatch_target equals `gpu_db_join_aggregate_batch`


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Require native timing, row IDs, and scalar count agreement")
var query = QueryBuilder.for_table(qo_table())
    .filter_by("status", CompareOp.Eq, "Open")
val execution = query.count_with_device_backend_validated(
    DbStorageOffloadMode.RamOnly,
    gpu_wdb_queue_initial(4),
    gpu_wdb_device_backend("cuda", 7, ["gpu_db_join_aggregate_batch"], true, "cuda-device-0"),
    true,
    7,
    true,
    qo_budget(),
    512,
    [0, 2, 3],
    3,
    100,
    190,
    58,
    "cuda-event"
)

expect(execution.count).to_equal(3)
expect(db_storage_offload_used_gpu(execution.offload.execution)).to_be(true)
expect(execution.offload.execution.cpu_authoritative).to_be(false)
expect(execution.offload.execution.gpu_candidate_validated).to_be(true)
expect(execution.offload.execution.validation_reason).to_equal("production-gpu-row-match")
expect(execution.offload.execution.dispatch_target).to_equal("gpu_db_join_aggregate_batch")
expect(execution.offload.device_execution.device_result.production_device_claim).to_be(true)
```

</details>

#### should keep QueryBuilder COUNT on CPU when native scalar candidates mismatch

- Reject native count replacement when the scalar candidate differs
- var query = QueryBuilder for table
-  filter by
- gpu wdb queue initial
- gpu wdb device backend
- qo budget
   - Expected: execution.count equals `3`
   - Expected: execution.offload.execution.dispatch_target equals `cpu_fallback`
   - Expected: execution.offload.execution.validation_reason equals `production-gpu-count-mismatch`


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Reject native count replacement when the scalar candidate differs")
var query = QueryBuilder.for_table(qo_table())
    .filter_by("status", CompareOp.Eq, "Open")
val execution = query.count_with_device_backend_validated(
    DbStorageOffloadMode.RamOnly,
    gpu_wdb_queue_initial(4),
    gpu_wdb_device_backend("cuda", 7, ["gpu_db_join_aggregate_batch"], true, "cuda-device-0"),
    true,
    7,
    true,
    qo_budget(),
    512,
    [0, 2, 3],
    99,
    100,
    190,
    58,
    "cuda-event"
)

expect(execution.count).to_equal(3)
expect(db_storage_offload_used_gpu(execution.offload.execution)).to_be(false)
expect(execution.offload.execution.dispatch_target).to_equal("cpu_fallback")
expect(execution.offload.execution.cpu_authoritative).to_be(true)
expect(execution.offload.execution.gpu_candidate_validated).to_be(false)
expect(execution.offload.execution.validation_reason).to_equal("production-gpu-count-mismatch")
expect(execution.offload.device_execution.device_result.production_device_claim).to_be(true)
```

</details>

#### should replace QueryBuilder SUM only after native candidates match

- Require native timing, row IDs, and scalar SUM agreement
- var query = QueryBuilder for table
-  filter by
- gpu wdb queue initial
- gpu wdb device backend
- qo budget
   - Expected: execution.sum equals `90`
   - Expected: execution.offload.execution.validation_reason equals `production-gpu-row-match`
   - Expected: execution.offload.execution.dispatch_target equals `gpu_db_join_aggregate_batch`


<details>
<summary>Executable SSpec</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Require native timing, row IDs, and scalar SUM agreement")
var query = QueryBuilder.for_table(qo_table())
    .filter_by("status", CompareOp.Eq, "Open")
val execution = query.sum_i64_with_device_backend_validated(
    "score",
    DbStorageOffloadMode.RamOnly,
    gpu_wdb_queue_initial(4),
    gpu_wdb_device_backend("cuda", 7, ["gpu_db_join_aggregate_batch"], true, "cuda-device-0"),
    true,
    7,
    true,
    qo_budget(),
    512,
    [0, 2, 3],
    90,
    100,
    190,
    58,
    "cuda-event"
)

expect(execution.sum).to_equal(90)
expect(db_storage_offload_used_gpu(execution.offload.execution)).to_be(true)
expect(execution.offload.execution.cpu_authoritative).to_be(false)
expect(execution.offload.execution.gpu_candidate_validated).to_be(true)
expect(execution.offload.execution.validation_reason).to_equal("production-gpu-row-match")
expect(execution.offload.execution.dispatch_target).to_equal("gpu_db_join_aggregate_batch")
expect(execution.offload.device_execution.device_result.production_device_claim).to_be(true)
```

</details>

#### should reject perf-only QueryBuilder SUM device evidence

- Keep SUM CPU authoritative when backend lacks production timing
- var query = QueryBuilder for table
-  filter by
- gpu wdb queue initial
- gpu wdb device backend
- qo budget
   - Expected: execution.sum equals `90`
   - Expected: execution.offload.execution.validation_reason equals `production-device-not-measured`


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Keep SUM CPU authoritative when backend lacks production timing")
var query = QueryBuilder.for_table(qo_table())
    .filter_by("status", CompareOp.Eq, "Open")
val execution = query.sum_i64_with_device_backend_validated(
    "score",
    DbStorageOffloadMode.RamOnly,
    gpu_wdb_queue_initial(4),
    gpu_wdb_device_backend("host-safe-mock", 7, ["gpu_db_join_aggregate_batch"], false, "mock-device"),
    true,
    7,
    true,
    qo_budget(),
    512,
    [0, 2, 3],
    90,
    100,
    190,
    58,
    "mock-timer"
)

expect(execution.sum).to_equal(90)
expect(db_storage_offload_used_gpu(execution.offload.execution)).to_be(false)
expect(execution.offload.execution.cpu_authoritative).to_be(true)
expect(execution.offload.execution.gpu_candidate_validated).to_be(false)
expect(execution.offload.execution.validation_reason).to_equal("production-device-not-measured")
expect(execution.offload.device_execution.device_result.production_device_claim).to_be(false)
```

</details>

#### should replace QueryBuilder AVG only after native candidates match

- Require native timing, row IDs, and scalar AVG agreement
- var query = QueryBuilder for table
-  filter by
- gpu wdb queue initial
- gpu wdb device backend
- qo budget
   - Expected: execution.value equals `30`
   - Expected: execution.offload.execution.validation_reason equals `production-gpu-row-match`


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Require native timing, row IDs, and scalar AVG agreement")
var query = QueryBuilder.for_table(qo_table())
    .filter_by("status", CompareOp.Eq, "Open")
val execution = query.avg_i64_with_device_backend_validated(
    "score",
    DbStorageOffloadMode.RamOnly,
    gpu_wdb_queue_initial(4),
    gpu_wdb_device_backend("cuda", 7, ["gpu_db_join_aggregate_batch"], true, "cuda-device-0"),
    true,
    7,
    true,
    qo_budget(),
    512,
    [0, 2, 3],
    30,
    100,
    190,
    58,
    "cuda-event"
)

expect(execution.value).to_equal(30)
expect(db_storage_offload_used_gpu(execution.offload.execution)).to_be(true)
expect(execution.offload.execution.cpu_authoritative).to_be(false)
expect(execution.offload.execution.gpu_candidate_validated).to_be(true)
expect(execution.offload.execution.validation_reason).to_equal("production-gpu-row-match")
expect(execution.offload.device_execution.device_result.production_device_claim).to_be(true)
```

</details>

#### should keep QueryBuilder AVG on CPU when native scalar candidates mismatch

- Reject native AVG replacement when the scalar candidate differs
- var query = QueryBuilder for table
-  filter by
- gpu wdb queue initial
- gpu wdb device backend
- qo budget
   - Expected: execution.value equals `30`
   - Expected: execution.offload.execution.dispatch_target equals `cpu_fallback`
   - Expected: execution.offload.execution.validation_reason equals `production-gpu-avg-mismatch`


<details>
<summary>Executable SSpec</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Reject native AVG replacement when the scalar candidate differs")
var query = QueryBuilder.for_table(qo_table())
    .filter_by("status", CompareOp.Eq, "Open")
val execution = query.avg_i64_with_device_backend_validated(
    "score",
    DbStorageOffloadMode.RamOnly,
    gpu_wdb_queue_initial(4),
    gpu_wdb_device_backend("cuda", 7, ["gpu_db_join_aggregate_batch"], true, "cuda-device-0"),
    true,
    7,
    true,
    qo_budget(),
    512,
    [0, 2, 3],
    99,
    100,
    190,
    58,
    "cuda-event"
)

expect(execution.value).to_equal(30)
expect(db_storage_offload_used_gpu(execution.offload.execution)).to_be(false)
expect(execution.offload.execution.dispatch_target).to_equal("cpu_fallback")
expect(execution.offload.execution.cpu_authoritative).to_be(true)
expect(execution.offload.execution.gpu_candidate_validated).to_be(false)
expect(execution.offload.execution.validation_reason).to_equal("production-gpu-avg-mismatch")
expect(execution.offload.device_execution.device_result.production_device_claim).to_be(true)
```

</details>

#### should replace QueryBuilder MIN only after native candidates match

- Require native timing, row IDs, and scalar MIN agreement
- var query = QueryBuilder for table
-  filter by
- gpu wdb queue initial
- gpu wdb device backend
- qo budget
   - Expected: execution.value equals `20`
   - Expected: execution.offload.execution.validation_reason equals `production-gpu-row-match`


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Require native timing, row IDs, and scalar MIN agreement")
var query = QueryBuilder.for_table(qo_table())
    .filter_by("status", CompareOp.Eq, "Open")
val execution = query.min_i64_with_device_backend_validated(
    "score",
    DbStorageOffloadMode.RamOnly,
    gpu_wdb_queue_initial(4),
    gpu_wdb_device_backend("cuda", 7, ["gpu_db_join_aggregate_batch"], true, "cuda-device-0"),
    true,
    7,
    true,
    qo_budget(),
    512,
    [0, 2, 3],
    20,
    100,
    190,
    58,
    "cuda-event"
)

expect(execution.value).to_equal(20)
expect(db_storage_offload_used_gpu(execution.offload.execution)).to_be(true)
expect(execution.offload.execution.cpu_authoritative).to_be(false)
expect(execution.offload.execution.gpu_candidate_validated).to_be(true)
expect(execution.offload.execution.validation_reason).to_equal("production-gpu-row-match")
expect(execution.offload.device_execution.device_result.production_device_claim).to_be(true)
```

</details>

#### should keep QueryBuilder MAX on CPU when native scalar candidates mismatch

- Reject native MAX replacement when the scalar candidate differs
- var query = QueryBuilder for table
-  filter by
- gpu wdb queue initial
- gpu wdb device backend
- qo budget
   - Expected: execution.value equals `40`
   - Expected: execution.offload.execution.dispatch_target equals `cpu_fallback`
   - Expected: execution.offload.execution.validation_reason equals `production-gpu-max-mismatch`


<details>
<summary>Executable SSpec</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Reject native MAX replacement when the scalar candidate differs")
var query = QueryBuilder.for_table(qo_table())
    .filter_by("status", CompareOp.Eq, "Open")
val execution = query.max_i64_with_device_backend_validated(
    "score",
    DbStorageOffloadMode.RamOnly,
    gpu_wdb_queue_initial(4),
    gpu_wdb_device_backend("cuda", 7, ["gpu_db_join_aggregate_batch"], true, "cuda-device-0"),
    true,
    7,
    true,
    qo_budget(),
    512,
    [0, 2, 3],
    99,
    100,
    190,
    58,
    "cuda-event"
)

expect(execution.value).to_equal(40)
expect(db_storage_offload_used_gpu(execution.offload.execution)).to_be(false)
expect(execution.offload.execution.dispatch_target).to_equal("cpu_fallback")
expect(execution.offload.execution.cpu_authoritative).to_be(true)
expect(execution.offload.execution.gpu_candidate_validated).to_be(false)
expect(execution.offload.execution.validation_reason).to_equal("production-gpu-max-mismatch")
expect(execution.offload.device_execution.device_result.production_device_claim).to_be(true)
```

</details>

#### should compute SUM from SSD projected rows after candidate validation

- Consume projected SSD numeric values for a validated QueryBuilder aggregate
- var query = QueryBuilder for table
-  filter by
-  order by
- qo ssd materialization
- gpu wdb queue initial
- gpu wdb library with targets
- qo budget
   - Expected: execution.sum equals `90`
   - Expected: execution.offload.validation_reason equals `gpu-cpu-row-match`
   - Expected: execution.offload.row_ids[0] equals `2`
   - Expected: execution.offload.row_ids[1] equals `0`
   - Expected: execution.offload.row_ids[2] equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Consume projected SSD numeric values for a validated QueryBuilder aggregate")
var query = QueryBuilder.for_table(qo_table())
    .filter_by("status", CompareOp.Eq, "Open")
    .order_by("score", false)
val execution = query.sum_i64_with_ssd_materialized_projection(
    "score",
    qo_ssd_materialization([2, 0, 3]),
    gpu_wdb_queue_initial(4),
    gpu_wdb_library_with_targets("cuda", 1, ["gpu_db_columnar_scan_batch"]),
    true,
    true,
    qo_budget(),
    [2, 0, 3]
)

expect(execution.sum).to_equal(90)
expect(db_storage_offload_used_gpu(execution.offload)).to_be(true)
expect(execution.offload.gpu_candidate_validated).to_be(true)
expect(execution.offload.validation_reason).to_equal("gpu-cpu-row-match")
expect(execution.offload.row_ids[0]).to_equal(2)
expect(execution.offload.row_ids[1]).to_equal(0)
expect(execution.offload.row_ids[2]).to_equal(3)
```

</details>

#### should compute MIN and MAX from SSD projected rows after candidate validation

- Consume projected SSD numeric values for validated QueryBuilder scalar aggregates
- var query = QueryBuilder for table
-  filter by
-  order by
- qo ssd materialization
- gpu wdb queue initial
- gpu wdb library with targets
- qo budget
- qo ssd materialization
- gpu wdb queue initial
- gpu wdb library with targets
- qo budget
   - Expected: min_execution.value equals `20`
   - Expected: max_execution.value equals `40`
   - Expected: max_execution.offload.validation_reason equals `gpu-cpu-row-match`


<details>
<summary>Executable SSpec</summary>

Runnable source: 31 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Consume projected SSD numeric values for validated QueryBuilder scalar aggregates")
var query = QueryBuilder.for_table(qo_table())
    .filter_by("status", CompareOp.Eq, "Open")
    .order_by("score", false)
val min_execution = query.min_i64_with_ssd_materialized_projection(
    "score",
    qo_ssd_materialization([2, 0, 3]),
    gpu_wdb_queue_initial(4),
    gpu_wdb_library_with_targets("cuda", 1, ["gpu_db_columnar_scan_batch"]),
    true,
    true,
    qo_budget(),
    [2, 0, 3]
)
val max_execution = query.max_i64_with_ssd_materialized_projection(
    "score",
    qo_ssd_materialization([2, 0, 3]),
    gpu_wdb_queue_initial(4),
    gpu_wdb_library_with_targets("cuda", 1, ["gpu_db_columnar_scan_batch"]),
    true,
    true,
    qo_budget(),
    [2, 0, 3]
)

expect(min_execution.value).to_equal(20)
expect(max_execution.value).to_equal(40)
expect(db_storage_offload_used_gpu(min_execution.offload)).to_be(true)
expect(db_storage_offload_used_gpu(max_execution.offload)).to_be(true)
expect(min_execution.offload.gpu_candidate_validated).to_be(true)
expect(max_execution.offload.validation_reason).to_equal("gpu-cpu-row-match")
```

</details>

#### should compute AVG from SSD projected rows after candidate validation

- Consume projected SSD numeric values for a validated QueryBuilder AVG
- var query = QueryBuilder for table
-  filter by
-  order by
- qo ssd materialization
- gpu wdb queue initial
- gpu wdb library with targets
- qo budget
   - Expected: execution.value equals `30`
   - Expected: execution.offload.validation_reason equals `gpu-cpu-row-match`
   - Expected: execution.offload.row_ids[0] equals `2`
   - Expected: execution.offload.row_ids[1] equals `0`
   - Expected: execution.offload.row_ids[2] equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Consume projected SSD numeric values for a validated QueryBuilder AVG")
var query = QueryBuilder.for_table(qo_table())
    .filter_by("status", CompareOp.Eq, "Open")
    .order_by("score", false)
val execution = query.avg_i64_with_ssd_materialized_projection(
    "score",
    qo_ssd_materialization([2, 0, 3]),
    gpu_wdb_queue_initial(4),
    gpu_wdb_library_with_targets("cuda", 1, ["gpu_db_columnar_scan_batch"]),
    true,
    true,
    qo_budget(),
    [2, 0, 3]
)

expect(execution.value).to_equal(30)
expect(db_storage_offload_used_gpu(execution.offload)).to_be(true)
expect(execution.offload.gpu_candidate_validated).to_be(true)
expect(execution.offload.validation_reason).to_equal("gpu-cpu-row-match")
expect(execution.offload.row_ids[0]).to_equal(2)
expect(execution.offload.row_ids[1]).to_equal(0)
expect(execution.offload.row_ids[2]).to_equal(3)
```

</details>

#### should compute COUNT from SSD projected rows after candidate validation

- Consume projected SSD row IDs for a validated QueryBuilder count aggregate
- var query = QueryBuilder for table
-  filter by
-  order by
- qo ssd materialization
- gpu wdb queue initial
- gpu wdb library with targets
- qo budget
   - Expected: execution.count equals `3`
   - Expected: execution.offload.validation_reason equals `gpu-cpu-row-match`
   - Expected: execution.offload.row_ids[0] equals `2`
   - Expected: execution.offload.row_ids[1] equals `0`
   - Expected: execution.offload.row_ids[2] equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Consume projected SSD row IDs for a validated QueryBuilder count aggregate")
var query = QueryBuilder.for_table(qo_table())
    .filter_by("status", CompareOp.Eq, "Open")
    .order_by("score", false)
val execution = query.count_with_ssd_materialized_projection(
    qo_ssd_materialization([2, 0, 3]),
    gpu_wdb_queue_initial(4),
    gpu_wdb_library_with_targets("cuda", 1, ["gpu_db_columnar_scan_batch"]),
    true,
    true,
    qo_budget(),
    [2, 0, 3]
)

expect(execution.count).to_equal(3)
expect(db_storage_offload_used_gpu(execution.offload)).to_be(true)
expect(execution.offload.gpu_candidate_validated).to_be(true)
expect(execution.offload.validation_reason).to_equal("gpu-cpu-row-match")
expect(execution.offload.row_ids[0]).to_equal(2)
expect(execution.offload.row_ids[1]).to_equal(0)
expect(execution.offload.row_ids[2]).to_equal(3)
```

</details>

#### should replace SSD projected COUNT after native materialized candidates match

- Require native timing and SSD materialized row agreement for QueryBuilder count
- var query = QueryBuilder for table
-  filter by
-  order by
- qo ssd materialization
- gpu wdb queue initial
- gpu wdb device backend
- qo budget
   - Expected: execution.count equals `3`
   - Expected: execution.offload.execution.validation_reason equals `production-gpu-row-match`


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Require native timing and SSD materialized row agreement for QueryBuilder count")
var query = QueryBuilder.for_table(qo_table())
    .filter_by("status", CompareOp.Eq, "Open")
    .order_by("score", false)
val execution = query.count_with_ssd_materialized_projection_device_validated(
    qo_ssd_materialization([2, 0, 3]),
    gpu_wdb_queue_initial(4),
    gpu_wdb_device_backend("cuda", 9, ["gpu_db_columnar_scan_batch"], true, "cuda-device-0"),
    9,
    true,
    qo_budget(),
    [2, 0, 3],
    120,
    210,
    64,
    "cuda-event"
)

expect(execution.count).to_equal(3)
expect(db_storage_offload_used_gpu(execution.offload.execution)).to_be(true)
expect(execution.offload.execution.cpu_authoritative).to_be(false)
expect(execution.offload.execution.gpu_candidate_validated).to_be(true)
expect(execution.offload.execution.validation_reason).to_equal("production-gpu-row-match")
expect(execution.offload.device_execution.device_result.production_device_claim).to_be(true)
```

</details>

#### should keep SSD projected SUM on CPU when native materialized rows mismatch

- Reject native SSD aggregate replacement when materialized rows differ from QueryBuilder rows
- var query = QueryBuilder for table
-  filter by
-  order by
- qo ssd materialization
- gpu wdb queue initial
- gpu wdb device backend
- qo budget
   - Expected: execution.sum equals `90`
   - Expected: execution.offload.execution.dispatch_target equals `cpu_fallback`
   - Expected: execution.offload.execution.validation_reason equals `production-ssd-sum-mismatch`


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Reject native SSD aggregate replacement when materialized rows differ from QueryBuilder rows")
var query = QueryBuilder.for_table(qo_table())
    .filter_by("status", CompareOp.Eq, "Open")
    .order_by("score", false)
val execution = query.sum_i64_with_ssd_materialized_projection_device_validated(
    "score",
    qo_ssd_materialization([2, 0, 1]),
    gpu_wdb_queue_initial(4),
    gpu_wdb_device_backend("cuda", 9, ["gpu_db_columnar_scan_batch"], true, "cuda-device-0"),
    9,
    true,
    qo_budget(),
    [2, 0, 1],
    120,
    210,
    64,
    "cuda-event"
)

expect(execution.sum).to_equal(90)
expect(db_storage_offload_used_gpu(execution.offload.execution)).to_be(false)
expect(execution.offload.execution.dispatch_target).to_equal("cpu_fallback")
expect(execution.offload.execution.cpu_authoritative).to_be(true)
expect(execution.offload.execution.gpu_candidate_validated).to_be(false)
expect(execution.offload.execution.validation_reason).to_equal("production-ssd-sum-mismatch")
expect(execution.offload.device_execution.device_result.production_device_claim).to_be(true)
```

</details>

#### should replace SSD projected AVG after native materialized candidates match

- Require native timing and SSD materialized row agreement for QueryBuilder AVG
- var query = QueryBuilder for table
-  filter by
-  order by
- qo ssd materialization
- gpu wdb queue initial
- gpu wdb device backend
- qo budget
   - Expected: execution.value equals `30`
   - Expected: execution.offload.execution.validation_reason equals `production-gpu-row-match`


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Require native timing and SSD materialized row agreement for QueryBuilder AVG")
var query = QueryBuilder.for_table(qo_table())
    .filter_by("status", CompareOp.Eq, "Open")
    .order_by("score", false)
val execution = query.avg_i64_with_ssd_materialized_projection_device_validated(
    "score",
    qo_ssd_materialization([2, 0, 3]),
    gpu_wdb_queue_initial(4),
    gpu_wdb_device_backend("cuda", 9, ["gpu_db_columnar_scan_batch"], true, "cuda-device-0"),
    9,
    true,
    qo_budget(),
    [2, 0, 3],
    120,
    210,
    64,
    "cuda-event"
)

expect(execution.value).to_equal(30)
expect(db_storage_offload_used_gpu(execution.offload.execution)).to_be(true)
expect(execution.offload.execution.cpu_authoritative).to_be(false)
expect(execution.offload.execution.gpu_candidate_validated).to_be(true)
expect(execution.offload.execution.validation_reason).to_equal("production-gpu-row-match")
expect(execution.offload.device_execution.device_result.production_device_claim).to_be(true)
```

</details>

#### should keep SSD projected AVG on CPU when native materialized rows mismatch

- Reject native SSD AVG replacement when materialized rows differ from QueryBuilder rows
- var query = QueryBuilder for table
-  filter by
-  order by
- qo ssd materialization
- gpu wdb queue initial
- gpu wdb device backend
- qo budget
   - Expected: execution.value equals `30`
   - Expected: execution.offload.execution.dispatch_target equals `cpu_fallback`
   - Expected: execution.offload.execution.validation_reason equals `production-ssd-avg-mismatch`


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Reject native SSD AVG replacement when materialized rows differ from QueryBuilder rows")
var query = QueryBuilder.for_table(qo_table())
    .filter_by("status", CompareOp.Eq, "Open")
    .order_by("score", false)
val execution = query.avg_i64_with_ssd_materialized_projection_device_validated(
    "score",
    qo_ssd_materialization([2, 0, 1]),
    gpu_wdb_queue_initial(4),
    gpu_wdb_device_backend("cuda", 9, ["gpu_db_columnar_scan_batch"], true, "cuda-device-0"),
    9,
    true,
    qo_budget(),
    [2, 0, 1],
    120,
    210,
    64,
    "cuda-event"
)

expect(execution.value).to_equal(30)
expect(db_storage_offload_used_gpu(execution.offload.execution)).to_be(false)
expect(execution.offload.execution.dispatch_target).to_equal("cpu_fallback")
expect(execution.offload.execution.cpu_authoritative).to_be(true)
expect(execution.offload.execution.gpu_candidate_validated).to_be(false)
expect(execution.offload.execution.validation_reason).to_equal("production-ssd-avg-mismatch")
expect(execution.offload.device_execution.device_result.production_device_claim).to_be(true)
```

</details>

#### should replace SSD projected MIN after native materialized candidates match

- Require native timing and SSD materialized row agreement for QueryBuilder MIN
- var query = QueryBuilder for table
-  filter by
-  order by
- qo ssd materialization
- gpu wdb queue initial
- gpu wdb device backend
- qo budget
   - Expected: execution.value equals `20`
   - Expected: execution.offload.execution.validation_reason equals `production-gpu-row-match`


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Require native timing and SSD materialized row agreement for QueryBuilder MIN")
var query = QueryBuilder.for_table(qo_table())
    .filter_by("status", CompareOp.Eq, "Open")
    .order_by("score", false)
val execution = query.min_i64_with_ssd_materialized_projection_device_validated(
    "score",
    qo_ssd_materialization([2, 0, 3]),
    gpu_wdb_queue_initial(4),
    gpu_wdb_device_backend("cuda", 9, ["gpu_db_columnar_scan_batch"], true, "cuda-device-0"),
    9,
    true,
    qo_budget(),
    [2, 0, 3],
    120,
    210,
    64,
    "cuda-event"
)

expect(execution.value).to_equal(20)
expect(db_storage_offload_used_gpu(execution.offload.execution)).to_be(true)
expect(execution.offload.execution.cpu_authoritative).to_be(false)
expect(execution.offload.execution.gpu_candidate_validated).to_be(true)
expect(execution.offload.execution.validation_reason).to_equal("production-gpu-row-match")
expect(execution.offload.device_execution.device_result.production_device_claim).to_be(true)
```

</details>

#### should replace SSD projected MAX after native materialized candidates match

- Require native timing and SSD materialized row agreement for QueryBuilder MAX
- var query = QueryBuilder for table
-  filter by
-  order by
- qo ssd materialization
- gpu wdb queue initial
- gpu wdb device backend
- qo budget
   - Expected: execution.value equals `40`
   - Expected: execution.offload.execution.validation_reason equals `production-gpu-row-match`


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Require native timing and SSD materialized row agreement for QueryBuilder MAX")
var query = QueryBuilder.for_table(qo_table())
    .filter_by("status", CompareOp.Eq, "Open")
    .order_by("score", false)
val execution = query.max_i64_with_ssd_materialized_projection_device_validated(
    "score",
    qo_ssd_materialization([2, 0, 3]),
    gpu_wdb_queue_initial(4),
    gpu_wdb_device_backend("cuda", 9, ["gpu_db_columnar_scan_batch"], true, "cuda-device-0"),
    9,
    true,
    qo_budget(),
    [2, 0, 3],
    120,
    210,
    64,
    "cuda-event"
)

expect(execution.value).to_equal(40)
expect(db_storage_offload_used_gpu(execution.offload.execution)).to_be(true)
expect(execution.offload.execution.cpu_authoritative).to_be(false)
expect(execution.offload.execution.gpu_candidate_validated).to_be(true)
expect(execution.offload.execution.validation_reason).to_equal("production-gpu-row-match")
expect(execution.offload.device_execution.device_result.production_device_claim).to_be(true)
```

</details>

#### should keep SSD projected MAX on CPU when native materialized rows mismatch

- Reject native SSD MAX replacement when materialized rows differ from QueryBuilder rows
- var query = QueryBuilder for table
-  filter by
-  order by
- qo ssd materialization
- gpu wdb queue initial
- gpu wdb device backend
- qo budget
   - Expected: execution.value equals `40`
   - Expected: execution.offload.execution.dispatch_target equals `cpu_fallback`
   - Expected: execution.offload.execution.validation_reason equals `production-ssd-max-mismatch`


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Reject native SSD MAX replacement when materialized rows differ from QueryBuilder rows")
var query = QueryBuilder.for_table(qo_table())
    .filter_by("status", CompareOp.Eq, "Open")
    .order_by("score", false)
val execution = query.max_i64_with_ssd_materialized_projection_device_validated(
    "score",
    qo_ssd_materialization([2, 0, 1]),
    gpu_wdb_queue_initial(4),
    gpu_wdb_device_backend("cuda", 9, ["gpu_db_columnar_scan_batch"], true, "cuda-device-0"),
    9,
    true,
    qo_budget(),
    [2, 0, 1],
    120,
    210,
    64,
    "cuda-event"
)

expect(execution.value).to_equal(40)
expect(db_storage_offload_used_gpu(execution.offload.execution)).to_be(false)
expect(execution.offload.execution.dispatch_target).to_equal("cpu_fallback")
expect(execution.offload.execution.cpu_authoritative).to_be(true)
expect(execution.offload.execution.gpu_candidate_validated).to_be(false)
expect(execution.offload.execution.validation_reason).to_equal("production-ssd-max-mismatch")
expect(execution.offload.device_execution.device_result.production_device_claim).to_be(true)
```

</details>

#### should keep SUM on CPU when SSD projected candidates mismatch

- Reject SSD projected aggregate values when candidate row IDs mismatch
- var query = QueryBuilder for table
-  filter by
-  order by
- qo ssd materialization
- gpu wdb queue initial
- gpu wdb library with targets
- qo budget
   - Expected: execution.sum equals `90`
   - Expected: execution.offload.dispatch_target equals `cpu_fallback`
   - Expected: execution.offload.reason equals `gpu-cpu-row-mismatch`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Reject SSD projected aggregate values when candidate row IDs mismatch")
var query = QueryBuilder.for_table(qo_table())
    .filter_by("status", CompareOp.Eq, "Open")
    .order_by("score", false)
val execution = query.sum_i64_with_ssd_materialized_projection(
    "score",
    qo_ssd_materialization([2, 0, 3]),
    gpu_wdb_queue_initial(4),
    gpu_wdb_library_with_targets("cuda", 1, ["gpu_db_columnar_scan_batch"]),
    true,
    true,
    qo_budget(),
    [2, 99, 3]
)

expect(execution.sum).to_equal(90)
expect(db_storage_offload_used_gpu(execution.offload)).to_be(false)
expect(execution.offload.dispatch_target).to_equal("cpu_fallback")
expect(execution.offload.reason).to_equal("gpu-cpu-row-mismatch")
expect(execution.offload.gpu_candidate_validated).to_be(false)
```

</details>

#### should keep COUNT on CPU when SSD projected candidates mismatch

- Reject SSD projected count values when candidate row IDs mismatch
- var query = QueryBuilder for table
-  filter by
-  order by
- qo ssd materialization
- gpu wdb queue initial
- gpu wdb library with targets
- qo budget
   - Expected: execution.count equals `3`
   - Expected: execution.offload.dispatch_target equals `cpu_fallback`
   - Expected: execution.offload.reason equals `gpu-cpu-row-mismatch`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Reject SSD projected count values when candidate row IDs mismatch")
var query = QueryBuilder.for_table(qo_table())
    .filter_by("status", CompareOp.Eq, "Open")
    .order_by("score", false)
val execution = query.count_with_ssd_materialized_projection(
    qo_ssd_materialization([2, 0, 3]),
    gpu_wdb_queue_initial(4),
    gpu_wdb_library_with_targets("cuda", 1, ["gpu_db_columnar_scan_batch"]),
    true,
    true,
    qo_budget(),
    [2, 99, 3]
)

expect(execution.count).to_equal(3)
expect(db_storage_offload_used_gpu(execution.offload)).to_be(false)
expect(execution.offload.dispatch_target).to_equal("cpu_fallback")
expect(execution.offload.reason).to_equal("gpu-cpu-row-mismatch")
expect(execution.offload.gpu_candidate_validated).to_be(false)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 31 |
| Active scenarios | 31 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** [doc/02_requirements/feature/gpu_web_db_offload.md](doc/02_requirements/feature/gpu_web_db_offload.md)
- **Plan:** [doc/03_plan/agent_tasks/gpu_web_db_offload_impl_status.md](doc/03_plan/agent_tasks/gpu_web_db_offload_impl_status.md)
- **Design:** [doc/05_design/gpu_web_db_offload.md](doc/05_design/gpu_web_db_offload.md)


</details>
