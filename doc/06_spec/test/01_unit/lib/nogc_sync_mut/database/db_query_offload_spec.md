# DB Query GPU Offload Facade

> These scenarios verify the DB-server-facing query facade that chooses the correct storage-mode offload adapter for RAM-only, SSD-accelerated, NoSQL document, and vector-search query work.

<!-- sdn-diagram:id=db_query_offload_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=db_query_offload_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

db_query_offload_spec -> std
db_query_offload_spec -> nogc_sync_mut
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=db_query_offload_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 31 | 31 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# DB Query GPU Offload Facade

These scenarios verify the DB-server-facing query facade that chooses the correct storage-mode offload adapter for RAM-only, SSD-accelerated, NoSQL document, and vector-search query work.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Requirements | doc/02_requirements/feature/gpu_web_db_offload.md |
| Plan | doc/03_plan/agent_tasks/gpu_web_db_offload_impl_status.md |
| Design | doc/05_design/gpu_web_db_offload.md |
| Research | N/A |
| Source | `test/01_unit/lib/nogc_sync_mut/database/db_query_offload_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

These scenarios verify the DB-server-facing query facade that chooses the
correct storage-mode offload adapter for RAM-only, SSD-accelerated, NoSQL
document, and vector-search query work.

## Requirements

**Requirements:** doc/02_requirements/feature/gpu_web_db_offload.md

- DB server callers can use one query offload entrypoint.
- RAM and SSD row queries route to row batch offload.
- NoSQL document queries route to document batch offload.
- Vector queries route to vector search offload.
- Invalid mode/workload combinations stay CPU authoritative.

## Plan

**Plan:** doc/03_plan/agent_tasks/gpu_web_db_offload_impl_status.md

## Design

**Design:** doc/05_design/gpu_web_db_offload.md

## Research

**Research:** N/A

## Examples

DB server code can build a `DbQueryOffloadRequest` with `db_query_rows`,
`db_query_documents`, or `db_query_vector`, then call
`db_query_offload_execute` with the shared GPU queue and registry.

## Scenarios

### DB query GPU offload facade

#### should dispatch RAM-only row scans through the query facade

- Use one DB server entrypoint for row scan/filter/project batches
- gpu wdb queue initial
- query budget
   - Expected: execution.dispatch_target equals `gpu_db_columnar_scan_batch`
   - Expected: execution.row_ids[0] equals `1`
   - Expected: execution.validation_reason equals `gpu-candidate-not-evaluated`
   - Expected: execution.profile.data_path equals `GpuWdbCoarseDataPath.GpuResidentBatch`


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Use one DB server entrypoint for row scan/filter/project batches")
val registry = gpu_wdb_library_with_targets("cuda", 1, ["gpu_db_columnar_scan_batch"])
val execution = db_query_offload_execute(
    db_query_rows(
        DbStorageOffloadMode.RamOnly,
        DbStorageOffloadWorkload.ScanFilterProject,
        128,
        64,
        true,
        [1, 2]
    ),
    gpu_wdb_queue_initial(2),
    registry,
    true,
    true,
    query_budget()
)
expect(db_storage_offload_used_gpu(execution)).to_be(true)
expect(execution.dispatch_target).to_equal("gpu_db_columnar_scan_batch")
expect(execution.row_ids[0]).to_equal(1)
expect(execution.gpu_candidate_validated).to_be(false)
expect(execution.validation_reason).to_equal("gpu-candidate-not-evaluated")
expect(execution.profile.data_path).to_equal(GpuWdbCoarseDataPath.GpuResidentBatch)
expect(db_storage_profile_allows_gpu(execution)).to_be(true)
```

</details>

#### should keep SSD row queries on CPU when generation is stale

- Preserve WAL freshness before SSD GPU dispatch
- gpu wdb queue initial
- query budget
   - Expected: execution.reason equals `stale-generation`
   - Expected: execution.row_ids[0] equals `7`
   - Expected: execution.validation_reason equals `gpu-candidate-not-evaluated`
   - Expected: execution.profile.data_path equals `GpuWdbCoarseDataPath.SsdStagedBatch`


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Preserve WAL freshness before SSD GPU dispatch")
val registry = gpu_wdb_library_with_targets("cuda", 1, ["gpu_db_columnar_scan_batch"])
val execution = db_query_offload_execute(
    db_query_rows(
        DbStorageOffloadMode.SsdAccelerated,
        DbStorageOffloadWorkload.ScanFilterProject,
        128,
        64,
        false,
        [7]
    ),
    gpu_wdb_queue_initial(2),
    registry,
    true,
    true,
    query_budget()
)
expect(db_storage_offload_used_gpu(execution)).to_be(false)
expect(execution.reason).to_equal("stale-generation")
expect(execution.row_ids[0]).to_equal(7)
expect(execution.gpu_candidate_validated).to_be(false)
expect(execution.validation_reason).to_equal("gpu-candidate-not-evaluated")
expect(execution.profile.data_path).to_equal(GpuWdbCoarseDataPath.SsdStagedBatch)
expect(db_storage_profile_allows_gpu(execution)).to_be(false)
```

</details>

#### should replace CPU query rows only after native device candidates match

- Accept query-level row replacement only from measured native device evidence
- gpu wdb queue initial
- gpu wdb device backend
- query budget
   - Expected: execution.execution.validation_reason equals `production-gpu-row-match`
   - Expected: execution.execution.row_ids[0] equals `1`
   - Expected: execution.execution.row_ids[1] equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Accept query-level row replacement only from measured native device evidence")
val execution = db_query_offload_execute_rows_device_validated(
    db_query_rows(
        DbStorageOffloadMode.RamOnly,
        DbStorageOffloadWorkload.ScanFilterProject,
        128,
        64,
        true,
        [1, 2]
    ),
    gpu_wdb_queue_initial(2),
    gpu_wdb_device_backend("cuda", 3, ["gpu_db_columnar_scan_batch"], true, "cuda-device-0"),
    3,
    true,
    query_budget(),
    [1, 2],
    100,
    188,
    51,
    "cuda-event"
)
expect(execution.execution.gpu_dispatched).to_be(true)
expect(execution.execution.cpu_authoritative).to_be(false)
expect(execution.execution.gpu_candidate_validated).to_be(true)
expect(execution.execution.validation_reason).to_equal("production-gpu-row-match")
expect(execution.execution.row_ids[0]).to_equal(1)
expect(execution.execution.row_ids[1]).to_equal(2)
expect(execution.device_execution.device_result.production_device_claim).to_be(true)
```

</details>

#### should keep CPU query rows authoritative when native device candidates mismatch

- Reject query-level row replacement when measured native candidates differ
- gpu wdb queue initial
- gpu wdb device backend
- query budget
   - Expected: execution.execution.dispatch_target equals `cpu_fallback`
   - Expected: execution.execution.validation_reason equals `production-gpu-row-mismatch`
   - Expected: execution.execution.row_ids[0] equals `1`
   - Expected: execution.execution.row_ids[1] equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Reject query-level row replacement when measured native candidates differ")
val execution = db_query_offload_execute_rows_device_validated(
    db_query_rows(
        DbStorageOffloadMode.RamOnly,
        DbStorageOffloadWorkload.ScanFilterProject,
        128,
        64,
        true,
        [1, 2]
    ),
    gpu_wdb_queue_initial(2),
    gpu_wdb_device_backend("cuda", 3, ["gpu_db_columnar_scan_batch"], true, "cuda-device-0"),
    3,
    true,
    query_budget(),
    [1, 3],
    100,
    188,
    51,
    "cuda-event"
)
expect(execution.execution.gpu_dispatched).to_be(false)
expect(execution.execution.cpu_authoritative).to_be(true)
expect(execution.execution.gpu_candidate_validated).to_be(false)
expect(execution.execution.dispatch_target).to_equal("cpu_fallback")
expect(execution.execution.validation_reason).to_equal("production-gpu-row-mismatch")
expect(execution.execution.row_ids[0]).to_equal(1)
expect(execution.execution.row_ids[1]).to_equal(2)
expect(execution.device_execution.device_result.production_device_claim).to_be(true)
```

</details>

#### should keep perf-only query device runs from replacing CPU rows

- Require production native device claims before query rows stop being CPU authoritative
- gpu wdb queue initial
- gpu wdb device backend
- query budget
   - Expected: execution.execution.validation_reason equals `production-device-not-measured`
   - Expected: execution.execution.row_ids[0] equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Require production native device claims before query rows stop being CPU authoritative")
val execution = db_query_offload_execute_rows_device_validated(
    db_query_rows(
        DbStorageOffloadMode.RamOnly,
        DbStorageOffloadWorkload.ScanFilterProject,
        128,
        64,
        true,
        [1, 2]
    ),
    gpu_wdb_queue_initial(2),
    gpu_wdb_device_backend("mock", 3, ["gpu_db_columnar_scan_batch"], false, "mock-device"),
    3,
    true,
    query_budget(),
    [1, 2],
    100,
    188,
    51,
    "mock-clock"
)
expect(execution.execution.gpu_dispatched).to_be(false)
expect(execution.execution.cpu_authoritative).to_be(true)
expect(execution.execution.gpu_candidate_validated).to_be(false)
expect(execution.execution.validation_reason).to_equal("production-device-not-measured")
expect(execution.execution.row_ids[0]).to_equal(1)
expect(execution.device_execution.device_result.production_device_claim).to_be(false)
```

</details>

#### should dispatch SSD row queries from DBFS snapshot evidence

- Use DBFS-owned SSD freshness at the query facade boundary
- query clean ssd snapshot
- gpu wdb queue initial
- query budget
   - Expected: execution.mode equals `DbStorageOffloadMode.SsdAccelerated`
   - Expected: execution.dispatch_target equals `gpu_db_columnar_scan_batch`
   - Expected: execution.row_ids[0] equals `7`
   - Expected: execution.row_ids[1] equals `8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Use DBFS-owned SSD freshness at the query facade boundary")
val registry = gpu_wdb_library_with_targets("cuda", 1, ["gpu_db_columnar_scan_batch"])
val execution = db_query_offload_execute_for_ssd_snapshot(
    query_clean_ssd_snapshot(128, 64),
    DbStorageOffloadWorkload.ScanFilterProject,
    gpu_wdb_queue_initial(2),
    registry,
    true,
    true,
    query_budget(),
    [7, 8]
)
expect(db_storage_offload_used_gpu(execution)).to_be(true)
expect(execution.mode).to_equal(DbStorageOffloadMode.SsdAccelerated)
expect(execution.dispatch_target).to_equal("gpu_db_columnar_scan_batch")
expect(execution.row_ids[0]).to_equal(7)
expect(execution.row_ids[1]).to_equal(8)
```

</details>

#### should dispatch SSD scan queries from snapshot-derived row ids

- Use the DBFS-owned scan facade without caller-provided CPU row ids
- query clean ssd snapshot
- gpu wdb queue initial
- query budget
   - Expected: execution.mode equals `DbStorageOffloadMode.SsdAccelerated`
   - Expected: execution.dispatch_target equals `gpu_db_columnar_scan_batch`
   - Expected: execution.row_ids.len() equals `3`
   - Expected: execution.row_ids[0] equals `0`
   - Expected: execution.row_ids[1] equals `1`
   - Expected: execution.row_ids[2] equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Use the DBFS-owned scan facade without caller-provided CPU row ids")
val registry = gpu_wdb_library_with_targets("cuda", 1, ["gpu_db_columnar_scan_batch"])
val execution = db_query_offload_execute_ssd_snapshot_scan(
    query_clean_ssd_snapshot(3, 64),
    gpu_wdb_queue_initial(2),
    registry,
    true,
    true,
    query_budget()
)
expect(db_storage_offload_used_gpu(execution)).to_be(true)
expect(execution.mode).to_equal(DbStorageOffloadMode.SsdAccelerated)
expect(execution.dispatch_target).to_equal("gpu_db_columnar_scan_batch")
expect(execution.row_ids.len()).to_equal(3)
expect(execution.row_ids[0]).to_equal(0)
expect(execution.row_ids[1]).to_equal(1)
expect(execution.row_ids[2]).to_equal(2)
```

</details>

#### should validate SSD materialized scan GPU candidates

- Compare GPU candidates against DBFS page-cursor materialized rows
- query clean materialized scan
- gpu wdb queue initial
- query budget
   - Expected: execution.validation_reason equals `gpu-cpu-row-match`
   - Expected: execution.row_ids[0] equals `12`
   - Expected: execution.row_ids[1] equals `34`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Compare GPU candidates against DBFS page-cursor materialized rows")
val registry = gpu_wdb_library_with_targets("cuda", 1, ["gpu_db_columnar_scan_batch"])
val execution = db_query_offload_execute_ssd_materialized_scan_validated(
    query_clean_materialized_scan(),
    gpu_wdb_queue_initial(2),
    registry,
    true,
    true,
    query_budget(),
    [12, 34]
)
expect(db_storage_offload_used_gpu(execution)).to_be(true)
expect(execution.gpu_candidate_validated).to_be(true)
expect(execution.validation_reason).to_equal("gpu-cpu-row-match")
expect(execution.row_ids[0]).to_equal(12)
expect(execution.row_ids[1]).to_equal(34)
```

</details>

#### should reject mismatched SSD materialized scan GPU candidates

- Keep DBFS page-cursor materialized rows authoritative on mismatch
- query clean materialized scan
- gpu wdb queue initial
- query budget
   - Expected: execution.dispatch_target equals `cpu_fallback`
   - Expected: execution.reason equals `gpu-cpu-row-mismatch`
   - Expected: execution.row_ids[0] equals `12`
   - Expected: execution.row_ids[1] equals `34`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Keep DBFS page-cursor materialized rows authoritative on mismatch")
val registry = gpu_wdb_library_with_targets("cuda", 1, ["gpu_db_columnar_scan_batch"])
val execution = db_query_offload_execute_ssd_materialized_scan_validated(
    query_clean_materialized_scan(),
    gpu_wdb_queue_initial(2),
    registry,
    true,
    true,
    query_budget(),
    [12, 35]
)
expect(db_storage_offload_used_gpu(execution)).to_be(false)
expect(execution.dispatch_target).to_equal("cpu_fallback")
expect(execution.reason).to_equal("gpu-cpu-row-mismatch")
expect(execution.gpu_candidate_validated).to_be(false)
expect(execution.row_ids[0]).to_equal(12)
expect(execution.row_ids[1]).to_equal(34)
```

</details>

#### should validate production SSD materialized scan candidates through the query facade

- Let measured native SSD scan candidates replace CPU output only after CPU oracle validation
- query clean materialized scan
- gpu wdb queue initial
- gpu wdb device backend
- query budget
   - Expected: execution.execution.mode equals `DbStorageOffloadMode.SsdAccelerated`
   - Expected: execution.execution.profile.data_path equals `GpuWdbCoarseDataPath.SsdStagedBatch`
   - Expected: execution.execution.validation_reason equals `production-gpu-row-match`
   - Expected: execution.execution.row_ids[0] equals `12`
   - Expected: execution.execution.row_ids[1] equals `34`


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Let measured native SSD scan candidates replace CPU output only after CPU oracle validation")
val execution = db_query_offload_execute_ssd_materialized_scan_device_validated(
    query_clean_materialized_scan(),
    gpu_wdb_queue_initial(2),
    gpu_wdb_device_backend("cuda", 8, ["gpu_db_columnar_scan_batch"], true, "cuda-device-0"),
    8,
    true,
    query_budget(),
    [12, 34],
    100,
    190,
    61,
    "cuda-event"
)
expect(db_storage_offload_used_gpu(execution.execution)).to_be(true)
expect(execution.execution.mode).to_equal(DbStorageOffloadMode.SsdAccelerated)
expect(execution.execution.profile.data_path).to_equal(GpuWdbCoarseDataPath.SsdStagedBatch)
expect(execution.execution.cpu_authoritative).to_be(false)
expect(execution.execution.gpu_candidate_validated).to_be(true)
expect(execution.execution.validation_reason).to_equal("production-gpu-row-match")
expect(execution.execution.row_ids[0]).to_equal(12)
expect(execution.execution.row_ids[1]).to_equal(34)
expect(execution.device_execution.device_result.production_device_claim).to_be(true)
```

</details>

#### should reject mismatched production SSD materialized scan candidates through the query facade

- Keep DBFS materialized scan rows authoritative when a native candidate disagrees
- query clean materialized scan
- gpu wdb queue initial
- gpu wdb device backend
- query budget
   - Expected: execution.execution.dispatch_target equals `cpu_fallback`
   - Expected: execution.execution.validation_reason equals `production-gpu-row-mismatch`
   - Expected: execution.execution.row_ids[0] equals `12`
   - Expected: execution.execution.row_ids[1] equals `34`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Keep DBFS materialized scan rows authoritative when a native candidate disagrees")
val execution = db_query_offload_execute_ssd_materialized_scan_device_validated(
    query_clean_materialized_scan(),
    gpu_wdb_queue_initial(2),
    gpu_wdb_device_backend("cuda", 8, ["gpu_db_columnar_scan_batch"], true, "cuda-device-0"),
    8,
    true,
    query_budget(),
    [12, 35],
    100,
    190,
    61,
    "cuda-event"
)
expect(db_storage_offload_used_gpu(execution.execution)).to_be(false)
expect(execution.execution.dispatch_target).to_equal("cpu_fallback")
expect(execution.execution.cpu_authoritative).to_be(true)
expect(execution.execution.gpu_candidate_validated).to_be(false)
expect(execution.execution.validation_reason).to_equal("production-gpu-row-mismatch")
expect(execution.execution.row_ids[0]).to_equal(12)
expect(execution.execution.row_ids[1]).to_equal(34)
expect(execution.device_execution.device_result.production_device_claim).to_be(true)
```

</details>

#### should reject perf-only SSD materialized scan candidates through the query facade

- Require production native timing before SSD scan candidates replace CPU output
- query clean materialized scan
- gpu wdb queue initial
- gpu wdb device backend
- query budget
   - Expected: execution.execution.mode equals `DbStorageOffloadMode.SsdAccelerated`
   - Expected: execution.execution.profile.data_path equals `GpuWdbCoarseDataPath.SsdStagedBatch`
   - Expected: execution.execution.validation_reason equals `production-device-not-measured`
   - Expected: execution.execution.row_ids[0] equals `12`
   - Expected: execution.execution.row_ids[1] equals `34`


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Require production native timing before SSD scan candidates replace CPU output")
val execution = db_query_offload_execute_ssd_materialized_scan_device_validated(
    query_clean_materialized_scan(),
    gpu_wdb_queue_initial(2),
    gpu_wdb_device_backend("host-safe-mock", 8, ["gpu_db_columnar_scan_batch"], false, "mock-device"),
    8,
    true,
    query_budget(),
    [12, 34],
    100,
    190,
    61,
    "mock-timer"
)
expect(db_storage_offload_used_gpu(execution.execution)).to_be(false)
expect(execution.execution.mode).to_equal(DbStorageOffloadMode.SsdAccelerated)
expect(execution.execution.profile.data_path).to_equal(GpuWdbCoarseDataPath.SsdStagedBatch)
expect(execution.execution.cpu_authoritative).to_be(true)
expect(execution.execution.gpu_candidate_validated).to_be(false)
expect(execution.execution.validation_reason).to_equal("production-device-not-measured")
expect(execution.execution.row_ids[0]).to_equal(12)
expect(execution.execution.row_ids[1]).to_equal(34)
expect(execution.device_execution.device_result.production_device_claim).to_be(false)
```

</details>

#### should dispatch SSD join aggregate queries from DBFS snapshot evidence

- Use the DBFS snapshot query path for SSD SQL aggregate work
- query clean ssd snapshot
- gpu wdb queue initial
- query budget
   - Expected: execution.mode equals `DbStorageOffloadMode.SsdAccelerated`
   - Expected: execution.workload equals `DbStorageOffloadWorkload.JoinAggregate`
   - Expected: execution.dispatch_target equals `gpu_db_join_aggregate_batch`
   - Expected: execution.row_ids[2] equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Use the DBFS snapshot query path for SSD SQL aggregate work")
val registry = gpu_wdb_library_with_targets("cuda", 1, ["gpu_db_join_aggregate_batch"])
val execution = db_query_offload_execute_for_ssd_snapshot(
    query_clean_ssd_snapshot(128, 64),
    DbStorageOffloadWorkload.JoinAggregate,
    gpu_wdb_queue_initial(2),
    registry,
    true,
    true,
    query_budget(),
    [0, 2, 3]
)
expect(db_storage_offload_used_gpu(execution)).to_be(true)
expect(execution.mode).to_equal(DbStorageOffloadMode.SsdAccelerated)
expect(execution.workload).to_equal(DbStorageOffloadWorkload.JoinAggregate)
expect(execution.dispatch_target).to_equal("gpu_db_join_aggregate_batch")
expect(execution.row_ids[2]).to_equal(3)
```

</details>

#### should keep SSD query facade work on CPU for stale DBFS snapshots

- Dirty DBFS pager state blocks SSD query dispatch
- query dirty ssd snapshot
- gpu wdb queue initial
- query budget
   - Expected: execution.mode equals `DbStorageOffloadMode.SsdAccelerated`
   - Expected: execution.reason equals `stale-generation`
   - Expected: execution.row_ids[0] equals `9`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Dirty DBFS pager state blocks SSD query dispatch")
val registry = gpu_wdb_library_with_targets("cuda", 1, ["gpu_db_columnar_scan_batch"])
val execution = db_query_offload_execute_for_ssd_snapshot(
    query_dirty_ssd_snapshot(128, 64),
    DbStorageOffloadWorkload.ScanFilterProject,
    gpu_wdb_queue_initial(2),
    registry,
    true,
    true,
    query_budget(),
    [9]
)
expect(db_storage_offload_used_gpu(execution)).to_be(false)
expect(execution.mode).to_equal(DbStorageOffloadMode.SsdAccelerated)
expect(execution.reason).to_equal("stale-generation")
expect(execution.row_ids[0]).to_equal(9)
```

</details>

#### should reject document workloads on the SSD snapshot query path

- Avoid mixing SSD row snapshots with document-filter workloads
- query clean ssd snapshot
- gpu wdb queue initial
- query budget
   - Expected: execution.reason equals `query-mode-workload-mismatch`
   - Expected: execution.row_ids[0] equals `11`
   - Expected: execution.profile.data_path equals `GpuWdbCoarseDataPath.SsdStagedBatch`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Avoid mixing SSD row snapshots with document-filter workloads")
val registry = gpu_wdb_library_with_targets("cuda", 1, ["gpu_db_document_filter_batch"])
val execution = db_query_offload_execute_for_ssd_snapshot(
    query_clean_ssd_snapshot(128, 64),
    DbStorageOffloadWorkload.DocumentFilter,
    gpu_wdb_queue_initial(2),
    registry,
    true,
    true,
    query_budget(),
    [11]
)
expect(db_storage_offload_used_gpu(execution)).to_be(false)
expect(execution.reason).to_equal("query-mode-workload-mismatch")
expect(execution.row_ids[0]).to_equal(11)
expect(execution.profile.data_path).to_equal(GpuWdbCoarseDataPath.SsdStagedBatch)
```

</details>

#### should dispatch NoSQL document queries through document offload

- Use the same query facade for document-filter batches
- db query documents
- gpu wdb queue initial
- query budget
   - Expected: execution.dispatch_target equals `gpu_db_document_filter_batch`
   - Expected: execution.document_ids[1] equals `doc-2`
   - Expected: execution.profile.data_path equals `GpuWdbCoarseDataPath.GpuIndexBatch`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Use the same query facade for document-filter batches")
val registry = gpu_wdb_library_with_targets("cuda", 1, ["gpu_db_document_filter_batch"])
val execution = db_query_offload_execute(
    db_query_documents(64, 128, true, true, ["doc-1", "doc-2"]),
    gpu_wdb_queue_initial(2),
    registry,
    true,
    true,
    query_budget()
)
expect(db_storage_offload_used_gpu(execution)).to_be(true)
expect(execution.dispatch_target).to_equal("gpu_db_document_filter_batch")
expect(execution.document_ids[1]).to_equal("doc-2")
expect(execution.profile.data_path).to_equal(GpuWdbCoarseDataPath.GpuIndexBatch)
expect(db_storage_profile_allows_gpu(execution)).to_be(true)
```

</details>

#### should dispatch saved SSD NoSQL document queries through the query facade

- Use durable document metadata freshness at the DB query boundary
- file delete
- var collection = NoSqlSsdDocumentCollection create
- collection insert
- collection insert
- gpu wdb queue initial
- gpu wdb library with targets
- query budget
   - Expected: execution.dispatch_target equals `gpu_db_document_filter_batch`
   - Expected: execution.document_ids[0] equals `doc-1`
   - Expected: execution.profile.data_path equals `GpuWdbCoarseDataPath.GpuIndexBatch`


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Use durable document metadata freshness at the DB query boundary")
val path = "/tmp/simple-db-query-ssd-nosql-documents.sdn"
file_delete(path)
var collection = NoSqlSsdDocumentCollection.create(path)
collection.insert("doc-1", 128, {"kind": "invoice"})
collection.insert("doc-2", 256, {"kind": "note"})
expect(collection.save()).to_be(true)

val loaded = NoSqlSsdDocumentCollection.open(path)
val execution = db_query_offload_execute_ssd_documents(
    loaded,
    "kind",
    "invoice",
    gpu_wdb_queue_initial(2),
    gpu_wdb_library_with_targets("cuda", 1, ["gpu_db_document_filter_batch"]),
    true,
    true,
    query_budget()
)
expect(db_storage_offload_used_gpu(execution)).to_be(true)
expect(execution.dispatch_target).to_equal("gpu_db_document_filter_batch")
expect(execution.document_ids[0]).to_equal("doc-1")
expect(execution.profile.data_path).to_equal(GpuWdbCoarseDataPath.GpuIndexBatch)
expect(execution.cpu_authoritative).to_be(true)
val _deleted = file_delete(path)
```

</details>

#### should keep unsaved SSD NoSQL query facade changes on CPU

- Block query-level GPU dispatch until SSD NoSQL changes are durable
- file delete
- var collection = NoSqlSsdDocumentCollection create
- collection insert
- gpu wdb queue initial
- gpu wdb library with targets
- query budget
   - Expected: execution.dispatch_target equals `cpu_fallback`
   - Expected: execution.reason equals `stale-generation`
   - Expected: execution.document_ids[0] equals `doc-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Block query-level GPU dispatch until SSD NoSQL changes are durable")
val path = "/tmp/simple-db-query-ssd-nosql-documents-stale.sdn"
file_delete(path)
var collection = NoSqlSsdDocumentCollection.create(path)
collection.insert("doc-1", 128, {"kind": "invoice"})
val execution = db_query_offload_execute_ssd_documents(
    collection,
    "kind",
    "invoice",
    gpu_wdb_queue_initial(2),
    gpu_wdb_library_with_targets("cuda", 1, ["gpu_db_document_filter_batch"]),
    true,
    true,
    query_budget()
)
expect(db_storage_offload_used_gpu(execution)).to_be(false)
expect(execution.dispatch_target).to_equal("cpu_fallback")
expect(execution.reason).to_equal("stale-generation")
expect(execution.document_ids[0]).to_equal("doc-1")
expect(execution.cpu_authoritative).to_be(true)
val _deleted = file_delete(path)
```

</details>

#### should validate production SSD NoSQL document device candidates through the query facade

- Let measured native document candidates replace CPU output only after CPU oracle validation
- file delete
- var collection = NoSqlSsdDocumentCollection create
- collection insert
- collection insert
- gpu wdb queue initial
- gpu wdb device backend
- query budget
   - Expected: execution.execution.validation_reason equals `production-gpu-document-match`
   - Expected: execution.execution.document_ids[0] equals `doc-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 31 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Let measured native document candidates replace CPU output only after CPU oracle validation")
val path = "/tmp/simple-db-query-ssd-nosql-documents-device.sdn"
file_delete(path)
var collection = NoSqlSsdDocumentCollection.create(path)
collection.insert("doc-1", 1024, {"kind": "invoice"})
collection.insert("doc-2", 1024, {"kind": "note"})
expect(collection.save()).to_be(true)

val loaded = NoSqlSsdDocumentCollection.open(path)
val execution = db_query_offload_execute_ssd_documents_device_validated(
    loaded,
    "kind",
    "invoice",
    gpu_wdb_queue_initial(2),
    gpu_wdb_device_backend("cuda", 8, ["gpu_db_document_filter_batch"], true, "cuda-device-0"),
    8,
    true,
    query_budget(),
    ["doc-1"],
    100,
    190,
    61,
    "cuda-event"
)
expect(db_storage_offload_used_gpu(execution.execution)).to_be(true)
expect(execution.execution.cpu_authoritative).to_be(false)
expect(execution.execution.gpu_candidate_validated).to_be(true)
expect(execution.execution.validation_reason).to_equal("production-gpu-document-match")
expect(execution.execution.document_ids[0]).to_equal("doc-1")
expect(execution.device_result.production_device_claim).to_be(true)
val _deleted = file_delete(path)
```

</details>

#### should reject mismatched SSD NoSQL document device candidates through the query facade

- Keep SSD document CPU oracle output authoritative when a native candidate disagrees
- file delete
- var collection = NoSqlSsdDocumentCollection create
- collection insert
- collection insert
- gpu wdb queue initial
- gpu wdb device backend
- query budget
   - Expected: execution.execution.dispatch_target equals `cpu_fallback`
   - Expected: execution.execution.validation_reason equals `production-gpu-document-mismatch`
   - Expected: execution.execution.document_ids[0] equals `doc-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 32 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Keep SSD document CPU oracle output authoritative when a native candidate disagrees")
val path = "/tmp/simple-db-query-ssd-nosql-documents-device-mismatch.sdn"
file_delete(path)
var collection = NoSqlSsdDocumentCollection.create(path)
collection.insert("doc-1", 1024, {"kind": "invoice"})
collection.insert("doc-2", 1024, {"kind": "note"})
expect(collection.save()).to_be(true)

val loaded = NoSqlSsdDocumentCollection.open(path)
val execution = db_query_offload_execute_ssd_documents_device_validated(
    loaded,
    "kind",
    "invoice",
    gpu_wdb_queue_initial(2),
    gpu_wdb_device_backend("cuda", 8, ["gpu_db_document_filter_batch"], true, "cuda-device-0"),
    8,
    true,
    query_budget(),
    ["doc-2"],
    100,
    190,
    61,
    "cuda-event"
)
expect(db_storage_offload_used_gpu(execution.execution)).to_be(false)
expect(execution.execution.dispatch_target).to_equal("cpu_fallback")
expect(execution.execution.cpu_authoritative).to_be(true)
expect(execution.execution.gpu_candidate_validated).to_be(false)
expect(execution.execution.validation_reason).to_equal("production-gpu-document-mismatch")
expect(execution.execution.document_ids[0]).to_equal("doc-1")
expect(execution.device_result.production_device_claim).to_be(true)
val _deleted = file_delete(path)
```

</details>

#### should dispatch vector queries through vector search offload

- Use the same query facade for vector-search batches
- [query vector result
- gpu wdb queue initial
- query budget
   - Expected: execution.dispatch_target equals `gpu_db_vector_search_batch`
   - Expected: execution.vector_ids[0] equals `vec-1`
   - Expected: execution.profile.data_path equals `GpuWdbCoarseDataPath.GpuIndexBatch`
   - Expected: execution.profile.stream_count equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Use the same query facade for vector-search batches")
val registry = gpu_wdb_library_with_targets("cuda", 1, ["gpu_db_vector_search_batch"])
val execution = db_query_offload_execute(
    db_query_vector(
        DistanceMetric.Cosine,
        128,
        32,
        true,
        true,
        [query_vector_result("vec-1", 0.1)]
    ),
    gpu_wdb_queue_initial(2),
    registry,
    true,
    true,
    query_budget()
)
expect(db_storage_offload_used_gpu(execution)).to_be(true)
expect(execution.dispatch_target).to_equal("gpu_db_vector_search_batch")
expect(execution.vector_ids[0]).to_equal("vec-1")
expect(execution.profile.data_path).to_equal(GpuWdbCoarseDataPath.GpuIndexBatch)
expect(execution.profile.stream_count).to_equal(4)
```

</details>

#### should validate vector query candidates through the query facade

- Expose vector result replacement through the DB query boundary
- [query vector result
- gpu wdb queue initial
- query budget
- [query vector result
   - Expected: execution.validation_reason equals `gpu-cpu-vector-match`
   - Expected: execution.vector_ids[1] equals `vec-2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Expose vector result replacement through the DB query boundary")
val registry = gpu_wdb_library_with_targets("cuda", 1, ["gpu_db_vector_search_batch"])
val execution = db_query_offload_execute_vector_validated(
    db_query_vector(
        DistanceMetric.Cosine,
        128,
        32,
        true,
        true,
        [query_vector_result("vec-1", 0.1), query_vector_result("vec-2", 0.2)]
    ),
    gpu_wdb_queue_initial(2),
    registry,
    true,
    true,
    query_budget(),
    [query_vector_result("vec-1", 0.1), query_vector_result("vec-2", 0.2)]
)
expect(db_storage_offload_used_gpu(execution)).to_be(true)
expect(execution.cpu_authoritative).to_be(false)
expect(execution.gpu_candidate_validated).to_be(true)
expect(execution.validation_reason).to_equal("gpu-cpu-vector-match")
expect(execution.vector_ids[1]).to_equal("vec-2")
```

</details>

#### should reject mismatched vector query candidates through the query facade

- Keep query CPU vector output authoritative on candidate mismatch
- [query vector result
- gpu wdb queue initial
- query budget
- [query vector result
   - Expected: execution.dispatch_target equals `cpu_fallback`
   - Expected: execution.validation_reason equals `gpu-cpu-vector-mismatch`
   - Expected: execution.vector_ids[1] equals `vec-2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Keep query CPU vector output authoritative on candidate mismatch")
val registry = gpu_wdb_library_with_targets("cuda", 1, ["gpu_db_vector_search_batch"])
val execution = db_query_offload_execute_vector_validated(
    db_query_vector(
        DistanceMetric.Cosine,
        128,
        32,
        true,
        true,
        [query_vector_result("vec-1", 0.1), query_vector_result("vec-2", 0.2)]
    ),
    gpu_wdb_queue_initial(2),
    registry,
    true,
    true,
    query_budget(),
    [query_vector_result("vec-1", 0.1), query_vector_result("vec-3", 0.3)]
)
expect(db_storage_offload_used_gpu(execution)).to_be(false)
expect(execution.dispatch_target).to_equal("cpu_fallback")
expect(execution.cpu_authoritative).to_be(true)
expect(execution.gpu_candidate_validated).to_be(false)
expect(execution.validation_reason).to_equal("gpu-cpu-vector-mismatch")
expect(execution.vector_ids[1]).to_equal("vec-2")
```

</details>

#### should replace vector query results only after native device candidates match

- Expose measured native vector replacement through the DB query facade
- [query vector result
- gpu wdb queue initial
- gpu wdb device backend
- query budget
- [query vector result
   - Expected: execution.execution.validation_reason equals `production-gpu-vector-match`
   - Expected: execution.execution.vector_ids[1] equals `vec-2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Expose measured native vector replacement through the DB query facade")
val execution = db_query_offload_execute_vector_device_validated(
    db_query_vector(
        DistanceMetric.Cosine,
        128,
        32,
        true,
        true,
        [query_vector_result("vec-1", 0.1), query_vector_result("vec-2", 0.2)]
    ),
    gpu_wdb_queue_initial(2),
    gpu_wdb_device_backend("cuda", 7, ["gpu_db_vector_search_batch"], true, "cuda-device-0"),
    7,
    true,
    query_budget(),
    [query_vector_result("vec-1", 0.1), query_vector_result("vec-2", 0.2)],
    100,
    190,
    58,
    "cuda-event"
)
expect(db_storage_offload_used_gpu(execution.execution)).to_be(true)
expect(execution.execution.cpu_authoritative).to_be(false)
expect(execution.execution.gpu_candidate_validated).to_be(true)
expect(execution.execution.validation_reason).to_equal("production-gpu-vector-match")
expect(execution.execution.vector_ids[1]).to_equal("vec-2")
expect(execution.device_result.production_device_claim).to_be(true)
```

</details>

#### should keep vector query results CPU authoritative when native candidates mismatch

- Reject measured native vector candidates that disagree with CPU IDs
- [query vector result
- gpu wdb queue initial
- gpu wdb device backend
- query budget
- [query vector result
   - Expected: execution.execution.dispatch_target equals `cpu_fallback`
   - Expected: execution.execution.validation_reason equals `production-gpu-vector-mismatch`
   - Expected: execution.execution.vector_ids[1] equals `vec-2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Reject measured native vector candidates that disagree with CPU IDs")
val execution = db_query_offload_execute_vector_device_validated(
    db_query_vector(
        DistanceMetric.Cosine,
        128,
        32,
        true,
        true,
        [query_vector_result("vec-1", 0.1), query_vector_result("vec-2", 0.2)]
    ),
    gpu_wdb_queue_initial(2),
    gpu_wdb_device_backend("cuda", 7, ["gpu_db_vector_search_batch"], true, "cuda-device-0"),
    7,
    true,
    query_budget(),
    [query_vector_result("vec-1", 0.1), query_vector_result("vec-3", 0.3)],
    100,
    190,
    58,
    "cuda-event"
)
expect(db_storage_offload_used_gpu(execution.execution)).to_be(false)
expect(execution.execution.dispatch_target).to_equal("cpu_fallback")
expect(execution.execution.cpu_authoritative).to_be(true)
expect(execution.execution.gpu_candidate_validated).to_be(false)
expect(execution.execution.validation_reason).to_equal("production-gpu-vector-mismatch")
expect(execution.execution.vector_ids[1]).to_equal("vec-2")
expect(execution.device_result.production_device_claim).to_be(true)
```

</details>

#### should keep invalid mode workload pairs on CPU

- Avoid dispatch when a row workload is paired with a document mode
- gpu wdb queue initial
- query budget
   - Expected: execution.reason equals `query-mode-workload-mismatch`
   - Expected: execution.row_ids[0] equals `9`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Avoid dispatch when a row workload is paired with a document mode")
val registry = gpu_wdb_library_with_targets("cuda", 1, ["gpu_db_columnar_scan_batch"])
val request = db_query_rows(
    DbStorageOffloadMode.NoSqlDocument,
    DbStorageOffloadWorkload.ScanFilterProject,
    128,
    64,
    true,
    [9]
)
val execution = db_query_offload_execute(
    request,
    gpu_wdb_queue_initial(2),
    registry,
    true,
    true,
    query_budget()
)
expect(db_query_mode_matches_workload(request.mode, request.workload)).to_be(false)
expect(db_storage_offload_used_gpu(execution)).to_be(false)
expect(execution.reason).to_equal("query-mode-workload-mismatch")
expect(execution.row_ids[0]).to_equal(9)
```

</details>

#### should defer tiny scheduled document queries for batch accumulation

- Use shared scheduler admission before DB query queue mutation
- db query documents
- gpu wdb queue initial
- query budget
   - Expected: execution.dispatch_target equals `gpu_batch_accumulator`
   - Expected: execution.reason equals `batch-too-small-defer`
   - Expected: execution.document_ids[0] equals `doc-small`
   - Expected: execution.profile.data_path equals `GpuWdbCoarseDataPath.GpuIndexBatch`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Use shared scheduler admission before DB query queue mutation")
val registry = gpu_wdb_library_with_targets("cuda", 1, ["gpu_db_document_filter_batch"])
val execution = db_query_offload_execute_scheduled(
    db_query_documents(1, 128, true, true, ["doc-small"]),
    gpu_wdb_queue_initial(2),
    registry,
    true,
    true,
    query_budget(),
    GpuWdbScheduleClass.Batch,
    true
)
expect(db_storage_offload_used_gpu(execution)).to_be(false)
expect(execution.dispatch_target).to_equal("gpu_batch_accumulator")
expect(execution.reason).to_equal("batch-too-small-defer")
expect(execution.document_ids[0]).to_equal("doc-small")
expect(execution.profile.data_path).to_equal(GpuWdbCoarseDataPath.GpuIndexBatch)
```

</details>

#### should add deferred document queries to the reusable accumulator

- Accumulate tiny NoSQL document work while preserving CPU-authoritative IDs
- db query documents
- gpu wdb queue initial
- query budget
- gpu wdb batch accumulator
   - Expected: accumulated.execution.dispatch_target equals `gpu_batch_accumulator`
   - Expected: accumulated.execution.document_ids[0] equals `doc-small`
   - Expected: accumulated.accumulator_result.accumulator.item_count equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Accumulate tiny NoSQL document work while preserving CPU-authoritative IDs")
val registry = gpu_wdb_library_with_targets("cuda", 1, ["gpu_db_document_filter_batch"])
val accumulated = db_query_offload_execute_accumulating(
    db_query_documents(1, 128, true, true, ["doc-small"]),
    gpu_wdb_queue_initial(2),
    registry,
    true,
    true,
    query_budget(),
    GpuWdbScheduleClass.Background,
    gpu_wdb_batch_accumulator(GpuWdbWorkKind.DbDocumentFilter)
)
expect(db_storage_offload_used_gpu(accumulated.execution)).to_be(false)
expect(accumulated.execution.dispatch_target).to_equal("gpu_batch_accumulator")
expect(accumulated.execution.document_ids[0]).to_equal("doc-small")
expect(accumulated.accumulator_result.accepted).to_be(true)
expect(accumulated.accumulator_result.should_flush).to_be(false)
expect(accumulated.accumulator_result.accumulator.item_count).to_equal(1)
```

</details>

#### should not accumulate DB query work that dispatches immediately

- Keep accumulator state unchanged for GPU-worthy DB query batches
- [query vector result
- gpu wdb queue initial
- query budget
- gpu wdb batch accumulator
   - Expected: accumulated.execution.dispatch_target equals `gpu_db_vector_search_batch`
   - Expected: accumulated.accumulator_result.reason equals `query-not-deferred`
   - Expected: accumulated.accumulator_result.accumulator.item_count equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Keep accumulator state unchanged for GPU-worthy DB query batches")
val registry = gpu_wdb_library_with_targets("cuda", 1, ["gpu_db_vector_search_batch"])
val accumulated = db_query_offload_execute_accumulating(
    db_query_vector(
        DistanceMetric.Cosine,
        128,
        32,
        true,
        true,
        [query_vector_result("vec-1", 0.1)]
    ),
    gpu_wdb_queue_initial(2),
    registry,
    true,
    true,
    query_budget(),
    GpuWdbScheduleClass.Batch,
    gpu_wdb_batch_accumulator(GpuWdbWorkKind.DbVectorSearch)
)
expect(db_storage_offload_used_gpu(accumulated.execution)).to_be(true)
expect(accumulated.execution.dispatch_target).to_equal("gpu_db_vector_search_batch")
expect(accumulated.accumulator_result.accepted).to_be(false)
expect(accumulated.accumulator_result.reason).to_equal("query-not-deferred")
expect(accumulated.accumulator_result.accumulator.item_count).to_equal(0)
```

</details>

#### should accumulate tiny join aggregate queries through the DB query facade

- Defer small SQL aggregate work into the shared join/aggregate accumulator
- gpu wdb queue initial
- query budget
- gpu wdb batch accumulator
   - Expected: accumulated.execution.workload equals `DbStorageOffloadWorkload.JoinAggregate`
   - Expected: accumulated.execution.dispatch_target equals `gpu_batch_accumulator`
   - Expected: accumulated.execution.row_ids[0] equals `0`
   - Expected: accumulated.execution.profile.data_path equals `GpuWdbCoarseDataPath.GpuResidentBatch`
   - Expected: accumulated.execution.row_ids[1] equals `2`
   - Expected: accumulated.execution.row_ids[2] equals `3`
   - Expected: accumulated.accumulator_result.accumulator.item_count equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Defer small SQL aggregate work into the shared join/aggregate accumulator")
val registry = gpu_wdb_library_with_targets("cuda", 1, ["gpu_db_join_aggregate_batch"])
val accumulated = db_query_offload_execute_accumulating(
    db_query_rows(
        DbStorageOffloadMode.RamOnly,
        DbStorageOffloadWorkload.JoinAggregate,
        4,
        128,
        true,
        [0, 2, 3]
    ),
    gpu_wdb_queue_initial(2),
    registry,
    true,
    true,
    query_budget(),
    GpuWdbScheduleClass.Background,
    gpu_wdb_batch_accumulator(GpuWdbWorkKind.DbJoinAggregate)
)
expect(db_storage_offload_used_gpu(accumulated.execution)).to_be(false)
expect(accumulated.execution.workload).to_equal(DbStorageOffloadWorkload.JoinAggregate)
expect(accumulated.execution.dispatch_target).to_equal("gpu_batch_accumulator")
expect(accumulated.execution.row_ids[0]).to_equal(0)
expect(accumulated.execution.profile.data_path).to_equal(GpuWdbCoarseDataPath.GpuResidentBatch)
expect(db_storage_profile_allows_gpu(accumulated.execution)).to_be(false)
expect(accumulated.execution.row_ids[1]).to_equal(2)
expect(accumulated.execution.row_ids[2]).to_equal(3)
expect(accumulated.accumulator_result.accepted).to_be(true)
expect(accumulated.accumulator_result.accumulator.item_count).to_equal(4)
```

</details>

#### should return SQL aggregate operator results with reusable offload metadata

- Wrap CPU-authoritative aggregate count output with query offload execution
- gpu wdb queue initial
- query budget
   - Expected: aggregate.operator equals `join_aggregate_count`
   - Expected: aggregate.count equals `3`
   - Expected: aggregate.offload.dispatch_target equals `gpu_db_join_aggregate_batch`
   - Expected: aggregate.offload.profile.data_path equals `GpuWdbCoarseDataPath.GpuResidentBatch`
   - Expected: aggregate.row_ids[0] equals `0`
   - Expected: aggregate.row_ids[1] equals `2`
   - Expected: aggregate.row_ids[2] equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Wrap CPU-authoritative aggregate count output with query offload execution")
val registry = gpu_wdb_library_with_targets("cuda", 1, ["gpu_db_join_aggregate_batch"])
val aggregate = db_query_join_aggregate_count_execute(
    db_query_rows(
        DbStorageOffloadMode.RamOnly,
        DbStorageOffloadWorkload.JoinAggregate,
        128,
        64,
        true,
        [0, 2, 3]
    ),
    3,
    gpu_wdb_queue_initial(2),
    registry,
    true,
    true,
    query_budget()
)
expect(aggregate.operator).to_equal("join_aggregate_count")
expect(aggregate.count).to_equal(3)
expect(db_storage_offload_used_gpu(aggregate.offload)).to_be(true)
expect(aggregate.offload.dispatch_target).to_equal("gpu_db_join_aggregate_batch")
expect(aggregate.offload.cpu_authoritative).to_be(true)
expect(aggregate.offload.profile.data_path).to_equal(GpuWdbCoarseDataPath.GpuResidentBatch)
expect(aggregate.row_ids[0]).to_equal(0)
expect(aggregate.row_ids[1]).to_equal(2)
expect(aggregate.row_ids[2]).to_equal(3)
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
