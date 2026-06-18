# DB Storage Mode GPU Offload

> These scenarios verify the DB-server-facing storage mode facade. It routes RAM-only, SSD-accelerated, NoSQL document, and vector-search workloads through the shared registry-gated GPU queue while preserving CPU results as authoritative.

<!-- sdn-diagram:id=storage_mode_offload_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=storage_mode_offload_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

storage_mode_offload_spec -> std
storage_mode_offload_spec -> nogc_sync_mut
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=storage_mode_offload_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 26 | 26 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# DB Storage Mode GPU Offload

These scenarios verify the DB-server-facing storage mode facade. It routes RAM-only, SSD-accelerated, NoSQL document, and vector-search workloads through the shared registry-gated GPU queue while preserving CPU results as authoritative.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Requirements | doc/02_requirements/feature/gpu_web_db_offload.md |
| Plan | doc/03_plan/agent_tasks/gpu_web_db_offload_impl_status.md |
| Design | doc/05_design/gpu_web_db_offload.md |
| Research | N/A |
| Source | `test/01_unit/lib/nogc_sync_mut/database/storage_mode_offload_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

These scenarios verify the DB-server-facing storage mode facade. It routes
RAM-only, SSD-accelerated, NoSQL document, and vector-search workloads through
the shared registry-gated GPU queue while preserving CPU results as
authoritative.

## Requirements

**Requirements:** doc/02_requirements/feature/gpu_web_db_offload.md

- RAM-only mode may offload scan/filter/project batches.
- SSD-accelerated mode must require current WAL generation evidence.
- NoSQL document mode keeps metadata filtering CPU-owned.
- Vector mode may offload vector-search batches while returning CPU result IDs.

## Plan

**Plan:** doc/03_plan/agent_tasks/gpu_web_db_offload_impl_status.md

## Design

**Design:** doc/05_design/gpu_web_db_offload.md

## Research

**Research:** N/A

## Examples

DB server code can call `db_storage_execute_rows`,
`db_storage_execute_documents`, or `db_storage_execute_vector` after CPU
planning has produced authoritative fallback results.

## Scenarios

### DB storage mode GPU offload facade

#### should dispatch RAM-only scan batches through the columnar target

- Route RAM-only scan/filter/project through the row batch adapter
- gpu wdb queue initial
- storage budget
   - Expected: execution.dispatch_target equals `gpu_db_columnar_scan_batch`
   - Expected: execution.row_ids.len() equals `2`
   - Expected: execution.profile.data_path equals `GpuWdbCoarseDataPath.GpuResidentBatch`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Route RAM-only scan/filter/project through the row batch adapter")
val registry = gpu_wdb_library_with_targets("cuda", 1, ["gpu_db_columnar_scan_batch"])
val execution = db_storage_execute_rows(
    DbStorageOffloadMode.RamOnly,
    DbStorageOffloadWorkload.ScanFilterProject,
    128,
    64,
    gpu_wdb_queue_initial(4),
    registry,
    true,
    true,
    true,
    storage_budget(),
    [1, 2]
)
expect(db_storage_offload_used_gpu(execution)).to_be(true)
expect(execution.dispatch_target).to_equal("gpu_db_columnar_scan_batch")
expect(execution.row_ids.len()).to_equal(2)
expect(execution.cpu_authoritative).to_be(true)
expect(execution.profile.data_path).to_equal(GpuWdbCoarseDataPath.GpuResidentBatch)
expect(execution.profile.gpu_resident_allowed).to_be(true)
expect(db_storage_profile_allows_gpu(execution)).to_be(true)
```

</details>

#### should validate matching RAM row GPU candidates before accepting evidence

- Compare GPU row-id candidates against the CPU oracle
- gpu wdb queue initial
- storage budget
   - Expected: execution.validation_reason equals `gpu-cpu-row-match`
   - Expected: execution.row_ids[1] equals `2`
   - Expected: execution.profile.data_path equals `GpuWdbCoarseDataPath.GpuResidentBatch`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Compare GPU row-id candidates against the CPU oracle")
val registry = gpu_wdb_library_with_targets("cuda", 1, ["gpu_db_columnar_scan_batch"])
val execution = db_storage_execute_rows_validated(
    DbStorageOffloadMode.RamOnly,
    DbStorageOffloadWorkload.ScanFilterProject,
    128,
    64,
    gpu_wdb_queue_initial(4),
    registry,
    true,
    true,
    true,
    storage_budget(),
    [1, 2],
    [1, 2]
)
expect(db_storage_offload_used_gpu(execution)).to_be(true)
expect(execution.gpu_candidate_validated).to_be(true)
expect(execution.validation_reason).to_equal("gpu-cpu-row-match")
expect(execution.row_ids[1]).to_equal(2)
expect(execution.profile.data_path).to_equal(GpuWdbCoarseDataPath.GpuResidentBatch)
```

</details>

#### should replace CPU row authority after measured native row candidates match

- Require production device evidence and CPU-oracle agreement before replacement
- gpu wdb queue initial
- gpu wdb device backend
- storage budget
   - Expected: execution.execution.validation_reason equals `production-gpu-row-match`
   - Expected: execution.execution.row_ids[1] equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Require production device evidence and CPU-oracle agreement before replacement")
val execution = db_storage_execute_rows_with_device_backend_validated(
    DbStorageOffloadMode.RamOnly,
    DbStorageOffloadWorkload.ScanFilterProject,
    128,
    64,
    gpu_wdb_queue_initial(4),
    gpu_wdb_device_backend("cuda", 5, ["gpu_db_columnar_scan_batch"], true, "cuda-device-0"),
    true,
    5,
    true,
    storage_budget(),
    [1, 2],
    [1, 2],
    100,
    190,
    53,
    "cuda-event"
)
expect(db_storage_offload_used_gpu(execution.execution)).to_be(true)
expect(execution.execution.cpu_authoritative).to_be(false)
expect(execution.execution.gpu_candidate_validated).to_be(true)
expect(execution.execution.validation_reason).to_equal("production-gpu-row-match")
expect(execution.execution.row_ids[1]).to_equal(2)
expect(execution.device_execution.device_result.production_device_claim).to_be(true)
```

</details>

#### should reject measured native row candidates that differ from CPU rows

- Keep CPU authority when a measured GPU candidate disagrees
- gpu wdb queue initial
- gpu wdb device backend
- storage budget
   - Expected: execution.execution.dispatch_target equals `cpu_fallback`
   - Expected: execution.execution.validation_reason equals `production-gpu-row-mismatch`
   - Expected: execution.execution.row_ids[1] equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Keep CPU authority when a measured GPU candidate disagrees")
val execution = db_storage_execute_rows_with_device_backend_validated(
    DbStorageOffloadMode.RamOnly,
    DbStorageOffloadWorkload.ScanFilterProject,
    128,
    64,
    gpu_wdb_queue_initial(4),
    gpu_wdb_device_backend("cuda", 5, ["gpu_db_columnar_scan_batch"], true, "cuda-device-0"),
    true,
    5,
    true,
    storage_budget(),
    [1, 2],
    [1, 3],
    100,
    190,
    53,
    "cuda-event"
)
expect(db_storage_offload_used_gpu(execution.execution)).to_be(false)
expect(execution.execution.dispatch_target).to_equal("cpu_fallback")
expect(execution.execution.cpu_authoritative).to_be(true)
expect(execution.execution.validation_reason).to_equal("production-gpu-row-mismatch")
expect(execution.execution.row_ids[1]).to_equal(2)
expect(execution.device_execution.device_result.production_device_claim).to_be(true)
```

</details>

#### should not replace CPU row authority for perf-only device backends

- Require native device timing before GPU candidates can replace CPU rows
- gpu wdb queue initial
- gpu wdb device backend
- storage budget
   - Expected: execution.execution.validation_reason equals `production-device-not-measured`
   - Expected: execution.execution.row_ids[1] equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Require native device timing before GPU candidates can replace CPU rows")
val execution = db_storage_execute_rows_with_device_backend_validated(
    DbStorageOffloadMode.RamOnly,
    DbStorageOffloadWorkload.ScanFilterProject,
    128,
    64,
    gpu_wdb_queue_initial(4),
    gpu_wdb_device_backend("host-safe-mock", 5, ["gpu_db_columnar_scan_batch"], false, "mock-device"),
    true,
    5,
    true,
    storage_budget(),
    [1, 2],
    [1, 2],
    100,
    190,
    53,
    "mock-timer"
)
expect(db_storage_offload_used_gpu(execution.execution)).to_be(false)
expect(execution.execution.cpu_authoritative).to_be(true)
expect(execution.execution.validation_reason).to_equal("production-device-not-measured")
expect(execution.execution.row_ids[1]).to_equal(2)
expect(execution.device_execution.device_result.production_device_claim).to_be(false)
```

</details>

#### should replace SSD materialized row authority after measured native row candidates match

- Run DBFS materialized scan rows through the strict native backend gate
- storage clean materialized scan
- gpu wdb queue initial
- gpu wdb device backend
- storage budget
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
step("Run DBFS materialized scan rows through the strict native backend gate")
val execution = db_storage_execute_ssd_materialized_scan_with_device_backend_validated(
    storage_clean_materialized_scan(),
    gpu_wdb_queue_initial(4),
    gpu_wdb_device_backend("cuda", 5, ["gpu_db_columnar_scan_batch"], true, "cuda-device-0"),
    5,
    true,
    storage_budget(),
    [12, 34],
    100,
    190,
    53,
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

#### should reject measured native SSD row candidates that differ from materialized rows

- Keep DBFS materialized row IDs authoritative when native candidates mismatch
- storage clean materialized scan
- gpu wdb queue initial
- gpu wdb device backend
- storage budget
   - Expected: execution.execution.dispatch_target equals `cpu_fallback`
   - Expected: execution.execution.mode equals `DbStorageOffloadMode.SsdAccelerated`
   - Expected: execution.execution.validation_reason equals `production-gpu-row-mismatch`
   - Expected: execution.execution.row_ids[0] equals `12`
   - Expected: execution.execution.row_ids[1] equals `34`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Keep DBFS materialized row IDs authoritative when native candidates mismatch")
val execution = db_storage_execute_ssd_materialized_scan_with_device_backend_validated(
    storage_clean_materialized_scan(),
    gpu_wdb_queue_initial(4),
    gpu_wdb_device_backend("cuda", 5, ["gpu_db_columnar_scan_batch"], true, "cuda-device-0"),
    5,
    true,
    storage_budget(),
    [12, 35],
    100,
    190,
    53,
    "cuda-event"
)
expect(db_storage_offload_used_gpu(execution.execution)).to_be(false)
expect(execution.execution.dispatch_target).to_equal("cpu_fallback")
expect(execution.execution.mode).to_equal(DbStorageOffloadMode.SsdAccelerated)
expect(execution.execution.cpu_authoritative).to_be(true)
expect(execution.execution.validation_reason).to_equal("production-gpu-row-mismatch")
expect(execution.execution.row_ids[0]).to_equal(12)
expect(execution.execution.row_ids[1]).to_equal(34)
expect(execution.device_execution.device_result.production_device_claim).to_be(true)
```

</details>

#### should not replace SSD row authority for perf-only device backends

- Require measured native timing before SSD materialized row replacement
- storage clean materialized scan
- gpu wdb queue initial
- gpu wdb device backend
- storage budget
   - Expected: execution.execution.mode equals `DbStorageOffloadMode.SsdAccelerated`
   - Expected: execution.execution.profile.data_path equals `GpuWdbCoarseDataPath.SsdStagedBatch`
   - Expected: execution.execution.validation_reason equals `production-device-not-measured`
   - Expected: execution.execution.row_ids[0] equals `12`
   - Expected: execution.execution.row_ids[1] equals `34`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Require measured native timing before SSD materialized row replacement")
val execution = db_storage_execute_ssd_materialized_scan_with_device_backend_validated(
    storage_clean_materialized_scan(),
    gpu_wdb_queue_initial(4),
    gpu_wdb_device_backend("host-safe-mock", 5, ["gpu_db_columnar_scan_batch"], false, "mock-device"),
    5,
    true,
    storage_budget(),
    [12, 34],
    100,
    190,
    53,
    "mock-timer"
)
expect(db_storage_offload_used_gpu(execution.execution)).to_be(false)
expect(execution.execution.mode).to_equal(DbStorageOffloadMode.SsdAccelerated)
expect(execution.execution.profile.data_path).to_equal(GpuWdbCoarseDataPath.SsdStagedBatch)
expect(execution.execution.cpu_authoritative).to_be(true)
expect(execution.execution.validation_reason).to_equal("production-device-not-measured")
expect(execution.execution.row_ids[0]).to_equal(12)
expect(execution.execution.row_ids[1]).to_equal(34)
expect(execution.device_execution.device_result.production_device_claim).to_be(false)
```

</details>

#### should reject mismatched RAM row GPU candidates

- Fall back to CPU when GPU row-id candidates differ from CPU rows
- gpu wdb queue initial
- storage budget
   - Expected: execution.dispatch_target equals `cpu_fallback`
   - Expected: execution.reason equals `gpu-cpu-row-mismatch`
   - Expected: execution.row_ids[0] equals `1`
   - Expected: execution.profile.data_path equals `GpuWdbCoarseDataPath.GpuResidentBatch`


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Fall back to CPU when GPU row-id candidates differ from CPU rows")
val registry = gpu_wdb_library_with_targets("cuda", 1, ["gpu_db_columnar_scan_batch"])
val execution = db_storage_execute_rows_validated(
    DbStorageOffloadMode.RamOnly,
    DbStorageOffloadWorkload.ScanFilterProject,
    128,
    64,
    gpu_wdb_queue_initial(4),
    registry,
    true,
    true,
    true,
    storage_budget(),
    [1, 2],
    [1, 3]
)
expect(db_storage_offload_used_gpu(execution)).to_be(false)
expect(execution.dispatch_target).to_equal("cpu_fallback")
expect(execution.reason).to_equal("gpu-cpu-row-mismatch")
expect(execution.gpu_candidate_validated).to_be(false)
expect(execution.row_ids[0]).to_equal(1)
expect(execution.profile.data_path).to_equal(GpuWdbCoarseDataPath.GpuResidentBatch)
expect(db_storage_profile_allows_gpu(execution)).to_be(false)
```

</details>

#### should keep SSD batches on CPU when WAL generation is stale

- Require WAL generation freshness before SSD GPU dispatch
- gpu wdb queue initial
- storage budget
   - Expected: execution.reason equals `stale-generation`
   - Expected: execution.row_ids[0] equals `3`
   - Expected: execution.profile.data_path equals `GpuWdbCoarseDataPath.SsdStagedBatch`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Require WAL generation freshness before SSD GPU dispatch")
val registry = gpu_wdb_library_with_targets("cuda", 1, ["gpu_db_columnar_scan_batch"])
val execution = db_storage_execute_rows(
    DbStorageOffloadMode.SsdAccelerated,
    DbStorageOffloadWorkload.ScanFilterProject,
    128,
    64,
    gpu_wdb_queue_initial(4),
    registry,
    true,
    false,
    true,
    storage_budget(),
    [3]
)
expect(db_storage_offload_used_gpu(execution)).to_be(false)
expect(execution.reason).to_equal("stale-generation")
expect(execution.row_ids[0]).to_equal(3)
expect(execution.profile.data_path).to_equal(GpuWdbCoarseDataPath.SsdStagedBatch)
expect(execution.profile.cpu_durability_path).to_be(true)
expect(db_storage_profile_allows_gpu(execution)).to_be(false)
```

</details>

#### should dispatch SSD batches when durable WAL generation is fresh

- Allow SSD scan/filter/project only after freshness evidence is current
- gpu wdb queue initial
- storage budget
   - Expected: execution.dispatch_target equals `gpu_db_columnar_scan_batch`
   - Expected: execution.row_ids.len() equals `2`
   - Expected: execution.profile.data_path equals `GpuWdbCoarseDataPath.SsdStagedBatch`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Allow SSD scan/filter/project only after freshness evidence is current")
val registry = gpu_wdb_library_with_targets("cuda", 1, ["gpu_db_columnar_scan_batch"])
val execution = db_storage_execute_rows(
    DbStorageOffloadMode.SsdAccelerated,
    DbStorageOffloadWorkload.ScanFilterProject,
    128,
    64,
    gpu_wdb_queue_initial(4),
    registry,
    true,
    true,
    true,
    storage_budget(),
    [3, 4]
)
expect(db_storage_offload_used_gpu(execution)).to_be(true)
expect(execution.dispatch_target).to_equal("gpu_db_columnar_scan_batch")
expect(execution.row_ids.len()).to_equal(2)
expect(execution.cpu_authoritative).to_be(true)
expect(execution.profile.data_path).to_equal(GpuWdbCoarseDataPath.SsdStagedBatch)
expect(execution.profile.cpu_durability_path).to_be(true)
expect(db_storage_profile_allows_gpu(execution)).to_be(true)
```

</details>

#### should validate fresh SSD row GPU candidates

- Require both WAL freshness and CPU-oracle row candidate agreement
- gpu wdb queue initial
- storage budget
   - Expected: execution.validation_reason equals `gpu-cpu-row-match`
   - Expected: execution.profile.data_path equals `GpuWdbCoarseDataPath.SsdStagedBatch`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Require both WAL freshness and CPU-oracle row candidate agreement")
val registry = gpu_wdb_library_with_targets("cuda", 1, ["gpu_db_columnar_scan_batch"])
val execution = db_storage_execute_rows_validated(
    DbStorageOffloadMode.SsdAccelerated,
    DbStorageOffloadWorkload.ScanFilterProject,
    128,
    64,
    gpu_wdb_queue_initial(4),
    registry,
    true,
    true,
    true,
    storage_budget(),
    [3, 4],
    [3, 4]
)
expect(db_storage_offload_used_gpu(execution)).to_be(true)
expect(execution.gpu_candidate_validated).to_be(true)
expect(execution.validation_reason).to_equal("gpu-cpu-row-match")
expect(execution.profile.data_path).to_equal(GpuWdbCoarseDataPath.SsdStagedBatch)
```

</details>

#### should dispatch NoSQL document batches only with CPU-owned metadata

- Route NoSQL document filters through the document adapter
- gpu wdb queue initial
- storage budget
   - Expected: execution.dispatch_target equals `gpu_db_document_filter_batch`
   - Expected: execution.document_ids.len() equals `2`
   - Expected: execution.profile.data_path equals `GpuWdbCoarseDataPath.GpuIndexBatch`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Route NoSQL document filters through the document adapter")
val registry = gpu_wdb_library_with_targets("cuda", 1, ["gpu_db_document_filter_batch"])
val execution = db_storage_execute_documents(
    64,
    128,
    true,
    gpu_wdb_queue_initial(4),
    registry,
    true,
    true,
    true,
    storage_budget(),
    ["doc-1", "doc-2"]
)
expect(db_storage_offload_used_gpu(execution)).to_be(true)
expect(execution.dispatch_target).to_equal("gpu_db_document_filter_batch")
expect(execution.document_ids.len()).to_equal(2)
expect(execution.profile.data_path).to_equal(GpuWdbCoarseDataPath.GpuIndexBatch)
expect(execution.profile.cpu_durability_path).to_be(true)
expect(db_storage_profile_allows_gpu(execution)).to_be(true)
```

</details>

#### should validate matching document GPU candidates

- Compare document-filter GPU candidates with CPU-owned metadata results
- gpu wdb queue initial
- storage budget
   - Expected: execution.validation_reason equals `gpu-cpu-document-match`
   - Expected: execution.document_ids[0] equals `doc-1`
   - Expected: execution.profile.data_path equals `GpuWdbCoarseDataPath.GpuIndexBatch`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Compare document-filter GPU candidates with CPU-owned metadata results")
val registry = gpu_wdb_library_with_targets("cuda", 1, ["gpu_db_document_filter_batch"])
val execution = db_storage_execute_documents_validated(
    64,
    128,
    true,
    gpu_wdb_queue_initial(4),
    registry,
    true,
    true,
    true,
    storage_budget(),
    ["doc-1", "doc-2"],
    ["doc-1", "doc-2"]
)
expect(db_storage_offload_used_gpu(execution)).to_be(true)
expect(execution.gpu_candidate_validated).to_be(true)
expect(execution.validation_reason).to_equal("gpu-cpu-document-match")
expect(execution.document_ids[0]).to_equal("doc-1")
expect(execution.profile.data_path).to_equal(GpuWdbCoarseDataPath.GpuIndexBatch)
```

</details>

#### should reject mismatched document GPU candidates

- Fall back to CPU when document candidate IDs differ
- gpu wdb queue initial
- storage budget
   - Expected: execution.dispatch_target equals `cpu_fallback`
   - Expected: execution.reason equals `gpu-cpu-document-mismatch`
   - Expected: execution.document_ids[1] equals `doc-2`
   - Expected: execution.profile.data_path equals `GpuWdbCoarseDataPath.GpuIndexBatch`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Fall back to CPU when document candidate IDs differ")
val registry = gpu_wdb_library_with_targets("cuda", 1, ["gpu_db_document_filter_batch"])
val execution = db_storage_execute_documents_validated(
    64,
    128,
    true,
    gpu_wdb_queue_initial(4),
    registry,
    true,
    true,
    true,
    storage_budget(),
    ["doc-1", "doc-2"],
    ["doc-1", "doc-3"]
)
expect(db_storage_offload_used_gpu(execution)).to_be(false)
expect(execution.dispatch_target).to_equal("cpu_fallback")
expect(execution.reason).to_equal("gpu-cpu-document-mismatch")
expect(execution.gpu_candidate_validated).to_be(false)
expect(execution.document_ids[1]).to_equal("doc-2")
expect(execution.profile.data_path).to_equal(GpuWdbCoarseDataPath.GpuIndexBatch)
expect(db_storage_profile_allows_gpu(execution)).to_be(false)
```

</details>

#### should reject NoSQL document offload when metadata filtering is GPU-owned

- Keep document metadata filtering in the CPU path
- gpu wdb queue initial
- storage budget
   - Expected: execution.reason equals `metadata-filter-must-stay-cpu-owned`
   - Expected: execution.document_ids[0] equals `doc-1`
   - Expected: execution.profile.data_path equals `GpuWdbCoarseDataPath.GpuIndexBatch`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Keep document metadata filtering in the CPU path")
val registry = gpu_wdb_library_with_targets("cuda", 1, ["gpu_db_document_filter_batch"])
val execution = db_storage_execute_documents(
    64,
    128,
    false,
    gpu_wdb_queue_initial(4),
    registry,
    true,
    true,
    true,
    storage_budget(),
    ["doc-1"]
)
expect(db_storage_offload_used_gpu(execution)).to_be(false)
expect(execution.reason).to_equal("metadata-filter-must-stay-cpu-owned")
expect(execution.document_ids[0]).to_equal("doc-1")
expect(execution.profile.data_path).to_equal(GpuWdbCoarseDataPath.GpuIndexBatch)
```

</details>

#### should replace RAM document authority after measured native document candidates match

- Expose RAM NoSQL document native replacement through the storage facade
- gpu wdb queue initial
- gpu wdb device backend
- storage budget
   - Expected: execution.execution.validation_reason equals `production-gpu-document-match`
   - Expected: execution.execution.reason equals `production-gpu-document-match`
   - Expected: execution.execution.document_ids[1] equals `doc-2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Expose RAM NoSQL document native replacement through the storage facade")
val execution = db_storage_execute_documents_with_device_backend_validated(
    64,
    128,
    true,
    gpu_wdb_queue_initial(4),
    gpu_wdb_device_backend("cuda", 7, ["gpu_db_document_filter_batch"], true, "cuda-device-0"),
    true,
    7,
    true,
    storage_budget(),
    ["doc-1", "doc-2"],
    ["doc-1", "doc-2"],
    100,
    190,
    57,
    "cuda-event"
)
expect(db_storage_offload_used_gpu(execution.execution)).to_be(true)
expect(execution.execution.cpu_authoritative).to_be(false)
expect(execution.execution.gpu_candidate_validated).to_be(true)
expect(execution.execution.validation_reason).to_equal("production-gpu-document-match")
expect(execution.execution.reason).to_equal("production-gpu-document-match")
expect(execution.execution.document_ids[1]).to_equal("doc-2")
expect(execution.device_result.production_device_claim).to_be(true)
```

</details>

#### should keep RAM document authority when measured native document candidates mismatch

- Reject RAM NoSQL document replacement when candidate IDs differ
- gpu wdb queue initial
- gpu wdb device backend
- storage budget
   - Expected: execution.execution.dispatch_target equals `cpu_fallback`
   - Expected: execution.execution.reason equals `production-gpu-document-mismatch`
   - Expected: execution.execution.document_ids[1] equals `doc-2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Reject RAM NoSQL document replacement when candidate IDs differ")
val execution = db_storage_execute_documents_with_device_backend_validated(
    64,
    128,
    true,
    gpu_wdb_queue_initial(4),
    gpu_wdb_device_backend("cuda", 7, ["gpu_db_document_filter_batch"], true, "cuda-device-0"),
    true,
    7,
    true,
    storage_budget(),
    ["doc-1", "doc-2"],
    ["doc-1", "doc-3"],
    100,
    190,
    57,
    "cuda-event"
)
expect(db_storage_offload_used_gpu(execution.execution)).to_be(false)
expect(execution.execution.dispatch_target).to_equal("cpu_fallback")
expect(execution.execution.cpu_authoritative).to_be(true)
expect(execution.execution.reason).to_equal("production-gpu-document-mismatch")
expect(execution.execution.document_ids[1]).to_equal("doc-2")
expect(execution.device_result.production_device_claim).to_be(true)
```

</details>

#### should route saved SSD NoSQL documents through the storage facade

- Let DB storage callers offload durable SSD document metadata filters
- file delete
- var collection = NoSqlSsdDocumentCollection create
- collection insert
- collection insert
- gpu wdb queue initial
- gpu wdb library with targets
- storage budget
   - Expected: execution.dispatch_target equals `gpu_db_document_filter_batch`
   - Expected: execution.document_ids[0] equals `doc-1`
   - Expected: execution.profile.data_path equals `GpuWdbCoarseDataPath.GpuIndexBatch`


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Let DB storage callers offload durable SSD document metadata filters")
val path = "/tmp/simple-db-storage-ssd-nosql-documents.sdn"
file_delete(path)
var collection = NoSqlSsdDocumentCollection.create(path)
collection.insert("doc-1", 1024, {"kind": "invoice"})
collection.insert("doc-2", 1024, {"kind": "note"})
expect(collection.save()).to_be(true)

val loaded = NoSqlSsdDocumentCollection.open(path)
val execution = db_storage_execute_ssd_documents(
    loaded,
    "kind",
    "invoice",
    gpu_wdb_queue_initial(4),
    gpu_wdb_library_with_targets("cuda", 1, ["gpu_db_document_filter_batch"]),
    true,
    true,
    storage_budget()
)
expect(db_storage_offload_used_gpu(execution)).to_be(true)
expect(execution.dispatch_target).to_equal("gpu_db_document_filter_batch")
expect(execution.document_ids[0]).to_equal("doc-1")
expect(execution.profile.data_path).to_equal(GpuWdbCoarseDataPath.GpuIndexBatch)
expect(execution.cpu_authoritative).to_be(true)
val _deleted = file_delete(path)
```

</details>

#### should replace CPU document authority after measured native document candidates match

- Require production device evidence and CPU-oracle agreement before document replacement
- file delete
- var collection = NoSqlSsdDocumentCollection create
- collection insert
- collection insert
- gpu wdb queue initial
- gpu wdb device backend
- storage budget
   - Expected: execution.execution.validation_reason equals `production-gpu-document-match`
   - Expected: execution.execution.document_ids[0] equals `doc-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 30 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Require production device evidence and CPU-oracle agreement before document replacement")
val path = "/tmp/simple-db-storage-ssd-nosql-documents-device.sdn"
file_delete(path)
var collection = NoSqlSsdDocumentCollection.create(path)
collection.insert("doc-1", 1024, {"kind": "invoice"})
collection.insert("doc-2", 1024, {"kind": "note"})
expect(collection.save()).to_be(true)
val loaded = NoSqlSsdDocumentCollection.open(path)
val execution = db_storage_execute_ssd_documents_with_device_backend_validated(
    loaded,
    "kind",
    "invoice",
    gpu_wdb_queue_initial(4),
    gpu_wdb_device_backend("cuda", 7, ["gpu_db_document_filter_batch"], true, "cuda-device-0"),
    7,
    true,
    storage_budget(),
    ["doc-1"],
    100,
    190,
    59,
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

#### should reject measured native document candidates that differ from CPU documents

- Keep CPU authority when a measured document GPU candidate disagrees
- file delete
- var collection = NoSqlSsdDocumentCollection create
- collection insert
- collection insert
- gpu wdb queue initial
- gpu wdb device backend
- storage budget
   - Expected: execution.execution.dispatch_target equals `cpu_fallback`
   - Expected: execution.execution.validation_reason equals `production-gpu-document-mismatch`
   - Expected: execution.execution.document_ids[0] equals `doc-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 30 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Keep CPU authority when a measured document GPU candidate disagrees")
val path = "/tmp/simple-db-storage-ssd-nosql-documents-device-mismatch.sdn"
file_delete(path)
var collection = NoSqlSsdDocumentCollection.create(path)
collection.insert("doc-1", 1024, {"kind": "invoice"})
collection.insert("doc-2", 1024, {"kind": "note"})
expect(collection.save()).to_be(true)
val loaded = NoSqlSsdDocumentCollection.open(path)
val execution = db_storage_execute_ssd_documents_with_device_backend_validated(
    loaded,
    "kind",
    "invoice",
    gpu_wdb_queue_initial(4),
    gpu_wdb_device_backend("cuda", 7, ["gpu_db_document_filter_batch"], true, "cuda-device-0"),
    7,
    true,
    storage_budget(),
    ["doc-2"],
    100,
    190,
    59,
    "cuda-event"
)
expect(db_storage_offload_used_gpu(execution.execution)).to_be(false)
expect(execution.execution.dispatch_target).to_equal("cpu_fallback")
expect(execution.execution.cpu_authoritative).to_be(true)
expect(execution.execution.validation_reason).to_equal("production-gpu-document-mismatch")
expect(execution.execution.document_ids[0]).to_equal("doc-1")
expect(execution.device_result.production_device_claim).to_be(true)
val _deleted = file_delete(path)
```

</details>

#### should not replace CPU document authority for perf-only device backends

- Require native device timing before document GPU candidates can replace CPU documents
- file delete
- var collection = NoSqlSsdDocumentCollection create
- collection insert
- collection insert
- gpu wdb queue initial
- gpu wdb device backend
- storage budget
   - Expected: execution.execution.validation_reason equals `production-device-not-measured`
   - Expected: execution.execution.document_ids[0] equals `doc-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Require native device timing before document GPU candidates can replace CPU documents")
val path = "/tmp/simple-db-storage-ssd-nosql-documents-device-mock.sdn"
file_delete(path)
var collection = NoSqlSsdDocumentCollection.create(path)
collection.insert("doc-1", 1024, {"kind": "invoice"})
collection.insert("doc-2", 1024, {"kind": "note"})
expect(collection.save()).to_be(true)
val loaded = NoSqlSsdDocumentCollection.open(path)
val execution = db_storage_execute_ssd_documents_with_device_backend_validated(
    loaded,
    "kind",
    "invoice",
    gpu_wdb_queue_initial(4),
    gpu_wdb_device_backend("host-safe-mock", 7, ["gpu_db_document_filter_batch"], false, "mock-device"),
    7,
    true,
    storage_budget(),
    ["doc-1"],
    100,
    190,
    59,
    "mock-timer"
)
expect(db_storage_offload_used_gpu(execution.execution)).to_be(false)
expect(execution.execution.cpu_authoritative).to_be(true)
expect(execution.execution.validation_reason).to_equal("production-device-not-measured")
expect(execution.execution.document_ids[0]).to_equal("doc-1")
expect(execution.device_result.production_device_claim).to_be(false)
val _deleted = file_delete(path)
```

</details>

#### should keep unsaved SSD NoSQL storage facade changes on CPU

- Require durable SSD document generation before facade GPU dispatch
- file delete
- var collection = NoSqlSsdDocumentCollection create
- collection insert
- gpu wdb queue initial
- gpu wdb library with targets
- storage budget
   - Expected: execution.dispatch_target equals `cpu_fallback`
   - Expected: execution.reason equals `stale-generation`
   - Expected: execution.document_ids[0] equals `doc-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Require durable SSD document generation before facade GPU dispatch")
val path = "/tmp/simple-db-storage-ssd-nosql-documents-stale.sdn"
file_delete(path)
var collection = NoSqlSsdDocumentCollection.create(path)
collection.insert("doc-1", 128, {"kind": "invoice"})
val execution = db_storage_execute_ssd_documents(
    collection,
    "kind",
    "invoice",
    gpu_wdb_queue_initial(4),
    gpu_wdb_library_with_targets("cuda", 1, ["gpu_db_document_filter_batch"]),
    true,
    true,
    storage_budget()
)
expect(db_storage_offload_used_gpu(execution)).to_be(false)
expect(execution.dispatch_target).to_equal("cpu_fallback")
expect(execution.reason).to_equal("stale-generation")
expect(execution.document_ids[0]).to_equal("doc-1")
expect(execution.cpu_authoritative).to_be(true)
val _deleted = file_delete(path)
```

</details>

#### should dispatch vector search through the vector target

- Route vector search while preserving CPU search result ids
- gpu wdb queue initial
- storage budget
- [vector result
   - Expected: execution.dispatch_target equals `gpu_db_vector_search_batch`
   - Expected: execution.vector_ids[0] equals `vec-1`
   - Expected: execution.profile.data_path equals `GpuWdbCoarseDataPath.GpuIndexBatch`
   - Expected: execution.profile.stream_count equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Route vector search while preserving CPU search result ids")
val registry = gpu_wdb_library_with_targets("cuda", 1, ["gpu_db_vector_search_batch"])
val execution = db_storage_execute_vector(
    DistanceMetric.Cosine,
    128,
    32,
    true,
    gpu_wdb_queue_initial(4),
    registry,
    true,
    true,
    true,
    storage_budget(),
    [vector_result("vec-1", 0.1), vector_result("vec-2", 0.2)]
)
expect(db_storage_offload_used_gpu(execution)).to_be(true)
expect(execution.dispatch_target).to_equal("gpu_db_vector_search_batch")
expect(execution.vector_ids[0]).to_equal("vec-1")
expect(execution.profile.data_path).to_equal(GpuWdbCoarseDataPath.GpuIndexBatch)
expect(execution.profile.stream_count).to_equal(4)
expect(db_storage_profile_allows_gpu(execution)).to_be(true)
```

</details>

#### should validate vector search candidates at the storage facade

- Allow vector candidate replacement only after result ID agreement
- gpu wdb queue initial
- storage budget
- [vector result
- [vector result
   - Expected: execution.validation_reason equals `gpu-cpu-vector-match`
   - Expected: execution.vector_ids[1] equals `vec-2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Allow vector candidate replacement only after result ID agreement")
val registry = gpu_wdb_library_with_targets("cuda", 1, ["gpu_db_vector_search_batch"])
val execution = db_storage_execute_vector_validated(
    DistanceMetric.Cosine,
    128,
    32,
    true,
    gpu_wdb_queue_initial(4),
    registry,
    true,
    true,
    true,
    storage_budget(),
    [vector_result("vec-1", 0.1), vector_result("vec-2", 0.2)],
    [vector_result("vec-1", 0.1), vector_result("vec-2", 0.2)]
)
expect(db_storage_offload_used_gpu(execution)).to_be(true)
expect(execution.cpu_authoritative).to_be(false)
expect(execution.gpu_candidate_validated).to_be(true)
expect(execution.validation_reason).to_equal("gpu-cpu-vector-match")
expect(execution.vector_ids[1]).to_equal("vec-2")
```

</details>

#### should reject mismatched vector search candidates at the storage facade

- Keep CPU vector IDs authoritative when GPU candidates disagree
- gpu wdb queue initial
- storage budget
- [vector result
- [vector result
   - Expected: execution.dispatch_target equals `cpu_fallback`
   - Expected: execution.validation_reason equals `gpu-cpu-vector-mismatch`
   - Expected: execution.vector_ids[1] equals `vec-2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Keep CPU vector IDs authoritative when GPU candidates disagree")
val registry = gpu_wdb_library_with_targets("cuda", 1, ["gpu_db_vector_search_batch"])
val execution = db_storage_execute_vector_validated(
    DistanceMetric.Cosine,
    128,
    32,
    true,
    gpu_wdb_queue_initial(4),
    registry,
    true,
    true,
    true,
    storage_budget(),
    [vector_result("vec-1", 0.1), vector_result("vec-2", 0.2)],
    [vector_result("vec-1", 0.1), vector_result("vec-3", 0.3)]
)
expect(db_storage_offload_used_gpu(execution)).to_be(false)
expect(execution.dispatch_target).to_equal("cpu_fallback")
expect(execution.cpu_authoritative).to_be(true)
expect(execution.gpu_candidate_validated).to_be(false)
expect(execution.validation_reason).to_equal("gpu-cpu-vector-mismatch")
expect(execution.vector_ids[1]).to_equal("vec-2")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 26 |
| Active scenarios | 26 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** [doc/02_requirements/feature/gpu_web_db_offload.md](doc/02_requirements/feature/gpu_web_db_offload.md)
- **Plan:** [doc/03_plan/agent_tasks/gpu_web_db_offload_impl_status.md](doc/03_plan/agent_tasks/gpu_web_db_offload_impl_status.md)
- **Design:** [doc/05_design/gpu_web_db_offload.md](doc/05_design/gpu_web_db_offload.md)


</details>
