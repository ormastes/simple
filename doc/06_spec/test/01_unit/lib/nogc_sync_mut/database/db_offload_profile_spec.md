# DB GPU Offload Profiles

> These scenarios verify reusable DB GPU offload profiles. Profiles bundle registry targets, queue defaults, budgets, GPU availability, and CPU fallback policy so DB server code can use consistent RAM-heavy, SSD-accelerated, NoSQL, vector, and CPU-only settings.

<!-- sdn-diagram:id=db_offload_profile_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=db_offload_profile_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

db_offload_profile_spec -> std
db_offload_profile_spec -> nogc_sync_mut
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=db_offload_profile_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 30 | 30 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# DB GPU Offload Profiles

These scenarios verify reusable DB GPU offload profiles. Profiles bundle registry targets, queue defaults, budgets, GPU availability, and CPU fallback policy so DB server code can use consistent RAM-heavy, SSD-accelerated, NoSQL, vector, and CPU-only settings.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Requirements | doc/02_requirements/feature/gpu_web_db_offload.md |
| Plan | doc/03_plan/agent_tasks/gpu_web_db_offload_impl_status.md |
| Design | doc/05_design/gpu_web_db_offload.md |
| Research | N/A |
| Source | `test/01_unit/lib/nogc_sync_mut/database/db_offload_profile_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

These scenarios verify reusable DB GPU offload profiles. Profiles bundle
registry targets, queue defaults, budgets, GPU availability, and CPU fallback
policy so DB server code can use consistent RAM-heavy, SSD-accelerated, NoSQL,
vector, and CPU-only settings.

## Requirements

**Requirements:** doc/02_requirements/feature/gpu_web_db_offload.md

- DB server code can reuse named GPU offload profiles.
- RAM-heavy profiles register row batch targets.
- NoSQL profiles register document targets without pretending row GPU exists.
- All-GPU profiles expose row, document, and vector targets.
- CPU-only profiles preserve authoritative CPU fallback.

## Plan

**Plan:** doc/03_plan/agent_tasks/gpu_web_db_offload_impl_status.md

## Design

**Design:** doc/05_design/gpu_web_db_offload.md

## Research

**Research:** N/A

## Examples

Use `db_offload_profile_all_gpu` for a DB server that can run every coarse DB
batch family, then call `db_offload_profile_execute` with a
`DbQueryOffloadRequest`.

## Scenarios

### DB reusable GPU offload profiles

#### should dispatch RAM-heavy row scans with row GPU targets

- Use the RAM-heavy profile for columnar scan/filter/project
   - Expected: profile.name equals `ram-heavy`
   - Expected: execution.dispatch_target equals `gpu_db_columnar_scan_batch`
   - Expected: execution.profile.data_path equals `GpuWdbCoarseDataPath.GpuResidentBatch`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Use the RAM-heavy profile for columnar scan/filter/project")
val profile = db_offload_profile_ram_heavy("cuda", 1, 4)
val execution = db_offload_profile_execute(
    profile,
    db_query_rows(
        DbStorageOffloadMode.RamOnly,
        DbStorageOffloadWorkload.ScanFilterProject,
        128,
        64,
        true,
        [1]
    )
)
expect(profile.name).to_equal("ram-heavy")
expect(db_storage_offload_used_gpu(execution)).to_be(true)
expect(db_offload_profile_execution_used_gpu(execution)).to_be(true)
expect(db_offload_profile_execution_allows_gpu(execution)).to_be(true)
expect(execution.dispatch_target).to_equal("gpu_db_columnar_scan_batch")
expect(execution.profile.data_path).to_equal(GpuWdbCoarseDataPath.GpuResidentBatch)
```

</details>

#### should advance DB profile queue state across sequential executions

- Return the updated profile so server code keeps queue accounting current
   - Expected: first.profile.queue_state.submitted_count equals `1`
   - Expected: first.profile.queue_state.completed_count equals `1`
   - Expected: first.profile.queue_state.gpu_hit_count equals `1`
   - Expected: second.profile.queue_state.submitted_count equals `2`
   - Expected: second.profile.queue_state.completed_count equals `2`
   - Expected: second.profile.queue_state.gpu_hit_count equals `2`
   - Expected: second.execution.row_ids[0] equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 34 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Return the updated profile so server code keeps queue accounting current")
val profile = db_offload_profile_ram_heavy("cuda", 1, 4)
val first = db_offload_profile_execute_advancing(
    profile,
    db_query_rows(
        DbStorageOffloadMode.RamOnly,
        DbStorageOffloadWorkload.ScanFilterProject,
        128,
        64,
        true,
        [1]
    )
)
val second = db_offload_profile_execute_advancing(
    first.profile,
    db_query_rows(
        DbStorageOffloadMode.RamOnly,
        DbStorageOffloadWorkload.ScanFilterProject,
        128,
        64,
        true,
        [2]
    )
)
expect(db_storage_offload_used_gpu(first.execution)).to_be(true)
expect(db_storage_offload_used_gpu(second.execution)).to_be(true)
expect(first.profile.queue_state.submitted_count).to_equal(1)
expect(first.profile.queue_state.completed_count).to_equal(1)
expect(first.profile.queue_state.gpu_hit_count).to_equal(1)
expect(second.profile.queue_state.submitted_count).to_equal(2)
expect(second.profile.queue_state.completed_count).to_equal(2)
expect(second.profile.queue_state.gpu_hit_count).to_equal(2)
expect(second.execution.row_ids[0]).to_equal(2)
expect(second.execution.cpu_authoritative).to_be(true)
```

</details>

#### should attach strict native device evidence to RAM-heavy row scans

- Run a DB profile row request through the production device backend boundary
   - Expected: executed.execution.row_ids[0] equals `7`
   - Expected: executed.device_result.submission.dispatch_target equals `gpu_db_columnar_scan_batch`
   - Expected: executed.device_result.evidence.device_time_us equals `41`
   - Expected: executed.profile.queue_state.gpu_hit_count equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 32 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Run a DB profile row request through the production device backend boundary")
val profile = db_offload_profile_ram_heavy("cuda", 3, 4)
val backend = gpu_wdb_device_backend(
    "cuda",
    3,
    ["gpu_db_columnar_scan_batch"],
    true,
    "cuda-device-0"
)
val executed = db_offload_profile_execute_device(
    profile,
    db_query_rows(
        DbStorageOffloadMode.RamOnly,
        DbStorageOffloadWorkload.ScanFilterProject,
        128,
        64,
        true,
        [7]
    ),
    backend,
    3,
    100,
    180,
    41,
    "cuda-event"
)
expect(executed.execution.cpu_authoritative).to_be(true)
expect(executed.execution.row_ids[0]).to_equal(7)
expect(executed.device_result.production_device_claim).to_be(true)
expect(executed.device_result.submission.dispatch_target).to_equal("gpu_db_columnar_scan_batch")
expect(executed.device_result.evidence.device_time_us).to_equal(41)
expect(executed.profile.queue_state.gpu_hit_count).to_equal(1)
```

</details>

#### should block DB profile production device claims for perf-only backends

- Keep DB profile device execution strict even when CPU-authoritative output exists
   - Expected: executed.execution.row_ids[0] equals `8`
   - Expected: executed.device_result.submission.dispatch_target equals `cpu_fallback`
   - Expected: executed.device_result.reason equals `gpu-unavailable`


<details>
<summary>Executable SSpec</summary>

Runnable source: 32 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Keep DB profile device execution strict even when CPU-authoritative output exists")
val profile = db_offload_profile_ram_heavy("host-safe-mock", 1, 4)
val backend = gpu_wdb_device_backend(
    "host-safe-mock",
    1,
    ["gpu_db_columnar_scan_batch"],
    false,
    "mock-device"
)
val executed = db_offload_profile_execute_device(
    profile,
    db_query_rows(
        DbStorageOffloadMode.RamOnly,
        DbStorageOffloadWorkload.ScanFilterProject,
        128,
        64,
        true,
        [8]
    ),
    backend,
    1,
    100,
    180,
    41,
    "mock-timer"
)
expect(executed.execution.cpu_authoritative).to_be(true)
expect(executed.execution.row_ids[0]).to_equal(8)
expect(executed.device_result.production_device_claim).to_be(false)
expect(executed.device_result.submission.dispatch_target).to_equal("cpu_fallback")
expect(executed.device_result.reason).to_equal("gpu-unavailable")
expect(executed.device_result.evidence.backend_timing_valid).to_be(false)
```

</details>

#### should attach strict native device evidence to SSD materialized scans

- Run a DB profile SSD materialized scan through the production device backend boundary
- profile clean materialized scan
- gpu wdb device backend
   - Expected: executed.execution.profile.data_path equals `GpuWdbCoarseDataPath.SsdStagedBatch`
   - Expected: executed.execution.validation_reason equals `production-gpu-row-match`
   - Expected: executed.execution.row_ids[0] equals `12`
   - Expected: executed.execution.row_ids[1] equals `34`
   - Expected: executed.device_result.submission.dispatch_target equals `gpu_db_columnar_scan_batch`
   - Expected: executed.device_result.evidence.device_time_us equals `58`


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Run a DB profile SSD materialized scan through the production device backend boundary")
val profile = db_offload_profile_ssd_accelerated("cuda", 6, 4)
val executed = db_offload_profile_execute_ssd_materialized_scan_device(
    profile,
    profile_clean_materialized_scan(),
    gpu_wdb_device_backend("cuda", 6, ["gpu_db_columnar_scan_batch"], true, "cuda-device-0"),
    6,
    [12, 34],
    100,
    190,
    58,
    "cuda-event"
)
expect(db_storage_offload_used_gpu(executed.execution)).to_be(true)
expect(executed.execution.profile.data_path).to_equal(GpuWdbCoarseDataPath.SsdStagedBatch)
expect(executed.execution.cpu_authoritative).to_be(false)
expect(executed.execution.gpu_candidate_validated).to_be(true)
expect(executed.execution.validation_reason).to_equal("production-gpu-row-match")
expect(executed.execution.row_ids[0]).to_equal(12)
expect(executed.execution.row_ids[1]).to_equal(34)
expect(executed.device_result.production_device_claim).to_be(true)
expect(executed.device_result.submission.dispatch_target).to_equal("gpu_db_columnar_scan_batch")
expect(executed.device_result.evidence.device_time_us).to_equal(58)
```

</details>

#### should reject mismatched SSD materialized scan candidates at the profile boundary

- Keep DB profile SSD materialized scans CPU authoritative on native candidate mismatch
- profile clean materialized scan
- gpu wdb device backend
   - Expected: executed.execution.dispatch_target equals `cpu_fallback`
   - Expected: executed.execution.validation_reason equals `production-gpu-row-mismatch`
   - Expected: executed.execution.row_ids[0] equals `12`
   - Expected: executed.execution.row_ids[1] equals `34`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Keep DB profile SSD materialized scans CPU authoritative on native candidate mismatch")
val profile = db_offload_profile_ssd_accelerated("cuda", 6, 4)
val executed = db_offload_profile_execute_ssd_materialized_scan_device(
    profile,
    profile_clean_materialized_scan(),
    gpu_wdb_device_backend("cuda", 6, ["gpu_db_columnar_scan_batch"], true, "cuda-device-0"),
    6,
    [12, 35],
    100,
    190,
    58,
    "cuda-event"
)
expect(db_storage_offload_used_gpu(executed.execution)).to_be(false)
expect(executed.execution.dispatch_target).to_equal("cpu_fallback")
expect(executed.execution.cpu_authoritative).to_be(true)
expect(executed.execution.gpu_candidate_validated).to_be(false)
expect(executed.execution.validation_reason).to_equal("production-gpu-row-mismatch")
expect(executed.execution.row_ids[0]).to_equal(12)
expect(executed.execution.row_ids[1]).to_equal(34)
expect(executed.device_result.production_device_claim).to_be(true)
```

</details>

#### should reject perf-only SSD materialized scan evidence at the profile boundary

- Keep DB profile SSD scans strict when the backend lacks native timing
- profile clean materialized scan
- gpu wdb device backend
   - Expected: executed.execution.profile.data_path equals `GpuWdbCoarseDataPath.SsdStagedBatch`
   - Expected: executed.execution.validation_reason equals `production-device-not-measured`
   - Expected: executed.execution.row_ids[0] equals `12`
   - Expected: executed.execution.row_ids[1] equals `34`
   - Expected: executed.device_result.submission.dispatch_target equals `cpu_fallback`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Keep DB profile SSD scans strict when the backend lacks native timing")
val profile = db_offload_profile_ssd_accelerated("host-safe-mock", 6, 4)
val executed = db_offload_profile_execute_ssd_materialized_scan_device(
    profile,
    profile_clean_materialized_scan(),
    gpu_wdb_device_backend("host-safe-mock", 6, ["gpu_db_columnar_scan_batch"], false, "mock-device"),
    6,
    [12, 34],
    100,
    190,
    58,
    "mock-timer"
)
expect(db_storage_offload_used_gpu(executed.execution)).to_be(false)
expect(executed.execution.profile.data_path).to_equal(GpuWdbCoarseDataPath.SsdStagedBatch)
expect(executed.execution.cpu_authoritative).to_be(true)
expect(executed.execution.gpu_candidate_validated).to_be(false)
expect(executed.execution.validation_reason).to_equal("production-device-not-measured")
expect(executed.execution.row_ids[0]).to_equal(12)
expect(executed.execution.row_ids[1]).to_equal(34)
expect(executed.device_result.production_device_claim).to_be(false)
expect(executed.device_result.submission.dispatch_target).to_equal("cpu_fallback")
```

</details>

#### should not claim row GPU evidence from the NoSQL profile

- Keep target registration scoped to document filtering
   - Expected: execution.dispatch_target equals `cpu_fallback`
   - Expected: execution.row_ids[0] equals `2`
   - Expected: execution.profile.data_path equals `GpuWdbCoarseDataPath.GpuResidentBatch`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Keep target registration scoped to document filtering")
val profile = db_offload_profile_nosql_gpu("cuda", 1, 4)
val execution = db_offload_profile_execute(
    profile,
    db_query_rows(
        DbStorageOffloadMode.RamOnly,
        DbStorageOffloadWorkload.ScanFilterProject,
        128,
        64,
        true,
        [2]
    )
)
expect(db_storage_offload_used_gpu(execution)).to_be(false)
expect(db_offload_profile_execution_allows_gpu(execution)).to_be(false)
expect(execution.dispatch_target).to_equal("cpu_fallback")
expect(execution.row_ids[0]).to_equal(2)
expect(execution.profile.data_path).to_equal(GpuWdbCoarseDataPath.GpuResidentBatch)
```

</details>

#### should dispatch NoSQL documents with the NoSQL profile

- Use document-filter profile targets for NoSQL batches
- db query documents
   - Expected: execution.dispatch_target equals `gpu_db_document_filter_batch`
   - Expected: execution.document_ids[0] equals `doc-1`
   - Expected: execution.profile.data_path equals `GpuWdbCoarseDataPath.GpuIndexBatch`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Use document-filter profile targets for NoSQL batches")
val profile = db_offload_profile_nosql_gpu("cuda", 1, 4)
val execution = db_offload_profile_execute(
    profile,
    db_query_documents(64, 128, true, true, ["doc-1"])
)
expect(db_storage_offload_used_gpu(execution)).to_be(true)
expect(db_offload_profile_execution_allows_gpu(execution)).to_be(true)
expect(execution.dispatch_target).to_equal("gpu_db_document_filter_batch")
expect(execution.document_ids[0]).to_equal("doc-1")
expect(execution.profile.data_path).to_equal(GpuWdbCoarseDataPath.GpuIndexBatch)
```

</details>

#### should replace RAM NoSQL document authority after measured native candidates match

- Use the NoSQL profile to validate RAM document candidates at the native backend boundary
- gpu wdb device backend
   - Expected: executed.execution.validation_reason equals `production-gpu-document-match`
   - Expected: executed.execution.reason equals `production-gpu-document-match`
   - Expected: executed.execution.document_ids[1] equals `doc-2`
   - Expected: executed.device_result.submission.dispatch_target equals `gpu_db_document_filter_batch`
   - Expected: executed.device_result.evidence.device_time_us equals `58`
   - Expected: executed.profile.queue_state.gpu_hit_count equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Use the NoSQL profile to validate RAM document candidates at the native backend boundary")
val profile = db_offload_profile_nosql_gpu("cuda", 6, 4)
val executed = db_offload_profile_execute_documents_device(
    profile,
    64,
    128,
    true,
    true,
    gpu_wdb_device_backend("cuda", 6, ["gpu_db_document_filter_batch"], true, "cuda-device-0"),
    6,
    ["doc-1", "doc-2"],
    ["doc-1", "doc-2"],
    100,
    190,
    58,
    "cuda-event"
)
expect(db_storage_offload_used_gpu(executed.execution)).to_be(true)
expect(executed.execution.cpu_authoritative).to_be(false)
expect(executed.execution.gpu_candidate_validated).to_be(true)
expect(executed.execution.validation_reason).to_equal("production-gpu-document-match")
expect(executed.execution.reason).to_equal("production-gpu-document-match")
expect(executed.execution.document_ids[1]).to_equal("doc-2")
expect(executed.device_result.production_device_claim).to_be(true)
expect(executed.device_result.submission.dispatch_target).to_equal("gpu_db_document_filter_batch")
expect(executed.device_result.evidence.device_time_us).to_equal(58)
expect(executed.profile.queue_state.gpu_hit_count).to_equal(1)
```

</details>

#### should reject mismatched RAM NoSQL document candidates at the profile boundary

- Keep CPU authority when native RAM document candidates disagree with the CPU oracle
- gpu wdb device backend
   - Expected: executed.execution.dispatch_target equals `cpu_fallback`
   - Expected: executed.execution.validation_reason equals `production-gpu-document-mismatch`
   - Expected: executed.execution.document_ids[1] equals `doc-2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Keep CPU authority when native RAM document candidates disagree with the CPU oracle")
val profile = db_offload_profile_nosql_gpu("cuda", 6, 4)
val executed = db_offload_profile_execute_documents_device(
    profile,
    64,
    128,
    true,
    true,
    gpu_wdb_device_backend("cuda", 6, ["gpu_db_document_filter_batch"], true, "cuda-device-0"),
    6,
    ["doc-1", "doc-2"],
    ["doc-1", "doc-3"],
    100,
    190,
    58,
    "cuda-event"
)
expect(db_storage_offload_used_gpu(executed.execution)).to_be(false)
expect(executed.execution.dispatch_target).to_equal("cpu_fallback")
expect(executed.execution.cpu_authoritative).to_be(true)
expect(executed.execution.gpu_candidate_validated).to_be(false)
expect(executed.execution.validation_reason).to_equal("production-gpu-document-mismatch")
expect(executed.execution.document_ids[1]).to_equal("doc-2")
expect(executed.device_result.production_device_claim).to_be(true)
```

</details>

#### should dispatch saved SSD NoSQL documents with the NoSQL profile

- Use profile queue and budget policy for durable document metadata filters
- file delete
- var collection = NoSqlSsdDocumentCollection create
- collection insert
- collection insert
   - Expected: execution.dispatch_target equals `gpu_db_document_filter_batch`
   - Expected: execution.document_ids[0] equals `doc-1`
   - Expected: execution.profile.data_path equals `GpuWdbCoarseDataPath.GpuIndexBatch`


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Use profile queue and budget policy for durable document metadata filters")
val path = "/tmp/simple-db-profile-ssd-nosql-documents.sdn"
file_delete(path)
val profile = db_offload_profile_nosql_gpu("cuda", 1, 4)
var collection = NoSqlSsdDocumentCollection.create(path)
collection.insert("doc-1", 4096, {"kind": "invoice"})
collection.insert("doc-2", 4096, {"kind": "note"})
expect(collection.save()).to_be(true)

val loaded = NoSqlSsdDocumentCollection.open(path)
val execution = db_offload_profile_execute_ssd_documents(
    profile,
    loaded,
    "kind",
    "invoice"
)
expect(db_storage_offload_used_gpu(execution)).to_be(true)
expect(db_offload_profile_execution_allows_gpu(execution)).to_be(true)
expect(execution.dispatch_target).to_equal("gpu_db_document_filter_batch")
expect(execution.document_ids[0]).to_equal("doc-1")
expect(execution.profile.data_path).to_equal(GpuWdbCoarseDataPath.GpuIndexBatch)
expect(execution.cpu_authoritative).to_be(true)
val _deleted = file_delete(path)
```

</details>

#### should keep unsaved SSD NoSQL profile work on CPU

- Require durable document generation before profile-level GPU evidence
- file delete
- var collection = NoSqlSsdDocumentCollection create
- collection insert
   - Expected: execution.dispatch_target equals `cpu_fallback`
   - Expected: execution.reason equals `stale-generation`
   - Expected: execution.document_ids[0] equals `doc-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Require durable document generation before profile-level GPU evidence")
val path = "/tmp/simple-db-profile-ssd-nosql-documents-stale.sdn"
file_delete(path)
val profile = db_offload_profile_nosql_gpu("cuda", 1, 4)
var collection = NoSqlSsdDocumentCollection.create(path)
collection.insert("doc-1", 128, {"kind": "invoice"})
val execution = db_offload_profile_execute_ssd_documents(
    profile,
    collection,
    "kind",
    "invoice"
)
expect(db_storage_offload_used_gpu(execution)).to_be(false)
expect(db_offload_profile_execution_allows_gpu(execution)).to_be(false)
expect(execution.dispatch_target).to_equal("cpu_fallback")
expect(execution.reason).to_equal("stale-generation")
expect(execution.document_ids[0]).to_equal("doc-1")
expect(execution.cpu_authoritative).to_be(true)
val _deleted = file_delete(path)
```

</details>

#### should attach strict native device evidence to saved SSD NoSQL documents

- Require native timing before SSD NoSQL document filters claim production GPU
- file delete
- var collection = NoSqlSsdDocumentCollection create
- collection insert
- collection insert
- gpu wdb device backend
   - Expected: executed.execution.validation_reason equals `production-gpu-document-match`
   - Expected: executed.execution.document_ids[0] equals `doc-1`
   - Expected: executed.device_result.submission.dispatch_target equals `gpu_db_document_filter_batch`
   - Expected: executed.device_result.evidence.device_time_us equals `58`
   - Expected: executed.profile.queue_state.gpu_hit_count equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 30 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Require native timing before SSD NoSQL document filters claim production GPU")
val path = "/tmp/simple-db-profile-ssd-nosql-documents-device.sdn"
file_delete(path)
val profile = db_offload_profile_nosql_gpu("cuda", 6, 4)
var collection = NoSqlSsdDocumentCollection.create(path)
collection.insert("doc-1", 4096, {"kind": "invoice"})
collection.insert("doc-2", 4096, {"kind": "note"})
expect(collection.save()).to_be(true)
val loaded = NoSqlSsdDocumentCollection.open(path)
val executed = db_offload_profile_execute_ssd_documents_device(
    profile,
    loaded,
    "kind",
    "invoice",
    gpu_wdb_device_backend("cuda", 6, ["gpu_db_document_filter_batch"], true, "cuda-device-0"),
    6,
    100,
    190,
    58,
    "cuda-event"
)
expect(executed.execution.cpu_authoritative).to_be(false)
expect(executed.execution.gpu_candidate_validated).to_be(true)
expect(executed.execution.validation_reason).to_equal("production-gpu-document-match")
expect(executed.execution.document_ids[0]).to_equal("doc-1")
expect(executed.device_result.production_device_claim).to_be(true)
expect(executed.device_result.submission.dispatch_target).to_equal("gpu_db_document_filter_batch")
expect(executed.device_result.evidence.device_time_us).to_equal(58)
expect(executed.profile.queue_state.gpu_hit_count).to_equal(1)
val _deleted = file_delete(path)
```

</details>

#### should reject mismatched SSD NoSQL document candidates at the profile boundary

- Keep durable SSD NoSQL filters CPU authoritative when native candidate IDs disagree
- file delete
- var collection = NoSqlSsdDocumentCollection create
- collection insert
- collection insert
- gpu wdb device backend
   - Expected: executed.execution.dispatch_target equals `cpu_fallback`
   - Expected: executed.execution.validation_reason equals `production-gpu-document-mismatch`
   - Expected: executed.execution.document_ids[0] equals `doc-1`
   - Expected: executed.profile.queue_state.gpu_hit_count equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 31 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Keep durable SSD NoSQL filters CPU authoritative when native candidate IDs disagree")
val path = "/tmp/simple-db-profile-ssd-nosql-documents-device-mismatch.sdn"
file_delete(path)
val profile = db_offload_profile_nosql_gpu("cuda", 6, 4)
var collection = NoSqlSsdDocumentCollection.create(path)
collection.insert("doc-1", 4096, {"kind": "invoice"})
collection.insert("doc-2", 4096, {"kind": "note"})
expect(collection.save()).to_be(true)
val loaded = NoSqlSsdDocumentCollection.open(path)
val executed = db_offload_profile_execute_ssd_documents_device_validated(
    profile,
    loaded,
    "kind",
    "invoice",
    gpu_wdb_device_backend("cuda", 6, ["gpu_db_document_filter_batch"], true, "cuda-device-0"),
    6,
    ["doc-2"],
    100,
    190,
    58,
    "cuda-event"
)
expect(db_storage_offload_used_gpu(executed.execution)).to_be(false)
expect(executed.execution.dispatch_target).to_equal("cpu_fallback")
expect(executed.execution.cpu_authoritative).to_be(true)
expect(executed.execution.gpu_candidate_validated).to_be(false)
expect(executed.execution.validation_reason).to_equal("production-gpu-document-mismatch")
expect(executed.execution.document_ids[0]).to_equal("doc-1")
expect(executed.device_result.production_device_claim).to_be(true)
expect(executed.profile.queue_state.gpu_hit_count).to_equal(1)
val _deleted = file_delete(path)
```

</details>

#### should block SSD NoSQL production device evidence for unsaved documents

- Use durable generation freshness before device-backed document dispatch
- file delete
- var collection = NoSqlSsdDocumentCollection create
- collection insert
- gpu wdb device backend
   - Expected: executed.execution.document_ids[0] equals `doc-1`
   - Expected: executed.device_result.submission.dispatch_target equals `cpu_fallback`
   - Expected: executed.device_result.reason equals `stale-generation`


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Use durable generation freshness before device-backed document dispatch")
val path = "/tmp/simple-db-profile-ssd-nosql-documents-device-stale.sdn"
file_delete(path)
val profile = db_offload_profile_nosql_gpu("cuda", 6, 4)
var collection = NoSqlSsdDocumentCollection.create(path)
collection.insert("doc-1", 4096, {"kind": "invoice"})
val executed = db_offload_profile_execute_ssd_documents_device(
    profile,
    collection,
    "kind",
    "invoice",
    gpu_wdb_device_backend("cuda", 6, ["gpu_db_document_filter_batch"], true, "cuda-device-0"),
    6,
    100,
    190,
    58,
    "cuda-event"
)
expect(executed.execution.cpu_authoritative).to_be(true)
expect(executed.execution.document_ids[0]).to_equal("doc-1")
expect(executed.device_result.production_device_claim).to_be(false)
expect(executed.device_result.submission.dispatch_target).to_equal("cpu_fallback")
expect(executed.device_result.reason).to_equal("stale-generation")
val _deleted = file_delete(path)
```

</details>

#### should reject perf-only SSD NoSQL device evidence

- Keep mock document-filter backends from claiming production GPU
- file delete
- var collection = NoSqlSsdDocumentCollection create
- collection insert
- gpu wdb device backend
   - Expected: executed.execution.document_ids[0] equals `doc-1`
   - Expected: executed.device_result.submission.dispatch_target equals `cpu_fallback`
   - Expected: executed.device_result.reason equals `gpu-unavailable`


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Keep mock document-filter backends from claiming production GPU")
val path = "/tmp/simple-db-profile-ssd-nosql-documents-device-mock.sdn"
file_delete(path)
val profile = db_offload_profile_nosql_gpu("host-safe-mock", 6, 4)
var collection = NoSqlSsdDocumentCollection.create(path)
collection.insert("doc-1", 128, {"kind": "invoice"})
expect(collection.save()).to_be(true)
val loaded = NoSqlSsdDocumentCollection.open(path)
val executed = db_offload_profile_execute_ssd_documents_device(
    profile,
    loaded,
    "kind",
    "invoice",
    gpu_wdb_device_backend("host-safe-mock", 6, ["gpu_db_document_filter_batch"], false, "mock-device"),
    6,
    100,
    190,
    58,
    "mock-timer"
)
expect(executed.execution.cpu_authoritative).to_be(true)
expect(executed.execution.document_ids[0]).to_equal("doc-1")
expect(executed.device_result.production_device_claim).to_be(false)
expect(executed.device_result.submission.dispatch_target).to_equal("cpu_fallback")
expect(executed.device_result.reason).to_equal("gpu-unavailable")
expect(executed.device_result.evidence.backend_timing_valid).to_be(false)
val _deleted = file_delete(path)
```

</details>

#### should dispatch vector search with the all-GPU profile

- Use the all-GPU profile for vector search targets
- [profile vector result
   - Expected: execution.dispatch_target equals `gpu_db_vector_search_batch`
   - Expected: execution.vector_ids[0] equals `vec-1`
   - Expected: execution.profile.data_path equals `GpuWdbCoarseDataPath.GpuIndexBatch`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Use the all-GPU profile for vector search targets")
val profile = db_offload_profile_all_gpu("cuda", 1, 4)
val execution = db_offload_profile_execute(
    profile,
    db_query_vector(
        DistanceMetric.Cosine,
        128,
        32,
        true,
        true,
        [profile_vector_result("vec-1", 0.1)]
    )
)
expect(db_storage_offload_used_gpu(execution)).to_be(true)
expect(db_offload_profile_execution_allows_gpu(execution)).to_be(true)
expect(execution.dispatch_target).to_equal("gpu_db_vector_search_batch")
expect(execution.vector_ids[0]).to_equal("vec-1")
expect(execution.profile.data_path).to_equal(GpuWdbCoarseDataPath.GpuIndexBatch)
```

</details>

#### should replace vector search results after measured native candidates match

- Use the DB profile vector boundary for production native result replacement
- gpu wdb device backend
- [profile vector result
- [profile vector result
   - Expected: executed.execution.validation_reason equals `production-gpu-vector-match`
   - Expected: executed.execution.vector_ids[1] equals `vec-2`
   - Expected: executed.device_result.submission.dispatch_target equals `gpu_db_vector_search_batch`
   - Expected: executed.profile.queue_state.gpu_hit_count equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Use the DB profile vector boundary for production native result replacement")
val profile = db_offload_profile_all_gpu("cuda", 7, 4)
val executed = db_offload_profile_execute_vector_device(
    profile,
    DistanceMetric.Cosine,
    128,
    32,
    true,
    true,
    gpu_wdb_device_backend("cuda", 7, ["gpu_db_vector_search_batch"], true, "cuda-device-0"),
    7,
    [profile_vector_result("vec-1", 0.1), profile_vector_result("vec-2", 0.2)],
    [profile_vector_result("vec-1", 0.1), profile_vector_result("vec-2", 0.2)],
    100,
    190,
    58,
    "cuda-event"
)
expect(db_storage_offload_used_gpu(executed.execution)).to_be(true)
expect(executed.execution.cpu_authoritative).to_be(false)
expect(executed.execution.gpu_candidate_validated).to_be(true)
expect(executed.execution.validation_reason).to_equal("production-gpu-vector-match")
expect(executed.execution.vector_ids[1]).to_equal("vec-2")
expect(executed.device_result.production_device_claim).to_be(true)
expect(executed.device_result.submission.dispatch_target).to_equal("gpu_db_vector_search_batch")
expect(executed.profile.queue_state.gpu_hit_count).to_equal(1)
```

</details>

#### should reject mismatched vector search candidates at the profile boundary

- Keep CPU vector results authoritative when measured native result IDs disagree
- gpu wdb device backend
- [profile vector result
- [profile vector result
   - Expected: executed.execution.dispatch_target equals `cpu_fallback`
   - Expected: executed.execution.validation_reason equals `production-gpu-vector-mismatch`
   - Expected: executed.execution.vector_ids[1] equals `vec-2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Keep CPU vector results authoritative when measured native result IDs disagree")
val profile = db_offload_profile_all_gpu("cuda", 7, 4)
val executed = db_offload_profile_execute_vector_device(
    profile,
    DistanceMetric.Cosine,
    128,
    32,
    true,
    true,
    gpu_wdb_device_backend("cuda", 7, ["gpu_db_vector_search_batch"], true, "cuda-device-0"),
    7,
    [profile_vector_result("vec-1", 0.1), profile_vector_result("vec-2", 0.2)],
    [profile_vector_result("vec-1", 0.1), profile_vector_result("vec-3", 0.3)],
    100,
    190,
    58,
    "cuda-event"
)
expect(db_storage_offload_used_gpu(executed.execution)).to_be(false)
expect(executed.execution.dispatch_target).to_equal("cpu_fallback")
expect(executed.execution.cpu_authoritative).to_be(true)
expect(executed.execution.gpu_candidate_validated).to_be(false)
expect(executed.execution.validation_reason).to_equal("production-gpu-vector-mismatch")
expect(executed.execution.vector_ids[1]).to_equal("vec-2")
expect(executed.device_result.production_device_claim).to_be(true)
```

</details>

#### should keep CPU-only profiles on CPU fallback

- Disable GPU evidence without losing CPU-authoritative results
- db query documents
   - Expected: execution.reason equals `gpu-unavailable`
   - Expected: execution.document_ids[0] equals `doc-2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Disable GPU evidence without losing CPU-authoritative results")
val profile = db_offload_profile_cpu_only("maintenance")
val execution = db_offload_profile_execute(
    profile,
    db_query_documents(64, 128, true, true, ["doc-2"])
)
expect(profile.gpu_available).to_be(false)
expect(db_storage_offload_used_gpu(execution)).to_be(false)
expect(db_offload_profile_execution_used_gpu(execution)).to_be(false)
expect(db_offload_profile_execution_allows_gpu(execution)).to_be(false)
expect(execution.reason).to_equal("gpu-unavailable")
expect(execution.document_ids[0]).to_equal("doc-2")
```

</details>

#### should defer tiny scheduled NoSQL profile batches

- Use profile-level scheduling for document batch accumulation
- db query documents
   - Expected: execution.dispatch_target equals `gpu_batch_accumulator`
   - Expected: execution.reason equals `batch-too-small-defer`
   - Expected: execution.document_ids[0] equals `doc-small`
   - Expected: execution.profile.data_path equals `GpuWdbCoarseDataPath.GpuIndexBatch`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Use profile-level scheduling for document batch accumulation")
val profile = db_offload_profile_nosql_gpu("cuda", 1, 4)
val execution = db_offload_profile_execute_scheduled(
    profile,
    db_query_documents(1, 128, true, true, ["doc-small"]),
    GpuWdbScheduleClass.Batch,
    true
)
expect(db_storage_offload_used_gpu(execution)).to_be(false)
expect(db_offload_profile_execution_allows_gpu(execution)).to_be(false)
expect(execution.dispatch_target).to_equal("gpu_batch_accumulator")
expect(execution.reason).to_equal("batch-too-small-defer")
expect(execution.document_ids[0]).to_equal("doc-small")
expect(execution.profile.data_path).to_equal(GpuWdbCoarseDataPath.GpuIndexBatch)
```

</details>

#### should accumulate tiny scheduled NoSQL profile batches

- Use profile defaults while mutating the reusable batch accumulator
- db query documents
- gpu wdb batch accumulator
   - Expected: accumulated.execution.dispatch_target equals `gpu_batch_accumulator`
   - Expected: accumulated.execution.document_ids[0] equals `doc-small`
   - Expected: accumulated.accumulator_result.accumulator.item_count equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Use profile defaults while mutating the reusable batch accumulator")
val profile = db_offload_profile_nosql_gpu("cuda", 1, 4)
val accumulated = db_offload_profile_execute_accumulating(
    profile,
    db_query_documents(1, 128, true, true, ["doc-small"]),
    GpuWdbScheduleClass.Background,
    gpu_wdb_batch_accumulator(GpuWdbWorkKind.DbDocumentFilter)
)
expect(db_storage_offload_used_gpu(accumulated.execution)).to_be(false)
expect(accumulated.execution.dispatch_target).to_equal("gpu_batch_accumulator")
expect(accumulated.execution.document_ids[0]).to_equal("doc-small")
expect(accumulated.accumulator_result.accepted).to_be(true)
expect(accumulated.accumulator_result.accumulator.item_count).to_equal(1)
```

</details>

#### should leave profile accumulator unchanged for immediate GPU dispatch

- Do not accumulate profile work that is already GPU-worthy
- [profile vector result
- gpu wdb batch accumulator
   - Expected: accumulated.execution.dispatch_target equals `gpu_db_vector_search_batch`
   - Expected: accumulated.accumulator_result.reason equals `query-not-deferred`
   - Expected: accumulated.accumulator_result.accumulator.item_count equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Do not accumulate profile work that is already GPU-worthy")
val profile = db_offload_profile_all_gpu("cuda", 1, 4)
val accumulated = db_offload_profile_execute_accumulating(
    profile,
    db_query_vector(
        DistanceMetric.Cosine,
        128,
        32,
        true,
        true,
        [profile_vector_result("vec-2", 0.2)]
    ),
    GpuWdbScheduleClass.Batch,
    gpu_wdb_batch_accumulator(GpuWdbWorkKind.DbVectorSearch)
)
expect(db_storage_offload_used_gpu(accumulated.execution)).to_be(true)
expect(db_offload_profile_execution_allows_gpu(accumulated.execution)).to_be(true)
expect(accumulated.execution.dispatch_target).to_equal("gpu_db_vector_search_batch")
expect(accumulated.accumulator_result.accepted).to_be(false)
expect(accumulated.accumulator_result.reason).to_equal("query-not-deferred")
expect(accumulated.accumulator_result.accumulator.item_count).to_equal(0)
```

</details>

#### should flush accumulated NoSQL profile work through the GPU queue

- Use profile targets and queue state to submit a ready document batch
- db query documents
- gpu wdb batch accumulator
- db query documents
   - Expected: flushed.submission.dispatch_target equals `gpu_db_document_filter_batch`
   - Expected: flushed.accumulator_after.item_count equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Use profile targets and queue state to submit a ready document batch")
val profile = db_offload_profile_nosql_gpu("cuda", 1, 4)
val first_accumulated = db_offload_profile_execute_accumulating(
    profile,
    db_query_documents(16, 128, true, true, ["doc-ready"]),
    GpuWdbScheduleClass.Background,
    gpu_wdb_batch_accumulator(GpuWdbWorkKind.DbDocumentFilter)
)
val accumulated = db_offload_profile_execute_accumulating(
    profile,
    db_query_documents(16, 128, true, true, ["doc-ready-2"]),
    GpuWdbScheduleClass.Background,
    first_accumulated.accumulator_result.accumulator
)
val flushed = db_offload_profile_flush_accumulator_current(
    profile,
    accumulated.accumulator_result.accumulator
)
expect(flushed.attempted).to_be(true)
expect(flushed.submission.accepted).to_be(true)
expect(flushed.submission.dispatch_target).to_equal("gpu_db_document_filter_batch")
expect(flushed.accumulator_after.item_count).to_equal(0)
```

</details>

#### should advance DB profile queue state after accumulator flush

- Return a profile with queued batch pressure after flushing accumulated work
- db query documents
- gpu wdb batch accumulator
- db query documents
   - Expected: flushed.flush.submission.dispatch_target equals `gpu_db_document_filter_batch`
   - Expected: flushed.profile.queue_state.submitted_count equals `1`
   - Expected: flushed.profile.queue_state.gpu_hit_count equals `1`
   - Expected: flushed.profile.queue_state.queue_depth equals `1`
   - Expected: flushed.profile.queue_state.completed_count equals `0`
   - Expected: flushed.flush.accumulator_after.item_count equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Return a profile with queued batch pressure after flushing accumulated work")
val profile = db_offload_profile_nosql_gpu("cuda", 1, 4)
val first_accumulated = db_offload_profile_execute_accumulating(
    profile,
    db_query_documents(16, 128, true, true, ["doc-ready"]),
    GpuWdbScheduleClass.Background,
    gpu_wdb_batch_accumulator(GpuWdbWorkKind.DbDocumentFilter)
)
val accumulated = db_offload_profile_execute_accumulating(
    profile,
    db_query_documents(16, 128, true, true, ["doc-ready-2"]),
    GpuWdbScheduleClass.Background,
    first_accumulated.accumulator_result.accumulator
)
val flushed = db_offload_profile_flush_accumulator_current_advancing(
    profile,
    accumulated.accumulator_result.accumulator
)
expect(flushed.flush.attempted).to_be(true)
expect(flushed.flush.submission.accepted).to_be(true)
expect(flushed.flush.submission.dispatch_target).to_equal("gpu_db_document_filter_batch")
expect(flushed.profile.queue_state.submitted_count).to_equal(1)
expect(flushed.profile.queue_state.gpu_hit_count).to_equal(1)
expect(flushed.profile.queue_state.queue_depth).to_equal(1)
expect(flushed.profile.queue_state.completed_count).to_equal(0)
expect(flushed.flush.accumulator_after.item_count).to_equal(0)
```

</details>

#### should complete DB profile flushed submissions and release queue pressure

- Use profile-level completion after a queued GPU batch finishes
- db query documents
- gpu wdb batch accumulator
- db query documents
   - Expected: completed.queue_state.submitted_count equals `1`
   - Expected: completed.queue_state.gpu_hit_count equals `1`
   - Expected: completed.queue_state.queue_depth equals `0`
   - Expected: completed.queue_state.completed_count equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Use profile-level completion after a queued GPU batch finishes")
val profile = db_offload_profile_nosql_gpu("cuda", 1, 4)
val first_accumulated = db_offload_profile_execute_accumulating(
    profile,
    db_query_documents(16, 128, true, true, ["doc-ready"]),
    GpuWdbScheduleClass.Background,
    gpu_wdb_batch_accumulator(GpuWdbWorkKind.DbDocumentFilter)
)
val accumulated = db_offload_profile_execute_accumulating(
    profile,
    db_query_documents(16, 128, true, true, ["doc-ready-2"]),
    GpuWdbScheduleClass.Background,
    first_accumulated.accumulator_result.accumulator
)
val flushed = db_offload_profile_flush_accumulator_current_advancing(
    profile,
    accumulated.accumulator_result.accumulator
)
val completed = db_offload_profile_complete_submission(
    flushed.profile,
    flushed.flush.submission
)
expect(completed.queue_state.submitted_count).to_equal(1)
expect(completed.queue_state.gpu_hit_count).to_equal(1)
expect(completed.queue_state.queue_depth).to_equal(0)
expect(completed.queue_state.completed_count).to_equal(1)
```

</details>

#### should flush stale SSD accumulated work to CPU fallback

- Preserve WAL freshness at the profile flush boundary
- gpu wdb batch accumulator
   - Expected: flushed.submission.dispatch_target equals `cpu_fallback`
   - Expected: flushed.reason equals `stale-generation`
   - Expected: flushed.accumulator_after.item_count equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Preserve WAL freshness at the profile flush boundary")
val profile = db_offload_profile_ssd_accelerated("cuda", 1, 4)
val accumulated = db_offload_profile_execute_accumulating(
    profile,
    db_query_rows(
        DbStorageOffloadMode.SsdAccelerated,
        DbStorageOffloadWorkload.ScanFilterProject,
        1,
        128,
        true,
        [5]
    ),
    GpuWdbScheduleClass.Background,
    gpu_wdb_batch_accumulator(GpuWdbWorkKind.DbScanFilterProject)
)
val flushed = db_offload_profile_flush_accumulator(
    profile,
    accumulated.accumulator_result.accumulator,
    false
)
expect(flushed.attempted).to_be(true)
expect(flushed.submission.accepted).to_be(false)
expect(flushed.submission.dispatch_target).to_equal("cpu_fallback")
expect(flushed.reason).to_equal("stale-generation")
expect(flushed.accumulator_after.item_count).to_equal(0)
```

</details>

#### should flush stale DB profile target generations to CPU fallback

- Use the reusable registry generation guard before DB GPU evidence
- gpu wdb batch accumulator
   - Expected: flushed.submission.dispatch_target equals `cpu_fallback`
   - Expected: flushed.reason equals `stale-generation`
   - Expected: flushed.accumulator_after.item_count equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Use the reusable registry generation guard before DB GPU evidence")
val profile = db_offload_profile_ssd_accelerated("cuda", 1, 4)
val accumulated = db_offload_profile_execute_accumulating(
    profile,
    db_query_rows(
        DbStorageOffloadMode.SsdAccelerated,
        DbStorageOffloadWorkload.ScanFilterProject,
        1,
        128,
        true,
        [5]
    ),
    GpuWdbScheduleClass.Background,
    gpu_wdb_batch_accumulator(GpuWdbWorkKind.DbScanFilterProject)
)
val flushed = db_offload_profile_flush_accumulator_for_generation(
    profile,
    accumulated.accumulator_result.accumulator,
    2
)
expect(flushed.attempted).to_be(true)
expect(flushed.submission.accepted).to_be(false)
expect(flushed.submission.dispatch_target).to_equal("cpu_fallback")
expect(flushed.reason).to_equal("stale-generation")
expect(flushed.accumulator_after.item_count).to_equal(0)
```

</details>

#### should retain accumulated DB profile work after hard reject

- Keep rejected accumulated work visible when no CPU fallback exists
- [profile vector result
- gpu wdb batch accumulator
   - Expected: flushed.submission.execution.decision.path equals `GpuWdbDecisionPath.Reject`
   - Expected: flushed.reason equals `cpu-fallback-required`
   - Expected: flushed.accumulator_after.item_count equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 36 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Keep rejected accumulated work visible when no CPU fallback exists")
val profile = db_offload_profile(
    "unsafe-no-cpu",
    "cuda",
    1,
    4,
    ["gpu_db_vector_search_batch"],
    GpuWdbBudget(
        max_queue_depth: 64,
        max_batch_bytes: 1024 * 1024,
        min_gpu_batch_bytes: 1024
    ),
    true,
    false
)
val accumulated = db_offload_profile_execute_accumulating(
    profile,
    db_query_vector(
        DistanceMetric.Cosine,
        1,
        32,
        true,
        true,
        [profile_vector_result("vec-small", 0.3)]
    ),
    GpuWdbScheduleClass.Background,
    gpu_wdb_batch_accumulator(GpuWdbWorkKind.DbVectorSearch)
)
val flushed = db_offload_profile_flush_accumulator_current(
    profile,
    accumulated.accumulator_result.accumulator
)
expect(flushed.attempted).to_be(true)
expect(flushed.submission.execution.decision.path).to_equal(GpuWdbDecisionPath.Reject)
expect(flushed.reason).to_equal("cpu-fallback-required")
expect(flushed.accumulator_after.item_count).to_equal(1)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 30 |
| Active scenarios | 30 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** [doc/02_requirements/feature/gpu_web_db_offload.md](doc/02_requirements/feature/gpu_web_db_offload.md)
- **Plan:** [doc/03_plan/agent_tasks/gpu_web_db_offload_impl_status.md](doc/03_plan/agent_tasks/gpu_web_db_offload_impl_status.md)
- **Design:** [doc/05_design/gpu_web_db_offload.md](doc/05_design/gpu_web_db_offload.md)


</details>
