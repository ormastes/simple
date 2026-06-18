# Async Database GPU Offload Public Exports

> These scenarios verify that async `std.database` callers can import the strict GPU device-validation facades used by RAM, SSD, NoSQL, and vector DB offload paths without reaching into sync implementation modules.

<!-- sdn-diagram:id=database_gpu_offload_exports_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=database_gpu_offload_exports_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

database_gpu_offload_exports_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=database_gpu_offload_exports_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Async Database GPU Offload Public Exports

These scenarios verify that async `std.database` callers can import the strict GPU device-validation facades used by RAM, SSD, NoSQL, and vector DB offload paths without reaching into sync implementation modules.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Requirements | doc/02_requirements/feature/gpu_web_db_offload.md |
| Plan | doc/03_plan/agent_tasks/gpu_web_db_offload_impl_status.md |
| Design | doc/05_design/gpu_web_db_offload.md |
| Research | doc/01_research/lib/networking/reverse_proxy_gpu_boundary_2026-06-16.md |
| Source | `test/01_unit/lib/nogc_async_mut/database/database_gpu_offload_exports_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

These scenarios verify that async `std.database` callers can import the strict
GPU device-validation facades used by RAM, SSD, NoSQL, and vector DB offload
paths without reaching into sync implementation modules.

## Requirements

**Requirements:** doc/02_requirements/feature/gpu_web_db_offload.md

## Plan

**Plan:** doc/03_plan/agent_tasks/gpu_web_db_offload_impl_status.md

## Design

**Design:** doc/05_design/gpu_web_db_offload.md

## Research

**Research:** doc/01_research/lib/networking/reverse_proxy_gpu_boundary_2026-06-16.md

## Examples

Import strict validation helpers from `std.database` in async DB/server code
instead of reaching into sync implementation modules.

## Scenarios

### async database GPU offload public exports

#### should expose strict GPU device validation facades through std.database

- Call an async-root strict RAM row validation helper with a matching GPU candidate
- gpu wdb queue initial
- gpu wdb device backend
- async export budget
   - Expected: execution.execution.validation_reason equals `production-gpu-row-match`
   - Expected: execution.execution.row_ids[0] equals `7`
   - Expected: execution.execution.row_ids[1] equals `8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Call an async-root strict RAM row validation helper with a matching GPU candidate")
val execution: DbStorageDeviceOffloadExecution = db_query_offload_execute_rows_device_validated(
    db_query_rows(
        DbStorageOffloadMode.RamOnly,
        DbStorageOffloadWorkload.ScanFilterProject,
        2,
        128,
        true,
        [7, 8]
    ),
    gpu_wdb_queue_initial(2),
    gpu_wdb_device_backend("cuda", 4, ["gpu_db_columnar_scan_batch"], true, "cuda-device-0"),
    4,
    true,
    async_export_budget(),
    [7, 8],
    100,
    180,
    39,
    "cuda-event"
)
expect(execution.execution.cpu_authoritative).to_be(false)
expect(execution.execution.gpu_candidate_validated).to_be(true)
expect(execution.execution.validation_reason).to_equal("production-gpu-row-match")
expect(execution.execution.row_ids[0]).to_equal(7)
expect(execution.execution.row_ids[1]).to_equal(8)
expect(execution.device_execution.device_result.production_device_claim).to_be(true)
```

</details>

#### should expose strict NoSQL document GPU validation through std.database

- Call an async-root strict NoSQL document validation helper with matching GPU IDs
- gpu wdb queue initial
- gpu wdb device backend
- async export budget
   - Expected: execution.execution.submission.reason equals `production-gpu-document-match`
   - Expected: execution.execution.result_ids[0] equals `doc-1`
   - Expected: execution.execution.result_ids[1] equals `doc-3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Call an async-root strict NoSQL document validation helper with matching GPU IDs")
val execution: NoSqlDocumentDeviceOffloadExecution = nosql_document_offload_execute_device_validated(
    128,
    64,
    true,
    gpu_wdb_queue_initial(2),
    gpu_wdb_device_backend("cuda", 5, ["gpu_db_document_filter_batch"], true, "cuda-device-0"),
    true,
    5,
    true,
    async_export_budget(),
    ["doc-1", "doc-3"],
    ["doc-1", "doc-3"],
    200,
    290,
    61,
    "cuda-event"
)
expect(execution.execution.cpu_authoritative).to_be(false)
expect(execution.execution.submission.reason).to_equal("production-gpu-document-match")
expect(execution.execution.result_ids[0]).to_equal("doc-1")
expect(execution.execution.result_ids[1]).to_equal("doc-3")
expect(execution.device_result.production_device_claim).to_be(true)
```

</details>

#### should expose strict vector-search GPU validation through std.database

- Call an async-root strict vector query helper with matching GPU search results
- SearchResult
- SearchResult
- db query vector
- gpu wdb queue initial
- gpu wdb device backend
- async export budget
   - Expected: execution.execution.validation_reason equals `production-gpu-vector-match`
   - Expected: execution.execution.vector_ids[0] equals `vec-a`
   - Expected: execution.execution.vector_ids[1] equals `vec-c`


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Call an async-root strict vector query helper with matching GPU search results")
val cpu_results = [
    SearchResult(id: "vec-a", distance: 0.0, metadata: {"kind": "unit"}),
    SearchResult(id: "vec-c", distance: 0.25, metadata: {"kind": "unit"})
]
val execution: DbStorageVectorDeviceOffloadExecution = db_query_offload_execute_vector_device_validated(
    db_query_vector(DistanceMetric.Euclidean, 3, 2, true, true, cpu_results),
    gpu_wdb_queue_initial(2),
    gpu_wdb_device_backend("cuda", 6, ["gpu_db_vector_search_batch"], true, "cuda-device-0"),
    6,
    true,
    async_export_budget(),
    cpu_results,
    300,
    420,
    71,
    "cuda-event"
)
expect(execution.execution.cpu_authoritative).to_be(false)
expect(execution.execution.gpu_candidate_validated).to_be(true)
expect(execution.execution.validation_reason).to_equal("production-gpu-vector-match")
expect(execution.execution.vector_ids[0]).to_equal("vec-a")
expect(execution.execution.vector_ids[1]).to_equal("vec-c")
expect(execution.device_result.production_device_claim).to_be(true)
```

</details>

#### should expose strict SSD materialized scan GPU validation through std.database

- Call an async-root strict SSD materialized scan helper with matching GPU row IDs
- async export materialized scan
- gpu wdb queue initial
- gpu wdb device backend
- async export budget
   - Expected: execution.execution.mode equals `DbStorageOffloadMode.SsdAccelerated`
   - Expected: execution.execution.validation_reason equals `production-gpu-row-match`
   - Expected: execution.execution.row_ids[0] equals `12`
   - Expected: execution.execution.row_ids[1] equals `34`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Call an async-root strict SSD materialized scan helper with matching GPU row IDs")
val execution: DbStorageDeviceOffloadExecution = db_storage_execute_ssd_materialized_scan_with_device_backend_validated(
    async_export_materialized_scan(),
    gpu_wdb_queue_initial(4),
    gpu_wdb_device_backend("cuda", 7, ["gpu_db_columnar_scan_batch"], true, "cuda-device-0"),
    7,
    true,
    async_export_budget(),
    [12, 34],
    500,
    640,
    88,
    "cuda-event"
)
expect(execution.execution.mode).to_equal(DbStorageOffloadMode.SsdAccelerated)
expect(execution.execution.cpu_authoritative).to_be(false)
expect(execution.execution.gpu_candidate_validated).to_be(true)
expect(execution.execution.validation_reason).to_equal("production-gpu-row-match")
expect(execution.execution.row_ids[0]).to_equal(12)
expect(execution.execution.row_ids[1]).to_equal(34)
expect(execution.device_execution.device_result.production_device_claim).to_be(true)
```

</details>

#### should expose strict SSD NoSQL document GPU validation through std.database

- Call an async-root strict SSD NoSQL helper with matching GPU document IDs
- file delete
- var collection = NoSqlSsdDocumentCollection create
- collection insert
- collection insert
- gpu wdb queue initial
- gpu wdb device backend
- async export budget
   - Expected: execution.execution.validation_reason equals `production-gpu-document-match`
   - Expected: execution.execution.document_ids[0] equals `doc-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Call an async-root strict SSD NoSQL helper with matching GPU document IDs")
val path = "/tmp/simple-async-db-exports-ssd-nosql-documents.sdn"
file_delete(path)
var collection = NoSqlSsdDocumentCollection.create(path)
collection.insert("doc-1", 1024, {"kind": "invoice"})
collection.insert("doc-2", 1024, {"kind": "note"})
expect(collection.save()).to_be(true)
val loaded = NoSqlSsdDocumentCollection.open(path)
val execution: DbStorageDocumentDeviceOffloadExecution = db_storage_execute_ssd_documents_with_device_backend_validated(
    loaded,
    "kind",
    "invoice",
    gpu_wdb_queue_initial(4),
    gpu_wdb_device_backend("cuda", 8, ["gpu_db_document_filter_batch"], true, "cuda-device-0"),
    8,
    true,
    async_export_budget(),
    ["doc-1"],
    700,
    860,
    97,
    "cuda-event"
)
expect(execution.execution.cpu_authoritative).to_be(false)
expect(execution.execution.gpu_candidate_validated).to_be(true)
expect(execution.execution.validation_reason).to_equal("production-gpu-document-match")
expect(execution.execution.document_ids[0]).to_equal("doc-1")
expect(execution.device_result.production_device_claim).to_be(true)
val _deleted = file_delete(path)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** [doc/02_requirements/feature/gpu_web_db_offload.md](doc/02_requirements/feature/gpu_web_db_offload.md)
- **Plan:** [doc/03_plan/agent_tasks/gpu_web_db_offload_impl_status.md](doc/03_plan/agent_tasks/gpu_web_db_offload_impl_status.md)
- **Design:** [doc/05_design/gpu_web_db_offload.md](doc/05_design/gpu_web_db_offload.md)
- **Research:** [doc/01_research/lib/networking/reverse_proxy_gpu_boundary_2026-06-16.md](doc/01_research/lib/networking/reverse_proxy_gpu_boundary_2026-06-16.md)


</details>
