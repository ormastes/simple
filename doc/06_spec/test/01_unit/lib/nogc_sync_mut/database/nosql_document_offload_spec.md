# NoSQL Document GPU Offload

> These scenarios model document-filter batches as coarse DB work while preserving CPU-owned metadata filtering and CPU-authoritative result IDs.

<!-- sdn-diagram:id=nosql_document_offload_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=nosql_document_offload_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

nosql_document_offload_spec -> std
nosql_document_offload_spec -> `filter_metadata_with_offload` to record GPU eligibility while preserving
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=nosql_document_offload_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 13 | 13 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# NoSQL Document GPU Offload

These scenarios model document-filter batches as coarse DB work while preserving CPU-owned metadata filtering and CPU-authoritative result IDs.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Requirements | doc/02_requirements/feature/gpu_web_db_offload.md |
| Plan | doc/03_plan/agent_tasks/gpu_web_db_offload_impl_status.md |
| Design | doc/05_design/gpu_web_db_offload.md |
| Research | N/A |
| Source | `test/01_unit/lib/nogc_sync_mut/database/nosql_document_offload_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

These scenarios model document-filter batches as coarse DB work while preserving
CPU-owned metadata filtering and CPU-authoritative result IDs.

## Requirements

**Requirements:** doc/02_requirements/feature/gpu_web_db_offload.md

- NoSQL document metadata filtering stays CPU-owned.
- RAM-only document collections can feed authoritative result IDs into the
  shared document offload adapter.
- NoSQL document collections can persist and reload durable metadata-filter
  state.
- Stale document collection generations fall back to CPU.

## Plan

**Plan:** doc/03_plan/agent_tasks/gpu_web_db_offload_impl_status.md

## Design

**Design:** doc/05_design/gpu_web_db_offload.md

## Research

**Research:** N/A

## Examples

Insert document records into `NoSqlDocumentCollection`, filter by metadata, and
use `filter_metadata_with_offload` to record GPU eligibility while preserving
the CPU-filtered document IDs as authoritative output.

## Scenarios

### NoSQL document GPU offload adapter

#### should estimate document batch bytes

- Estimate document count times average encoded document size
   - Expected: nosql_document_estimated_batch_bytes(128, 64) equals `8192`
   - Expected: nosql_document_estimated_batch_bytes(0, 64) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Estimate document count times average encoded document size")
expect(nosql_document_estimated_batch_bytes(128, 64)).to_equal(8192)
expect(nosql_document_estimated_batch_bytes(0, 64)).to_equal(0)
```

</details>

#### should dispatch registered document filter batches to GPU accounting

- Use the reusable registry target for document filtering
- gpu wdb queue initial
- nosql budget
   - Expected: execution.submission.dispatch_target equals `gpu_db_document_filter_batch`
   - Expected: execution.state_after.completed_count equals `1`
   - Expected: execution.result_ids.len() equals `2`
   - Expected: execution.profile.data_path equals `GpuWdbCoarseDataPath.GpuIndexBatch`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Use the reusable registry target for document filtering")
val registry = gpu_wdb_library_with_targets("cuda", 1, ["gpu_db_document_filter_batch"])
val execution = nosql_document_offload_execute(
    128,
    64,
    true,
    gpu_wdb_queue_initial(2),
    registry,
    true,
    true,
    true,
    nosql_budget(),
    ["doc-1", "doc-2"]
)
expect(nosql_document_offload_used_gpu(execution)).to_be(true)
expect(execution.submission.dispatch_target).to_equal("gpu_db_document_filter_batch")
expect(execution.state_after.completed_count).to_equal(1)
expect(execution.result_ids.len()).to_equal(2)
expect(execution.cpu_authoritative).to_be(true)
expect(execution.profile.data_path).to_equal(GpuWdbCoarseDataPath.GpuIndexBatch)
expect(nosql_document_profile_allows_gpu(execution)).to_be(true)
```

</details>

#### should fall back when document GPU target is missing

- Avoid fake GPU evidence without a registered document target
- gpu wdb queue initial
- gpu wdb library empty
- nosql budget
   - Expected: execution.submission.dispatch_target equals `cpu_fallback`
   - Expected: execution.submission.reason equals `gpu-unavailable`
   - Expected: execution.state_after.cpu_fallback_count equals `1`
   - Expected: execution.profile.data_path equals `GpuWdbCoarseDataPath.GpuIndexBatch`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Avoid fake GPU evidence without a registered document target")
val execution = nosql_document_offload_execute(
    128,
    64,
    true,
    gpu_wdb_queue_initial(2),
    gpu_wdb_library_empty(),
    true,
    true,
    true,
    nosql_budget(),
    ["doc-1"]
)
expect(nosql_document_offload_used_gpu(execution)).to_be(false)
expect(execution.submission.dispatch_target).to_equal("cpu_fallback")
expect(execution.submission.reason).to_equal("gpu-unavailable")
expect(execution.state_after.cpu_fallback_count).to_equal(1)
expect(execution.profile.data_path).to_equal(GpuWdbCoarseDataPath.GpuIndexBatch)
expect(nosql_document_profile_allows_gpu(execution)).to_be(false)
```

</details>

#### should reject document offload when metadata filtering is not CPU-owned

- Keep metadata filtering in the CPU control path
- gpu wdb queue initial
- nosql budget
   - Expected: execution.submission.dispatch_target equals `cpu_fallback`
   - Expected: execution.submission.reason equals `metadata-filter-must-stay-cpu-owned`
   - Expected: execution.state_after.rejected_count equals `0`
   - Expected: execution.profile.data_path equals `GpuWdbCoarseDataPath.GpuIndexBatch`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Keep metadata filtering in the CPU control path")
val registry = gpu_wdb_library_with_targets("cuda", 1, ["gpu_db_document_filter_batch"])
val execution = nosql_document_offload_execute(
    128,
    64,
    false,
    gpu_wdb_queue_initial(2),
    registry,
    true,
    true,
    true,
    nosql_budget(),
    ["doc-1"]
)
expect(nosql_document_offload_used_gpu(execution)).to_be(false)
expect(execution.submission.dispatch_target).to_equal("cpu_fallback")
expect(execution.submission.reason).to_equal("metadata-filter-must-stay-cpu-owned")
expect(execution.state_after.rejected_count).to_equal(0)
expect(execution.cpu_authoritative).to_be(true)
expect(execution.profile.data_path).to_equal(GpuWdbCoarseDataPath.GpuIndexBatch)
expect(nosql_document_profile_allows_gpu(execution)).to_be(false)
```

</details>

#### should filter RAM document metadata before offload accounting

- Use engine-owned CPU metadata filtering to produce authoritative IDs
- var collection = NoSqlDocumentCollection empty
- collection insert
- collection insert
- collection insert
- gpu wdb queue initial
- gpu wdb library with targets
- nosql budget
   - Expected: ids.len() equals `2`
   - Expected: ids[0] equals `doc-1`
   - Expected: ids[1] equals `doc-3`
   - Expected: collection.document_count() equals `3`
   - Expected: collection.average_encoded_bytes() equals `170`
   - Expected: execution.result_ids[0] equals `doc-1`
   - Expected: execution.result_ids[1] equals `doc-3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Use engine-owned CPU metadata filtering to produce authoritative IDs")
var collection = NoSqlDocumentCollection.empty()
collection.insert("doc-1", 128, {"kind": "invoice", "tenant": "a"})
collection.insert("doc-2", 256, {"kind": "note", "tenant": "a"})
collection.insert("doc-3", 128, {"kind": "invoice", "tenant": "b"})
val ids = collection.filter_metadata_ids("kind", "invoice")
val execution = collection.filter_metadata_with_offload(
    "kind",
    "invoice",
    gpu_wdb_queue_initial(2),
    gpu_wdb_library_with_targets("cuda", 1, ["gpu_db_document_filter_batch"]),
    true,
    true,
    nosql_budget()
)
expect(ids.len()).to_equal(2)
expect(ids[0]).to_equal("doc-1")
expect(ids[1]).to_equal("doc-3")
expect(collection.document_count()).to_equal(3)
expect(collection.average_encoded_bytes()).to_equal(170)
expect(nosql_document_offload_used_gpu(execution)).to_be(true)
expect(execution.result_ids[0]).to_equal("doc-1")
expect(execution.result_ids[1]).to_equal("doc-3")
expect(execution.cpu_authoritative).to_be(true)
```

</details>

#### should keep stale RAM document collection filters on CPU

- Preserve generation freshness before document-filter dispatch
- var collection = NoSqlDocumentCollection empty
- collection insert
- collection mark generation stale
- gpu wdb queue initial
- gpu wdb library with targets
- nosql budget
   - Expected: execution.submission.dispatch_target equals `cpu_fallback`
   - Expected: execution.submission.reason equals `stale-generation`
   - Expected: execution.result_ids[0] equals `doc-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Preserve generation freshness before document-filter dispatch")
var collection = NoSqlDocumentCollection.empty()
collection.insert("doc-1", 128, {"kind": "invoice"})
collection.mark_generation_stale()
val execution = collection.filter_metadata_with_offload(
    "kind",
    "invoice",
    gpu_wdb_queue_initial(2),
    gpu_wdb_library_with_targets("cuda", 1, ["gpu_db_document_filter_batch"]),
    true,
    true,
    nosql_budget()
)
expect(nosql_document_offload_used_gpu(execution)).to_be(false)
expect(execution.submission.dispatch_target).to_equal("cpu_fallback")
expect(execution.submission.reason).to_equal("stale-generation")
expect(execution.result_ids[0]).to_equal("doc-1")
```

</details>

#### should keep stale document GPU target generations on CPU

- Require current registry generation separately from document freshness
- gpu wdb queue initial
- nosql budget
   - Expected: execution.submission.dispatch_target equals `cpu_fallback`
   - Expected: execution.submission.reason equals `stale-generation`
   - Expected: execution.state_after.cpu_fallback_count equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Require current registry generation separately from document freshness")
val registry = gpu_wdb_library_with_targets("cuda", 1, ["gpu_db_document_filter_batch"])
val execution = nosql_document_offload_execute_for_generation(
    128,
    64,
    true,
    gpu_wdb_queue_initial(2),
    registry,
    true,
    true,
    2,
    true,
    nosql_budget(),
    ["doc-1"]
)
expect(nosql_document_offload_used_gpu(execution)).to_be(false)
expect(execution.submission.dispatch_target).to_equal("cpu_fallback")
expect(execution.submission.reason).to_equal("stale-generation")
expect(execution.state_after.cpu_fallback_count).to_equal(1)
expect(nosql_document_profile_allows_gpu(execution)).to_be(false)
```

</details>

#### should replace RAM document filter IDs only after native candidates match

- Require production native timing and CPU document ID agreement
- gpu wdb queue initial
- gpu wdb device backend
- nosql budget
   - Expected: execution.execution.result_ids[0] equals `doc-1`
   - Expected: execution.execution.result_ids[1] equals `doc-3`
   - Expected: execution.execution.submission.reason equals `production-gpu-document-match`


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Require production native timing and CPU document ID agreement")
val execution = nosql_document_offload_execute_device_validated(
    128,
    64,
    true,
    gpu_wdb_queue_initial(2),
    gpu_wdb_device_backend("cuda", 3, ["gpu_db_document_filter_batch"], true, "cuda-device-0"),
    true,
    3,
    true,
    nosql_budget(),
    ["doc-1", "doc-3"],
    ["doc-1", "doc-3"],
    100,
    190,
    55,
    "cuda-event"
)
expect(nosql_document_offload_used_gpu(execution.execution)).to_be(true)
expect(execution.execution.cpu_authoritative).to_be(false)
expect(execution.execution.result_ids[0]).to_equal("doc-1")
expect(execution.execution.result_ids[1]).to_equal("doc-3")
expect(execution.execution.submission.reason).to_equal("production-gpu-document-match")
expect(execution.device_result.production_device_claim).to_be(true)
```

</details>

#### should keep RAM document filter IDs CPU authoritative when native candidates mismatch

- Reject production native document IDs that differ from the CPU oracle
- gpu wdb queue initial
- gpu wdb device backend
- nosql budget
   - Expected: execution.execution.submission.dispatch_target equals `cpu_fallback`
   - Expected: execution.execution.submission.reason equals `production-gpu-document-mismatch`
   - Expected: execution.execution.result_ids[1] equals `doc-3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Reject production native document IDs that differ from the CPU oracle")
val execution = nosql_document_offload_execute_device_validated(
    128,
    64,
    true,
    gpu_wdb_queue_initial(2),
    gpu_wdb_device_backend("cuda", 3, ["gpu_db_document_filter_batch"], true, "cuda-device-0"),
    true,
    3,
    true,
    nosql_budget(),
    ["doc-1", "doc-3"],
    ["doc-1", "doc-4"],
    100,
    190,
    55,
    "cuda-event"
)
expect(nosql_document_offload_used_gpu(execution.execution)).to_be(false)
expect(execution.execution.cpu_authoritative).to_be(true)
expect(execution.execution.submission.dispatch_target).to_equal("cpu_fallback")
expect(execution.execution.submission.reason).to_equal("production-gpu-document-mismatch")
expect(execution.execution.result_ids[1]).to_equal("doc-3")
expect(execution.device_result.production_device_claim).to_be(true)
```

</details>

#### should reject perf-only RAM document filter device evidence

- Keep document filter IDs CPU authoritative without production native timing
- gpu wdb queue initial
- gpu wdb device backend
- nosql budget
   - Expected: execution.execution.submission.dispatch_target equals `cpu_fallback`
   - Expected: execution.execution.submission.reason equals `production-device-not-measured`


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Keep document filter IDs CPU authoritative without production native timing")
val execution = nosql_document_offload_execute_device_validated(
    128,
    64,
    true,
    gpu_wdb_queue_initial(2),
    gpu_wdb_device_backend("mock", 3, ["gpu_db_document_filter_batch"], false, "mock-device"),
    true,
    3,
    true,
    nosql_budget(),
    ["doc-1", "doc-3"],
    ["doc-1", "doc-3"],
    100,
    190,
    55,
    "mock-clock"
)
expect(nosql_document_offload_used_gpu(execution.execution)).to_be(false)
expect(execution.execution.cpu_authoritative).to_be(true)
expect(execution.execution.submission.dispatch_target).to_equal("cpu_fallback")
expect(execution.execution.submission.reason).to_equal("production-device-not-measured")
expect(execution.device_result.production_device_claim).to_be(false)
```

</details>

#### should persist and reload NoSQL document collection metadata

- Round-trip durable document metadata before filtering with offload evidence
- file delete
- var collection = NoSqlDocumentCollection empty
- collection insert
- collection insert
- gpu wdb queue initial
- gpu wdb library with targets
- nosql budget
   - Expected: loaded.document_count() equals `2`
   - Expected: loaded.average_encoded_bytes() equals `192`
   - Expected: execution.result_ids.len() equals `1`
   - Expected: execution.result_ids[0] equals `doc-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Round-trip durable document metadata before filtering with offload evidence")
val path = "/tmp/simple-nosql-document-offload-spec.sdn"
file_delete(path)
var collection = NoSqlDocumentCollection.empty()
collection.insert("doc-1", 128, {"kind": "invoice", "tenant": "a"})
collection.insert("doc-2", 256, {"kind": "note", "tenant": "a"})
expect(collection.save(path)).to_be(true)
expect(file_exists(path)).to_be(true)

val loaded = NoSqlDocumentCollection.load(path)
val execution = loaded.filter_metadata_with_offload(
    "kind",
    "invoice",
    gpu_wdb_queue_initial(2),
    gpu_wdb_library_with_targets("cuda", 1, ["gpu_db_document_filter_batch"]),
    true,
    true,
    nosql_budget()
)
expect(loaded.document_count()).to_equal(2)
expect(loaded.average_encoded_bytes()).to_equal(192)
expect(execution.result_ids.len()).to_equal(1)
expect(execution.result_ids[0]).to_equal("doc-1")
expect(nosql_document_offload_used_gpu(execution)).to_be(true)
val _deleted = file_delete(path)
expect(execution.cpu_authoritative).to_be(true)
```

</details>

#### should offload SSD NoSQL document filters after durable save

- Use saved document metadata as durable generation evidence for GPU batches
- file delete
- var ssd = NoSqlSsdDocumentCollection create
- ssd insert
- ssd insert
- gpu wdb queue initial
- gpu wdb library with targets
- nosql budget
   - Expected: loaded.document_count() equals `2`
   - Expected: loaded.average_encoded_bytes() equals `192`
   - Expected: execution.result_ids[0] equals `doc-1`
   - Expected: execution.submission.dispatch_target equals `gpu_db_document_filter_batch`


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Use saved document metadata as durable generation evidence for GPU batches")
val path = "/tmp/simple-nosql-ssd-document-offload-spec.sdn"
file_delete(path)
var ssd = NoSqlSsdDocumentCollection.create(path)
ssd.insert("doc-1", 128, {"kind": "invoice", "tenant": "a"})
ssd.insert("doc-2", 256, {"kind": "note", "tenant": "a"})
expect(ssd.save()).to_be(true)

val loaded = NoSqlSsdDocumentCollection.open(path)
val execution = loaded.filter_metadata_with_offload(
    "kind",
    "invoice",
    gpu_wdb_queue_initial(2),
    gpu_wdb_library_with_targets("cuda", 1, ["gpu_db_document_filter_batch"]),
    true,
    true,
    nosql_budget()
)
expect(loaded.document_count()).to_equal(2)
expect(loaded.average_encoded_bytes()).to_equal(192)
expect(execution.result_ids[0]).to_equal("doc-1")
expect(nosql_document_offload_used_gpu(execution)).to_be(true)
expect(execution.submission.dispatch_target).to_equal("gpu_db_document_filter_batch")
expect(execution.cpu_authoritative).to_be(true)
val _deleted = file_delete(path)
```

</details>

#### should keep unsaved SSD NoSQL document changes on CPU

- Require durable generation evidence before SSD-backed document filter dispatch
- file delete
- var ssd = NoSqlSsdDocumentCollection create
- ssd insert
- gpu wdb queue initial
- gpu wdb library with targets
- nosql budget
   - Expected: execution.submission.dispatch_target equals `cpu_fallback`
   - Expected: execution.submission.reason equals `stale-generation`
   - Expected: execution.result_ids[0] equals `doc-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Require durable generation evidence before SSD-backed document filter dispatch")
val path = "/tmp/simple-nosql-ssd-document-stale-spec.sdn"
file_delete(path)
var ssd = NoSqlSsdDocumentCollection.create(path)
ssd.insert("doc-1", 128, {"kind": "invoice"})
val execution = ssd.filter_metadata_with_offload(
    "kind",
    "invoice",
    gpu_wdb_queue_initial(2),
    gpu_wdb_library_with_targets("cuda", 1, ["gpu_db_document_filter_batch"]),
    true,
    true,
    nosql_budget()
)
expect(nosql_document_offload_used_gpu(execution)).to_be(false)
expect(execution.submission.dispatch_target).to_equal("cpu_fallback")
expect(execution.submission.reason).to_equal("stale-generation")
expect(execution.result_ids[0]).to_equal("doc-1")
expect(execution.cpu_authoritative).to_be(true)
val _deleted = file_delete(path)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 13 |
| Active scenarios | 13 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** [doc/02_requirements/feature/gpu_web_db_offload.md](doc/02_requirements/feature/gpu_web_db_offload.md)
- **Plan:** [doc/03_plan/agent_tasks/gpu_web_db_offload_impl_status.md](doc/03_plan/agent_tasks/gpu_web_db_offload_impl_status.md)
- **Design:** [doc/05_design/gpu_web_db_offload.md](doc/05_design/gpu_web_db_offload.md)


</details>
