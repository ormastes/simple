# SdnTable Storage Row Batch Offload

> These scenarios verify that the RAM table storage layer can materialize CPU-authoritative row batch manifests from valid SDN rows and feed them into the shared storage-mode offload adapter.

<!-- sdn-diagram:id=storage_row_batch_offload_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=storage_row_batch_offload_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

storage_row_batch_offload_spec -> std
storage_row_batch_offload_spec -> nogc_sync_mut
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=storage_row_batch_offload_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 15 | 15 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# SdnTable Storage Row Batch Offload

These scenarios verify that the RAM table storage layer can materialize CPU-authoritative row batch manifests from valid SDN rows and feed them into the shared storage-mode offload adapter.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Requirements | doc/02_requirements/feature/gpu_web_db_offload.md |
| Plan | doc/03_plan/agent_tasks/gpu_web_db_offload_impl_status.md |
| Design | doc/05_design/gpu_web_db_offload.md |
| Research | N/A |
| Source | `test/01_unit/lib/nogc_sync_mut/database/storage_row_batch_offload_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

These scenarios verify that the RAM table storage layer can materialize
CPU-authoritative row batch manifests from valid SDN rows and feed them into the
shared storage-mode offload adapter.

## Requirements

**Requirements:** doc/02_requirements/feature/gpu_web_db_offload.md

- RAM table batches exclude soft-deleted rows.
- CPU row IDs remain authoritative when GPU accounting accepts a batch.
- Tiny or unregistered batches stay on CPU fallback.
- SSD table batches preserve WAL generation freshness before GPU dispatch.

## Plan

**Plan:** doc/03_plan/agent_tasks/gpu_web_db_offload_impl_status.md

## Design

**Design:** doc/05_design/gpu_web_db_offload.md

## Research

**Research:** N/A

## Examples

Call `storage_row_batch_with_offload` on an `SdnTable` after normal storage
updates. The table computes valid row IDs from storage state, then the shared
storage-mode adapter decides whether the batch can report GPU evidence.

## Syntax

```simple
val execution = table.storage_row_batch_with_offload(workload, state, registry, true, true, budget, 1024)
```

## Scenarios

### SdnTable storage row batch offload

#### should materialize valid row ids from RAM table storage

- Exclude soft-deleted rows before building an offload batch
   - Expected: row_ids.len() equals `2`
   - Expected: row_ids[0] equals `0`
   - Expected: row_ids[1] equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Exclude soft-deleted rows before building an offload batch")
val table = storage_table()
val row_ids = table.valid_row_ids()
expect(row_ids.len()).to_equal(2)
expect(row_ids[0]).to_equal(0)
expect(row_ids[1]).to_equal(2)
```

</details>

#### should dispatch eligible RAM table batches with CPU row ids

- Use the storage-owned row manifest for scan/filter/project accounting
- gpu wdb queue initial
- gpu wdb library with targets
- storage budget
   - Expected: execution.dispatch_target equals `gpu_db_columnar_scan_batch`
   - Expected: execution.row_ids.len() equals `2`
   - Expected: execution.row_ids[0] equals `0`
   - Expected: execution.row_ids[1] equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Use the storage-owned row manifest for scan/filter/project accounting")
val table = storage_table()
val execution = table.storage_row_batch_with_offload(
    DbStorageOffloadWorkload.ScanFilterProject,
    gpu_wdb_queue_initial(2),
    gpu_wdb_library_with_targets("cuda", 1, ["gpu_db_columnar_scan_batch"]),
    true,
    true,
    storage_budget(),
    1024
)
expect(db_storage_offload_used_gpu(execution)).to_be(true)
expect(execution.dispatch_target).to_equal("gpu_db_columnar_scan_batch")
expect(execution.row_ids.len()).to_equal(2)
expect(execution.row_ids[0]).to_equal(0)
expect(execution.row_ids[1]).to_equal(2)
expect(execution.cpu_authoritative).to_be(true)
```

</details>

#### should attach native device evidence to RAM table row batches

- Run storage-owned row manifests through the strict native backend boundary
- gpu wdb queue initial
- storage budget
   - Expected: execution.execution.dispatch_target equals `gpu_db_columnar_scan_batch`
   - Expected: execution.execution.row_ids.len() equals `2`
   - Expected: execution.execution.row_ids[0] equals `0`
   - Expected: execution.execution.row_ids[1] equals `2`
   - Expected: execution.device_execution.device_result.evidence.device_time_us equals `47`


<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Run storage-owned row manifests through the strict native backend boundary")
val table = storage_table()
val execution = table.storage_row_batch_with_device_backend(
    DbStorageOffloadWorkload.ScanFilterProject,
    gpu_wdb_queue_initial(2),
    gpu_wdb_device_backend(
        "cuda",
        4,
        ["gpu_db_columnar_scan_batch"],
        true,
        "cuda-device-0"
    ),
    4,
    true,
    storage_budget(),
    1024,
    100,
    190,
    47,
    "cuda-event"
)
expect(db_storage_offload_used_gpu(execution.execution)).to_be(true)
expect(execution.execution.dispatch_target).to_equal("gpu_db_columnar_scan_batch")
expect(execution.execution.row_ids.len()).to_equal(2)
expect(execution.execution.row_ids[0]).to_equal(0)
expect(execution.execution.row_ids[1]).to_equal(2)
expect(execution.execution.cpu_authoritative).to_be(true)
expect(execution.device_execution.device_result.production_device_claim).to_be(true)
expect(execution.device_execution.device_result.evidence.device_time_us).to_equal(47)
```

</details>

#### should keep tiny RAM table batches on CPU fallback

- Avoid fake GPU evidence for small storage-owned row batches
- gpu wdb queue initial
- gpu wdb library with targets
- storage budget
   - Expected: execution.dispatch_target equals `cpu_fallback`
   - Expected: execution.reason equals `batch-too-small`
   - Expected: execution.row_ids[1] equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Avoid fake GPU evidence for small storage-owned row batches")
val table = storage_table()
val execution = table.storage_row_batch_with_offload(
    DbStorageOffloadWorkload.ScanFilterProject,
    gpu_wdb_queue_initial(2),
    gpu_wdb_library_with_targets("cuda", 1, ["gpu_db_columnar_scan_batch"]),
    true,
    true,
    storage_budget(),
    1
)
expect(db_storage_offload_used_gpu(execution)).to_be(false)
expect(execution.dispatch_target).to_equal("cpu_fallback")
expect(execution.reason).to_equal("batch-too-small")
expect(execution.row_ids[1]).to_equal(2)
```

</details>

#### should keep unregistered RAM table batches on CPU fallback

- Require the row batch target before reporting GPU evidence
- gpu wdb queue initial
- gpu wdb library empty
- storage budget
   - Expected: execution.dispatch_target equals `cpu_fallback`
   - Expected: execution.reason equals `gpu-unavailable`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Require the row batch target before reporting GPU evidence")
val table = storage_table()
val execution = table.storage_row_batch_with_offload(
    DbStorageOffloadWorkload.ScanFilterProject,
    gpu_wdb_queue_initial(2),
    gpu_wdb_library_empty(),
    true,
    true,
    storage_budget(),
    1024
)
expect(db_storage_offload_used_gpu(execution)).to_be(false)
expect(execution.dispatch_target).to_equal("cpu_fallback")
expect(execution.reason).to_equal("gpu-unavailable")
```

</details>

#### should dispatch fresh SSD table batches through the mode-aware helper

- Use storage-owned row manifests with explicit SSD WAL freshness
- gpu wdb queue initial
- gpu wdb library with targets
- storage budget
   - Expected: execution.mode equals `DbStorageOffloadMode.SsdAccelerated`
   - Expected: execution.dispatch_target equals `gpu_db_columnar_scan_batch`
   - Expected: execution.row_ids[0] equals `0`
   - Expected: execution.row_ids[1] equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Use storage-owned row manifests with explicit SSD WAL freshness")
val table = storage_table()
val execution = table.storage_row_batch_with_mode_offload(
    DbStorageOffloadMode.SsdAccelerated,
    DbStorageOffloadWorkload.ScanFilterProject,
    gpu_wdb_queue_initial(2),
    gpu_wdb_library_with_targets("cuda", 1, ["gpu_db_columnar_scan_batch"]),
    true,
    true,
    true,
    storage_budget(),
    1024
)
expect(db_storage_offload_used_gpu(execution)).to_be(true)
expect(execution.mode).to_equal(DbStorageOffloadMode.SsdAccelerated)
expect(execution.dispatch_target).to_equal("gpu_db_columnar_scan_batch")
expect(execution.row_ids[0]).to_equal(0)
expect(execution.row_ids[1]).to_equal(2)
```

</details>

#### should keep stale SSD table batches on CPU fallback

- Do not report GPU evidence when the durable table generation is stale
- gpu wdb queue initial
- gpu wdb library with targets
- storage budget
   - Expected: execution.mode equals `DbStorageOffloadMode.SsdAccelerated`
   - Expected: execution.dispatch_target equals `cpu_fallback`
   - Expected: execution.reason equals `stale-generation`
   - Expected: execution.row_ids[1] equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Do not report GPU evidence when the durable table generation is stale")
val table = storage_table()
val execution = table.storage_row_batch_with_mode_offload(
    DbStorageOffloadMode.SsdAccelerated,
    DbStorageOffloadWorkload.ScanFilterProject,
    gpu_wdb_queue_initial(2),
    gpu_wdb_library_with_targets("cuda", 1, ["gpu_db_columnar_scan_batch"]),
    true,
    false,
    true,
    storage_budget(),
    1024
)
expect(db_storage_offload_used_gpu(execution)).to_be(false)
expect(execution.mode).to_equal(DbStorageOffloadMode.SsdAccelerated)
expect(execution.dispatch_target).to_equal("cpu_fallback")
expect(execution.reason).to_equal("stale-generation")
expect(execution.row_ids[1]).to_equal(2)
```

</details>

#### should dispatch SSD table batches from DBFS snapshot evidence

- Use DBFS-owned freshness instead of a caller-owned WAL boolean
- storage clean ssd snapshot
- gpu wdb queue initial
- gpu wdb library with targets
- storage budget
   - Expected: execution.mode equals `DbStorageOffloadMode.SsdAccelerated`
   - Expected: execution.dispatch_target equals `gpu_db_columnar_scan_batch`
   - Expected: execution.row_ids[0] equals `0`
   - Expected: execution.row_ids[1] equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Use DBFS-owned freshness instead of a caller-owned WAL boolean")
val table = storage_table()
val execution = table.storage_row_batch_with_ssd_snapshot(
    storage_clean_ssd_snapshot(128, 1024),
    DbStorageOffloadWorkload.ScanFilterProject,
    gpu_wdb_queue_initial(2),
    gpu_wdb_library_with_targets("cuda", 1, ["gpu_db_columnar_scan_batch"]),
    true,
    true,
    storage_budget()
)
expect(db_storage_offload_used_gpu(execution)).to_be(true)
expect(execution.mode).to_equal(DbStorageOffloadMode.SsdAccelerated)
expect(execution.dispatch_target).to_equal("gpu_db_columnar_scan_batch")
expect(execution.row_ids[0]).to_equal(0)
expect(execution.row_ids[1]).to_equal(2)
```

</details>

#### should validate SSD table GPU candidate rows against CPU row ids

- Accept SSD table GPU candidates only when they match storage-owned rows
- storage clean ssd snapshot
- gpu wdb queue initial
- gpu wdb library with targets
- storage budget
   - Expected: execution.dispatch_target equals `gpu_db_columnar_scan_batch`
   - Expected: execution.validation_reason equals `gpu-cpu-row-match`
   - Expected: execution.row_ids[0] equals `0`
   - Expected: execution.row_ids[1] equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Accept SSD table GPU candidates only when they match storage-owned rows")
val table = storage_table()
val execution = table.storage_row_batch_with_ssd_snapshot_validated(
    storage_clean_ssd_snapshot(128, 1024),
    DbStorageOffloadWorkload.ScanFilterProject,
    gpu_wdb_queue_initial(2),
    gpu_wdb_library_with_targets("cuda", 1, ["gpu_db_columnar_scan_batch"]),
    true,
    true,
    storage_budget(),
    [0, 2]
)
expect(db_storage_offload_used_gpu(execution)).to_be(true)
expect(execution.dispatch_target).to_equal("gpu_db_columnar_scan_batch")
expect(execution.gpu_candidate_validated).to_be(true)
expect(execution.validation_reason).to_equal("gpu-cpu-row-match")
expect(execution.row_ids[0]).to_equal(0)
expect(execution.row_ids[1]).to_equal(2)
```

</details>

#### should keep CPU row ids when SSD table GPU candidates mismatch

- Reject stale or wrong SSD table GPU candidates without losing CPU authority
- storage clean ssd snapshot
- gpu wdb queue initial
- gpu wdb library with targets
- storage budget
   - Expected: execution.dispatch_target equals `cpu_fallback`
   - Expected: execution.reason equals `gpu-cpu-row-mismatch`
   - Expected: execution.validation_reason equals `gpu-cpu-row-mismatch`
   - Expected: execution.row_ids[0] equals `0`
   - Expected: execution.row_ids[1] equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Reject stale or wrong SSD table GPU candidates without losing CPU authority")
val table = storage_table()
val execution = table.storage_row_batch_with_ssd_snapshot_validated(
    storage_clean_ssd_snapshot(128, 1024),
    DbStorageOffloadWorkload.ScanFilterProject,
    gpu_wdb_queue_initial(2),
    gpu_wdb_library_with_targets("cuda", 1, ["gpu_db_columnar_scan_batch"]),
    true,
    true,
    storage_budget(),
    [0, 99]
)
expect(db_storage_offload_used_gpu(execution)).to_be(false)
expect(execution.dispatch_target).to_equal("cpu_fallback")
expect(execution.reason).to_equal("gpu-cpu-row-mismatch")
expect(execution.gpu_candidate_validated).to_be(false)
expect(execution.validation_reason).to_equal("gpu-cpu-row-mismatch")
expect(execution.cpu_authoritative).to_be(true)
expect(execution.row_ids[0]).to_equal(0)
expect(execution.row_ids[1]).to_equal(2)
```

</details>

#### should materialize SSD table rows after candidate validation

- Return projected SSD rows when materialized row IDs match the GPU candidate
- storage clean materialized rows
- gpu wdb queue initial
- gpu wdb library with targets
- storage budget
   - Expected: execution.offload.validation_reason equals `gpu-cpu-row-match`
   - Expected: execution.rows.len() equals `2`
   - Expected: execution.rows[0].get("id")? equals `97`
   - Expected: execution.rows[0].get("valid")? equals `49`
   - Expected: execution.rows[1].get("id")? equals `99`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Return projected SSD rows when materialized row IDs match the GPU candidate")
val table = storage_table()
val execution = table.storage_row_batch_with_ssd_materialized_rows(
    storage_clean_materialized_rows(),
    gpu_wdb_queue_initial(2),
    gpu_wdb_library_with_targets("cuda", 1, ["gpu_db_columnar_scan_batch"]),
    true,
    true,
    storage_budget(),
    [0, 2]
)
expect(db_storage_offload_used_gpu(execution.offload)).to_be(true)
expect(execution.offload.gpu_candidate_validated).to_be(true)
expect(execution.offload.validation_reason).to_equal("gpu-cpu-row-match")
expect(execution.rows.len()).to_equal(2)
expect(execution.rows[0].get("id")?).to_equal("97")
expect(execution.rows[0].get("valid")?).to_equal("49")
expect(execution.rows[1].get("id")?).to_equal("99")
```

</details>

#### should keep CPU table rows when SSD materialized row candidates mismatch

- Reject projected SSD rows when candidate IDs disagree with materialized row IDs
- storage clean materialized rows
- gpu wdb queue initial
- gpu wdb library with targets
- storage budget
   - Expected: execution.offload.dispatch_target equals `cpu_fallback`
   - Expected: execution.offload.validation_reason equals `gpu-cpu-row-mismatch`
   - Expected: execution.rows.len() equals `2`
   - Expected: execution.rows[0].get("id")? equals `a`
   - Expected: execution.rows[1].get("id")? equals `c`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Reject projected SSD rows when candidate IDs disagree with materialized row IDs")
val table = storage_table()
val execution = table.storage_row_batch_with_ssd_materialized_rows(
    storage_clean_materialized_rows(),
    gpu_wdb_queue_initial(2),
    gpu_wdb_library_with_targets("cuda", 1, ["gpu_db_columnar_scan_batch"]),
    true,
    true,
    storage_budget(),
    [0, 99]
)
expect(db_storage_offload_used_gpu(execution.offload)).to_be(false)
expect(execution.offload.dispatch_target).to_equal("cpu_fallback")
expect(execution.offload.validation_reason).to_equal("gpu-cpu-row-mismatch")
expect(execution.rows.len()).to_equal(2)
expect(execution.rows[0].get("id")?).to_equal("a")
expect(execution.rows[1].get("id")?).to_equal("c")
```

</details>

#### should replace table rows from SSD materialization only after native candidates match

- Require native timing and materialized row agreement before returning SSD rows
- storage clean materialized rows
- gpu wdb queue initial
- storage budget
   - Expected: execution.offload.execution.validation_reason equals `production-gpu-row-match`
   - Expected: execution.rows.len() equals `2`
   - Expected: execution.rows[0].get("id")? equals `97`
   - Expected: execution.rows[0].get("valid")? equals `49`
   - Expected: execution.rows[1].get("id")? equals `99`


<details>
<summary>Executable SSpec</summary>

Runnable source: 30 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Require native timing and materialized row agreement before returning SSD rows")
val table = storage_table()
val execution = table.storage_row_batch_with_ssd_materialized_rows_device_validated(
    storage_clean_materialized_rows(),
    gpu_wdb_queue_initial(2),
    gpu_wdb_device_backend(
        "cuda",
        4,
        ["gpu_db_columnar_scan_batch"],
        true,
        "cuda-device-0"
    ),
    4,
    true,
    storage_budget(),
    [0, 2],
    100,
    190,
    47,
    "cuda-event"
)
expect(db_storage_offload_used_gpu(execution.offload.execution)).to_be(true)
expect(execution.offload.execution.cpu_authoritative).to_be(false)
expect(execution.offload.execution.gpu_candidate_validated).to_be(true)
expect(execution.offload.execution.validation_reason).to_equal("production-gpu-row-match")
expect(execution.offload.device_execution.device_result.production_device_claim).to_be(true)
expect(execution.rows.len()).to_equal(2)
expect(execution.rows[0].get("id")?).to_equal("97")
expect(execution.rows[0].get("valid")?).to_equal("49")
expect(execution.rows[1].get("id")?).to_equal("99")
```

</details>

#### should keep CPU table rows when native SSD materialized candidates mismatch

- Reject native SSD row replacement when candidate IDs disagree
- storage clean materialized rows
- gpu wdb queue initial
- storage budget
   - Expected: execution.offload.execution.dispatch_target equals `cpu_fallback`
   - Expected: execution.offload.execution.validation_reason equals `production-gpu-row-mismatch`
   - Expected: execution.rows.len() equals `2`
   - Expected: execution.rows[0].get("id")? equals `a`
   - Expected: execution.rows[1].get("id")? equals `c`


<details>
<summary>Executable SSpec</summary>

Runnable source: 30 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Reject native SSD row replacement when candidate IDs disagree")
val table = storage_table()
val execution = table.storage_row_batch_with_ssd_materialized_rows_device_validated(
    storage_clean_materialized_rows(),
    gpu_wdb_queue_initial(2),
    gpu_wdb_device_backend(
        "cuda",
        4,
        ["gpu_db_columnar_scan_batch"],
        true,
        "cuda-device-0"
    ),
    4,
    true,
    storage_budget(),
    [0, 99],
    100,
    190,
    47,
    "cuda-event"
)
expect(db_storage_offload_used_gpu(execution.offload.execution)).to_be(false)
expect(execution.offload.execution.dispatch_target).to_equal("cpu_fallback")
expect(execution.offload.execution.cpu_authoritative).to_be(true)
expect(execution.offload.execution.gpu_candidate_validated).to_be(false)
expect(execution.offload.execution.validation_reason).to_equal("production-gpu-row-mismatch")
expect(execution.offload.device_execution.device_result.production_device_claim).to_be(true)
expect(execution.rows.len()).to_equal(2)
expect(execution.rows[0].get("id")?).to_equal("a")
expect(execution.rows[1].get("id")?).to_equal("c")
```

</details>

#### should keep stale DBFS snapshot table batches on CPU fallback

- Let DBFS dirty-page evidence block SSD table GPU dispatch
- storage dirty ssd snapshot
- gpu wdb queue initial
- gpu wdb library with targets
- storage budget
   - Expected: execution.mode equals `DbStorageOffloadMode.SsdAccelerated`
   - Expected: execution.reason equals `stale-generation`
   - Expected: execution.row_ids[1] equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Let DBFS dirty-page evidence block SSD table GPU dispatch")
val table = storage_table()
val execution = table.storage_row_batch_with_ssd_snapshot(
    storage_dirty_ssd_snapshot(128, 1024),
    DbStorageOffloadWorkload.ScanFilterProject,
    gpu_wdb_queue_initial(2),
    gpu_wdb_library_with_targets("cuda", 1, ["gpu_db_columnar_scan_batch"]),
    true,
    true,
    storage_budget()
)
expect(db_storage_offload_used_gpu(execution)).to_be(false)
expect(execution.mode).to_equal(DbStorageOffloadMode.SsdAccelerated)
expect(execution.reason).to_equal("stale-generation")
expect(execution.row_ids[1]).to_equal(2)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 15 |
| Active scenarios | 15 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** [doc/02_requirements/feature/gpu_web_db_offload.md](doc/02_requirements/feature/gpu_web_db_offload.md)
- **Plan:** [doc/03_plan/agent_tasks/gpu_web_db_offload_impl_status.md](doc/03_plan/agent_tasks/gpu_web_db_offload_impl_status.md)
- **Design:** [doc/05_design/gpu_web_db_offload.md](doc/05_design/gpu_web_db_offload.md)


</details>
