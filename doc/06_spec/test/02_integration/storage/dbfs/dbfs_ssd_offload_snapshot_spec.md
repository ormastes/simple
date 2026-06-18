# DBFS SSD Offload Snapshot

> These scenarios verify the DBFS-owned freshness snapshot used before SSD-accelerated storage-mode GPU offload admission.

<!-- sdn-diagram:id=dbfs_ssd_offload_snapshot_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=dbfs_ssd_offload_snapshot_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

dbfs_ssd_offload_snapshot_spec -> std
dbfs_ssd_offload_snapshot_spec -> nogc_sync_mut
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=dbfs_ssd_offload_snapshot_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 14 | 14 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# DBFS SSD Offload Snapshot

These scenarios verify the DBFS-owned freshness snapshot used before SSD-accelerated storage-mode GPU offload admission.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Requirements | doc/02_requirements/feature/gpu_web_db_offload.md |
| Plan | doc/03_plan/agent_tasks/gpu_web_db_offload_impl_status.md |
| Design | doc/05_design/gpu_web_db_offload.md |
| Research | N/A |
| Source | `test/02_integration/storage/dbfs/dbfs_ssd_offload_snapshot_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

These scenarios verify the DBFS-owned freshness snapshot used before
SSD-accelerated storage-mode GPU offload admission.

## Requirements

**Requirements:** doc/02_requirements/feature/gpu_web_db_offload.md

- SSD-accelerated DB offload must require durable WAL and clean checkpoint
  evidence.
- Dirty pager pages keep SSD batches on CPU.
- WAL tail beyond durable LSN keeps SSD batches on CPU.
- Current DBFS snapshots can drive the storage-mode SSD adapter.

## Plan

**Plan:** doc/03_plan/agent_tasks/gpu_web_db_offload_impl_status.md

## Design

**Design:** doc/05_design/gpu_web_db_offload.md

## Research

**Research:** N/A

## Examples

Build a `DbfsSsdOffloadSnapshot` from pager, WAL, checkpoint, and namespace
B-tree state, then pass it to `db_storage_execute_rows_for_ssd_snapshot`.

## Scenarios

### DBFS SSD offload freshness snapshot

#### should report current when checkpoint, WAL, pager, and B-tree are clean

- Build a snapshot from flushed WAL, clean checkpoint, and clean pager state
   - Expected: snapshot.pager_dirty_count equals `0`
   - Expected: snapshot.wal_tail_lsn equals `snapshot.wal_durable_lsn`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Build a snapshot from flushed WAL, clean checkpoint, and clean pager state")
val snapshot = clean_snapshot(128, 64)
expect(dbfs_ssd_snapshot_current(snapshot)).to_be(true)
expect(snapshot.pager_dirty_count).to_equal(0)
expect(snapshot.wal_tail_lsn).to_equal(snapshot.wal_durable_lsn)
```

</details>

#### should derive scan row ids from a current DBFS SSD snapshot

- Build a row-id manifest from DBFS snapshot row count rather than caller CPU state
   - Expected: row_ids.len() equals `3`
   - Expected: row_ids[0] equals `0`
   - Expected: row_ids[1] equals `1`
   - Expected: row_ids[2] equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Build a row-id manifest from DBFS snapshot row count rather than caller CPU state")
val snapshot = clean_snapshot(3, 64)
val row_ids = dbfs_ssd_snapshot_scan_row_ids(snapshot)
expect(row_ids.len()).to_equal(3)
expect(row_ids[0]).to_equal(0)
expect(row_ids[1]).to_equal(1)
expect(row_ids[2]).to_equal(2)
```

</details>

#### should report stale when the pager has dirty pages

- Dirty pager pages block SSD offload even with a clean checkpoint
- pager write page
- wal flush
- checkpoints checkpoint now
   - Expected: snapshot.pager_dirty_count equals `1`
   - Expected: dbfs_ssd_snapshot_scan_row_ids(snapshot).len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Dirty pager pages block SSD offload even with a clean checkpoint")
val pager = DbfsPager.new(8)
val page = pager.alloc_page().unwrap()
pager.write_page(page, PageData.zeroed(), 0, 0).unwrap()
val wal = DbfsWal.new()
wal.flush().unwrap()
val checkpoints = CheckpointEngine.new()
checkpoints.checkpoint_now(1).unwrap()
val btree = NsBTree.new()
val snapshot = dbfs_ssd_offload_snapshot(pager, wal, checkpoints, btree, 128, 64)
expect(dbfs_ssd_snapshot_current(snapshot)).to_be(false)
expect(snapshot.pager_dirty_count).to_equal(1)
expect(dbfs_ssd_snapshot_scan_row_ids(snapshot).len()).to_equal(0)
```

</details>

#### should report stale when WAL tail is beyond durable LSN

- Unflushed WAL tail blocks SSD offload
- wal append
- checkpoints checkpoint now


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Unflushed WAL tail blocks SSD offload")
val pager = DbfsPager.new(8)
val wal = DbfsWal.new()
wal.append(commit_record(2)).unwrap()
val checkpoints = CheckpointEngine.new()
checkpoints.checkpoint_now(1).unwrap()
val btree = NsBTree.new()
val snapshot = dbfs_ssd_offload_snapshot(pager, wal, checkpoints, btree, 128, 64)
expect(dbfs_ssd_snapshot_current(snapshot)).to_be(false)
expect(snapshot.wal_tail_lsn > snapshot.wal_durable_lsn).to_be(true)
```

</details>

#### should report stale when checkpoint is older than B-tree generation

- Namespace B-tree changes require a fresh checkpoint before SSD offload
- wal flush
- btree insert


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Namespace B-tree changes require a fresh checkpoint before SSD offload")
val pager = DbfsPager.new(8)
val wal = DbfsWal.new()
wal.flush().unwrap()
val checkpoints = CheckpointEngine.new()
val btree = NsBTree.new()
btree.insert(ns_dentry_key(1, 10), ns_ino(42)).unwrap()
val snapshot = dbfs_ssd_offload_snapshot(pager, wal, checkpoints, btree, 128, 64)
expect(dbfs_ssd_snapshot_current(snapshot)).to_be(false)
expect(snapshot.clean_checkpoint_available).to_be(false)
```

</details>

#### should drive SSD storage-mode GPU admission from DBFS snapshot evidence

- Use current DBFS snapshot evidence instead of a caller-owned freshness boolean
- gpu wdb queue initial
- gpu wdb library with targets
- ssd budget
   - Expected: execution.mode equals `DbStorageOffloadMode.SsdAccelerated`
   - Expected: execution.dispatch_target equals `gpu_db_columnar_scan_batch`
   - Expected: execution.row_ids.len() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Use current DBFS snapshot evidence instead of a caller-owned freshness boolean")
val snapshot = clean_snapshot(128, 64)
val execution = db_storage_execute_rows_for_ssd_snapshot(
    snapshot,
    DbStorageOffloadWorkload.ScanFilterProject,
    gpu_wdb_queue_initial(4),
    gpu_wdb_library_with_targets("cuda", 1, ["gpu_db_columnar_scan_batch"]),
    true,
    true,
    ssd_budget(),
    [1, 2, 3]
)
expect(db_storage_offload_used_gpu(execution)).to_be(true)
expect(execution.mode).to_equal(DbStorageOffloadMode.SsdAccelerated)
expect(execution.dispatch_target).to_equal("gpu_db_columnar_scan_batch")
expect(execution.row_ids.len()).to_equal(3)
```

</details>

#### should drive SSD scan execution from DBFS-owned row ids

- Use snapshot-derived row ids for scan/filter/project execution
- gpu wdb queue initial
- gpu wdb library with targets
- ssd budget
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
step("Use snapshot-derived row ids for scan/filter/project execution")
val snapshot = clean_snapshot(3, 64)
val execution = db_storage_execute_ssd_snapshot_scan(
    snapshot,
    gpu_wdb_queue_initial(4),
    gpu_wdb_library_with_targets("cuda", 1, ["gpu_db_columnar_scan_batch"]),
    true,
    true,
    ssd_budget()
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

#### should materialize SSD scan rows from DBFS pager page cursors

- Read clean DBFS pages to produce CPU-authoritative scan rows
- pager write page
- pager write page
- pager flush dirty
- wal append
- wal flush
- checkpoints checkpoint now
   - Expected: materialized.reason equals `ssd-page-cursor-materialized`
   - Expected: materialized.page_cursor_ids[0] equals `first.id`
   - Expected: materialized.row_ids[0] equals `42`
   - Expected: materialized.row_ids[1] equals `77`
   - Expected: materialized.row_payload_bytes[0] equals `9`
   - Expected: materialized.row_payload_bytes[1] equals `11`


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Read clean DBFS pages to produce CPU-authoritative scan rows")
val pager = DbfsPager.new(8)
val first = pager.alloc_page().unwrap()
val second = pager.alloc_page().unwrap()
pager.write_page(first, row_page_with_payload(42, 9), 0, 0).unwrap()
pager.write_page(second, row_page_with_payload(77, 11), 0, 0).unwrap()
pager.flush_dirty().unwrap()
val wal = DbfsWal.new()
wal.append(commit_record(3)).unwrap()
wal.flush().unwrap()
val checkpoints = CheckpointEngine.new()
checkpoints.checkpoint_now(1).unwrap()
val btree = NsBTree.new()
val snapshot = dbfs_ssd_offload_snapshot(pager, wal, checkpoints, btree, 2, 64)
val materialized = dbfs_ssd_snapshot_materialize_scan(snapshot, pager, [first.id, second.id])
expect(materialized.current).to_be(true)
expect(materialized.materialized).to_be(true)
expect(materialized.reason).to_equal("ssd-page-cursor-materialized")
expect(materialized.page_cursor_ids[0]).to_equal(first.id)
expect(materialized.row_ids[0]).to_equal(42)
expect(materialized.row_ids[1]).to_equal(77)
expect(materialized.row_payload_bytes[0]).to_equal(9)
expect(materialized.row_payload_bytes[1]).to_equal(11)
```

</details>

#### should carry SSD schema projection and predicate metadata

- Materialize clean page cursors with table schema and projected columns
- pager write page
- pager write page
- pager flush dirty
- wal append
- wal flush
- checkpoints checkpoint now
   - Expected: materialized.reason equals `ssd-page-cursor-materialized`
   - Expected: materialized.schema_columns.len() equals `3`
   - Expected: materialized.projected_columns.len() equals `2`
   - Expected: materialized.projected_columns[1] equals `amount`
   - Expected: materialized.predicate equals `status = active`
   - Expected: materialized.bytes_per_row equals `96`
   - Expected: materialized.row_ids[0] equals `12`
   - Expected: materialized.row_ids[1] equals `34`
   - Expected: materialized.row_payload_bytes[0] equals `21`
   - Expected: materialized.row_payload_bytes[1] equals `55`


<details>
<summary>Executable SSpec</summary>

Runnable source: 33 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Materialize clean page cursors with table schema and projected columns")
val pager = DbfsPager.new(8)
val first = pager.alloc_page().unwrap()
val second = pager.alloc_page().unwrap()
pager.write_page(first, row_page_with_payload(12, 21), 0, 0).unwrap()
pager.write_page(second, row_page_with_payload(34, 55), 0, 0).unwrap()
pager.flush_dirty().unwrap()
val wal = DbfsWal.new()
wal.append(commit_record(4)).unwrap()
wal.flush().unwrap()
val checkpoints = CheckpointEngine.new()
checkpoints.checkpoint_now(1).unwrap()
val btree = NsBTree.new()
val snapshot = dbfs_ssd_offload_snapshot(pager, wal, checkpoints, btree, 2, 96)
val materialized = dbfs_ssd_snapshot_materialize_projected_scan(
    snapshot,
    pager,
    [first.id, second.id],
    ["id", "status", "amount"],
    ["id", "amount"],
    "status = active"
)
expect(materialized.materialized).to_be(true)
expect(materialized.reason).to_equal("ssd-page-cursor-materialized")
expect(materialized.schema_columns.len()).to_equal(3)
expect(materialized.projected_columns.len()).to_equal(2)
expect(materialized.projected_columns[1]).to_equal("amount")
expect(materialized.predicate).to_equal("status = active")
expect(materialized.bytes_per_row).to_equal(96)
expect(materialized.row_ids[0]).to_equal(12)
expect(materialized.row_ids[1]).to_equal(34)
expect(materialized.row_payload_bytes[0]).to_equal(21)
expect(materialized.row_payload_bytes[1]).to_equal(55)
```

</details>

#### should materialize projected SSD row values from page bytes

- Expose projected table values, not only row IDs and payload bytes
- pager write page
- pager write page
- pager flush dirty
- wal append
- wal flush
- checkpoints checkpoint now
   - Expected: materialized.projected_rows.len() equals `2`
   - Expected: materialized.projected_rows[0].row_id equals `12`
   - Expected: materialized.projected_rows[0].values["id"] equals `12`
   - Expected: materialized.projected_rows[0].values["amount"] equals `90`
   - Expected: materialized.projected_rows[1].row_id equals `34`
   - Expected: materialized.projected_rows[1].values["id"] equals `34`
   - Expected: materialized.projected_rows[1].values["amount"] equals `91`


<details>
<summary>Executable SSpec</summary>

Runnable source: 30 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Expose projected table values, not only row IDs and payload bytes")
val pager = DbfsPager.new(8)
val first = pager.alloc_page().unwrap()
val second = pager.alloc_page().unwrap()
pager.write_page(first, row_page_with_columns(12, 1, 90), 0, 0).unwrap()
pager.write_page(second, row_page_with_columns(34, 2, 91), 0, 0).unwrap()
pager.flush_dirty().unwrap()
val wal = DbfsWal.new()
wal.append(commit_record(7)).unwrap()
wal.flush().unwrap()
val checkpoints = CheckpointEngine.new()
checkpoints.checkpoint_now(1).unwrap()
val btree = NsBTree.new()
val snapshot = dbfs_ssd_offload_snapshot(pager, wal, checkpoints, btree, 2, 96)
val materialized = dbfs_ssd_snapshot_materialize_projected_scan(
    snapshot,
    pager,
    [first.id, second.id],
    ["id", "status", "amount"],
    ["id", "amount"],
    "status > 0"
)
expect(materialized.materialized).to_be(true)
expect(materialized.projected_rows.len()).to_equal(2)
expect(materialized.projected_rows[0].row_id).to_equal(12)
expect(materialized.projected_rows[0].values["id"]).to_equal("12")
expect(materialized.projected_rows[0].values["amount"]).to_equal("90")
expect(materialized.projected_rows[1].row_id).to_equal(34)
expect(materialized.projected_rows[1].values["id"]).to_equal("34")
expect(materialized.projected_rows[1].values["amount"]).to_equal("91")
```

</details>

#### should validate projected SSD materialized scan GPU candidates

- Compare GPU candidates with DBFS projected page-cursor rows
- pager write page
- page ids push
- expected ids push
- pager flush dirty
- wal append
- wal flush
- checkpoints checkpoint now
- gpu wdb queue initial
- gpu wdb library with targets
- ssd budget
   - Expected: execution.mode equals `DbStorageOffloadMode.SsdAccelerated`
   - Expected: execution.dispatch_target equals `gpu_db_columnar_scan_batch`
   - Expected: execution.validation_reason equals `gpu-cpu-row-match`
   - Expected: execution.row_ids.len() equals `16`
   - Expected: execution.row_ids[0] equals `20`
   - Expected: execution.row_ids[15] equals `35`
   - Expected: materialized.row_payload_bytes[0] equals `80`
   - Expected: materialized.row_payload_bytes[15] equals `95`
   - Expected: execution.profile.data_path equals `GpuWdbCoarseDataPath.SsdStagedBatch`


<details>
<summary>Executable SSpec</summary>

Runnable source: 48 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Compare GPU candidates with DBFS projected page-cursor rows")
val pager = DbfsPager.new(32)
var page_ids: [i64] = []
var expected_ids: [i64] = []
var i = 0
while i < 16:
    val page = pager.alloc_page().unwrap()
    val row_id = 20 + i
    pager.write_page(page, row_page_with_payload(row_id, 80 + i), 0, 0).unwrap()
    page_ids.push(page.id)
    expected_ids.push(row_id)
    i = i + 1
pager.flush_dirty().unwrap()
val wal = DbfsWal.new()
wal.append(commit_record(5)).unwrap()
wal.flush().unwrap()
val checkpoints = CheckpointEngine.new()
checkpoints.checkpoint_now(1).unwrap()
val btree = NsBTree.new()
val snapshot = dbfs_ssd_offload_snapshot(pager, wal, checkpoints, btree, 16, 96)
val materialized = dbfs_ssd_snapshot_materialize_projected_scan(
    snapshot,
    pager,
    page_ids,
    ["id", "status", "amount"],
    ["id", "amount"],
    "status = active"
)
val execution = db_storage_execute_ssd_materialized_scan_validated(
    materialized,
    gpu_wdb_queue_initial(4),
    gpu_wdb_library_with_targets("cuda", 1, ["gpu_db_columnar_scan_batch"]),
    true,
    true,
    ssd_budget(),
    expected_ids
)
expect(db_storage_offload_used_gpu(execution)).to_be(true)
expect(execution.mode).to_equal(DbStorageOffloadMode.SsdAccelerated)
expect(execution.dispatch_target).to_equal("gpu_db_columnar_scan_batch")
expect(execution.gpu_candidate_validated).to_be(true)
expect(execution.validation_reason).to_equal("gpu-cpu-row-match")
expect(execution.row_ids.len()).to_equal(16)
expect(execution.row_ids[0]).to_equal(20)
expect(execution.row_ids[15]).to_equal(35)
expect(materialized.row_payload_bytes[0]).to_equal(80)
expect(materialized.row_payload_bytes[15]).to_equal(95)
expect(execution.profile.data_path).to_equal(GpuWdbCoarseDataPath.SsdStagedBatch)
```

</details>

#### should reject mismatched projected SSD materialized scan GPU candidates

- Preserve DBFS projected page-cursor rows when GPU candidates differ
- pager write page
- page ids push
- candidate ids push
- pager flush dirty
- wal append
- wal flush
- checkpoints checkpoint now
- gpu wdb queue initial
- gpu wdb library with targets
- ssd budget
   - Expected: execution.dispatch_target equals `cpu_fallback`
   - Expected: execution.reason equals `gpu-cpu-row-mismatch`
   - Expected: execution.row_ids[0] equals `40`
   - Expected: execution.row_ids[15] equals `55`
   - Expected: execution.profile.data_path equals `GpuWdbCoarseDataPath.SsdStagedBatch`


<details>
<summary>Executable SSpec</summary>

Runnable source: 45 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Preserve DBFS projected page-cursor rows when GPU candidates differ")
val pager = DbfsPager.new(32)
var page_ids: [i64] = []
var candidate_ids: [i64] = []
var i = 0
while i < 16:
    val page = pager.alloc_page().unwrap()
    val row_id = 40 + i
    pager.write_page(page, row_page(row_id), 0, 0).unwrap()
    page_ids.push(page.id)
    candidate_ids.push(row_id)
    i = i + 1
candidate_ids[15] = 99
pager.flush_dirty().unwrap()
val wal = DbfsWal.new()
wal.append(commit_record(6)).unwrap()
wal.flush().unwrap()
val checkpoints = CheckpointEngine.new()
checkpoints.checkpoint_now(1).unwrap()
val btree = NsBTree.new()
val snapshot = dbfs_ssd_offload_snapshot(pager, wal, checkpoints, btree, 16, 96)
val materialized = dbfs_ssd_snapshot_materialize_projected_scan(
    snapshot,
    pager,
    page_ids,
    ["id", "status", "amount"],
    ["id", "amount"],
    "status = active"
)
val execution = db_storage_execute_ssd_materialized_scan_validated(
    materialized,
    gpu_wdb_queue_initial(4),
    gpu_wdb_library_with_targets("cuda", 1, ["gpu_db_columnar_scan_batch"]),
    true,
    true,
    ssd_budget(),
    candidate_ids
)
expect(db_storage_offload_used_gpu(execution)).to_be(false)
expect(execution.dispatch_target).to_equal("cpu_fallback")
expect(execution.reason).to_equal("gpu-cpu-row-mismatch")
expect(execution.gpu_candidate_validated).to_be(false)
expect(execution.row_ids[0]).to_equal(40)
expect(execution.row_ids[15]).to_equal(55)
expect(execution.profile.data_path).to_equal(GpuWdbCoarseDataPath.SsdStagedBatch)
```

</details>

#### should reject SSD projected scans with unknown columns

- Validate projected columns against the DBFS-owned schema metadata
   - Expected: materialized.reason equals `ssd-projection-column-missing`
   - Expected: materialized.schema_columns[1] equals `status`
   - Expected: materialized.projected_columns[1] equals `missing`
   - Expected: materialized.row_ids.len() equals `0`
   - Expected: materialized.projected_rows.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Validate projected columns against the DBFS-owned schema metadata")
val snapshot = clean_snapshot(2, 64)
val pager = DbfsPager.new(8)
val materialized = dbfs_ssd_snapshot_materialize_projected_scan(
    snapshot,
    pager,
    [1],
    ["id", "status"],
    ["id", "missing"],
    "status = active"
)
expect(materialized.current).to_be(true)
expect(materialized.materialized).to_be(false)
expect(materialized.reason).to_equal("ssd-projection-column-missing")
expect(materialized.schema_columns[1]).to_equal("status")
expect(materialized.projected_columns[1]).to_equal("missing")
expect(materialized.row_ids.len()).to_equal(0)
expect(materialized.projected_rows.len()).to_equal(0)
```

</details>

#### should reject missing SSD page cursors during scan materialization

- Do not synthesize rows when a DBFS page cursor cannot be read
   - Expected: materialized.reason equals `ssd-page-cursor-missing`
   - Expected: materialized.row_ids.len() equals `0`
   - Expected: materialized.projected_rows.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Do not synthesize rows when a DBFS page cursor cannot be read")
val snapshot = clean_snapshot(2, 64)
val pager = DbfsPager.new(8)
val materialized = dbfs_ssd_snapshot_materialize_scan(snapshot, pager, [999])
expect(materialized.current).to_be(true)
expect(materialized.materialized).to_be(false)
expect(materialized.reason).to_equal("ssd-page-cursor-missing")
expect(materialized.row_ids.len()).to_equal(0)
expect(materialized.projected_rows.len()).to_equal(0)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 14 |
| Active scenarios | 14 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** [doc/02_requirements/feature/gpu_web_db_offload.md](doc/02_requirements/feature/gpu_web_db_offload.md)
- **Plan:** [doc/03_plan/agent_tasks/gpu_web_db_offload_impl_status.md](doc/03_plan/agent_tasks/gpu_web_db_offload_impl_status.md)
- **Design:** [doc/05_design/gpu_web_db_offload.md](doc/05_design/gpu_web_db_offload.md)


</details>
