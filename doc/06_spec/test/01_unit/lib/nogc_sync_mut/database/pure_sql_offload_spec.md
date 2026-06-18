# Pure SQL GPU Offload Adapter Integration

> These scenarios verify that engine-owned pure-SQL SELECT execution can report storage-mode GPU offload evidence for join and aggregate work while keeping the existing CPU SQL rows authoritative.

<!-- sdn-diagram:id=pure_sql_offload_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=pure_sql_offload_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

pure_sql_offload_spec -> std
pure_sql_offload_spec -> nogc_sync_mut
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=pure_sql_offload_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 24 | 24 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Pure SQL GPU Offload Adapter Integration

These scenarios verify that engine-owned pure-SQL SELECT execution can report storage-mode GPU offload evidence for join and aggregate work while keeping the existing CPU SQL rows authoritative.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Requirements | doc/02_requirements/feature/gpu_web_db_offload.md |
| Plan | doc/03_plan/agent_tasks/gpu_web_db_offload_impl_status.md |
| Design | doc/05_design/gpu_web_db_offload.md |
| Research | N/A |
| Source | `test/01_unit/lib/nogc_sync_mut/database/pure_sql_offload_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

These scenarios verify that engine-owned pure-SQL SELECT execution can report
storage-mode GPU offload evidence for join and aggregate work while keeping the
existing CPU SQL rows authoritative.

## Requirements

**Requirements:** doc/02_requirements/feature/gpu_web_db_offload.md

- Pure-SQL join and aggregate paths can be observed as join/aggregate offload
  work.
- CPU SQL result rows remain authoritative for all current join/aggregate shapes.
- SSD offload still respects WAL freshness evidence.

## Plan

**Plan:** doc/03_plan/agent_tasks/gpu_web_db_offload_impl_status.md

## Design

**Design:** doc/05_design/gpu_web_db_offload.md

## Research

**Research:** N/A

## Examples

Call `query_with_offload_profile` with a RAM-heavy or SSD-accelerated DB
profile. The returned rows come from the existing pure-SQL CPU engine while the
offload record describes whether the SELECT shape was eligible for
`gpu_db_join_aggregate_batch`.

## Syntax

```simple
val execution = db.query_with_offload_profile(sql, [], profile, mode, true, 512).unwrap()
```

## Scenarios

### Pure SQL GPU offload adapter integration

#### should report filtered projection SELECT work as scan filter project offload

- Execute an engine-owned SQL projection/filter and preserve CPU row output
- var db = sql offload db
- sql offload profile
   - Expected: execution.rows.len() equals `1`
   - Expected: execution.rows[0].values[0].to_text() equals `Bob`
   - Expected: execution.offload.workload equals `DbStorageOffloadWorkload.ScanFilterProject`
   - Expected: execution.offload.dispatch_target equals `gpu_db_columnar_scan_batch`
   - Expected: execution.offload.validation_reason equals `gpu-candidate-not-evaluated`
   - Expected: execution.offload.profile.data_path equals `GpuWdbCoarseDataPath.GpuResidentBatch`
   - Expected: execution.result_source equals `cpu_select`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Execute an engine-owned SQL projection/filter and preserve CPU row output")
var db = sql_offload_db()
val execution = db.query_with_offload_profile(
    "SELECT name FROM users WHERE uid > 1",
    [],
    sql_offload_profile(),
    DbStorageOffloadMode.RamOnly,
    true,
    512
).unwrap()

expect(execution.rows.len()).to_equal(1)
expect(execution.rows[0].values[0].to_text()).to_equal("Bob")
expect(execution.offload.workload).to_equal(DbStorageOffloadWorkload.ScanFilterProject)
expect(db_storage_offload_used_gpu(execution.offload)).to_be(true)
expect(execution.offload.dispatch_target).to_equal("gpu_db_columnar_scan_batch")
expect(execution.offload.cpu_authoritative).to_be(true)
expect(execution.offload.gpu_candidate_validated).to_be(false)
expect(execution.offload.validation_reason).to_equal("gpu-candidate-not-evaluated")
expect(execution.offload.profile.data_path).to_equal(GpuWdbCoarseDataPath.GpuResidentBatch)
expect(db_storage_profile_allows_gpu(execution.offload)).to_be(true)
expect(execution.result_source).to_equal("cpu_select")
```

</details>

#### should report join SELECT work as join aggregate offload

- Execute an engine-owned SQL join and preserve CPU row output
- var db = sql offload db
- sql offload profile
   - Expected: execution.rows.len() equals `3`
   - Expected: execution.rows[0].values[1].to_text() equals `Alice`
   - Expected: execution.offload.workload equals `DbStorageOffloadWorkload.JoinAggregate`
   - Expected: execution.offload.dispatch_target equals `gpu_db_join_aggregate_batch`
   - Expected: execution.offload.validation_reason equals `gpu-candidate-not-evaluated`
   - Expected: execution.offload.profile.data_path equals `GpuWdbCoarseDataPath.GpuResidentBatch`
   - Expected: execution.result_source equals `cpu_select`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Execute an engine-owned SQL join and preserve CPU row output")
var db = sql_offload_db()
val execution = db.query_with_offload_profile(
    "SELECT * FROM users JOIN orders ON uid = user_id",
    [],
    sql_offload_profile(),
    DbStorageOffloadMode.RamOnly,
    true,
    512
).unwrap()

expect(execution.rows.len()).to_equal(3)
expect(execution.rows[0].values[1].to_text()).to_equal("Alice")
expect(execution.offload.workload).to_equal(DbStorageOffloadWorkload.JoinAggregate)
expect(db_storage_offload_used_gpu(execution.offload)).to_be(true)
expect(execution.offload.dispatch_target).to_equal("gpu_db_join_aggregate_batch")
expect(execution.offload.cpu_authoritative).to_be(true)
expect(execution.offload.gpu_candidate_validated).to_be(false)
expect(execution.offload.validation_reason).to_equal("gpu-candidate-not-evaluated")
expect(execution.offload.profile.data_path).to_equal(GpuWdbCoarseDataPath.GpuResidentBatch)
expect(db_storage_profile_allows_gpu(execution.offload)).to_be(true)
expect(execution.result_source).to_equal("cpu_select")
```

</details>

#### should report grouped aggregate SELECT work through the adapter

- Execute GROUP BY COUNT with CPU-authoritative rows and offload metadata
- var db = sql offload db
- "SELECT category, COUNT
- sql offload profile
   - Expected: execution.rows.len() equals `2`
   - Expected: execution.offload.workload equals `DbStorageOffloadWorkload.JoinAggregate`
   - Expected: execution.offload.dispatch_target equals `gpu_db_join_aggregate_batch`
   - Expected: execution.result_source equals `cpu_select`
   - Expected: execution.rows[0].values[0].to_text() equals `fruit`
   - Expected: execution.rows[0].values[1].to_text() equals `2`
   - Expected: execution.rows[1].values[0].to_text() equals `veggie`
   - Expected: execution.rows[1].values[1].to_text() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Execute GROUP BY COUNT with CPU-authoritative rows and offload metadata")
var db = sql_offload_db()
val execution = db.query_with_offload_profile(
    "SELECT category, COUNT(*) FROM categories GROUP BY category",
    [],
    sql_offload_profile(),
    DbStorageOffloadMode.RamOnly,
    true,
    512
).unwrap()

expect(execution.rows.len()).to_equal(2)
expect(execution.offload.workload).to_equal(DbStorageOffloadWorkload.JoinAggregate)
expect(db_storage_offload_used_gpu(execution.offload)).to_be(true)
expect(execution.offload.dispatch_target).to_equal("gpu_db_join_aggregate_batch")
expect(execution.offload.cpu_authoritative).to_be(true)
expect(execution.result_source).to_equal("cpu_select")
expect(execution.rows[0].values[0].to_text()).to_equal("fruit")
expect(execution.rows[0].values[1].to_text()).to_equal("2")
expect(execution.rows[1].values[0].to_text()).to_equal("veggie")
expect(execution.rows[1].values[1].to_text()).to_equal("1")
```

</details>

#### should execute grouped join aggregate rows through the adapter

- Execute an inner equi-join GROUP BY COUNT with CPU-authoritative rows
- var db = sql offload db
- "SELECT name, COUNT
- sql offload profile
   - Expected: execution.rows.len() equals `2`
   - Expected: execution.rows[0].values[0].to_text() equals `Alice`
   - Expected: execution.rows[0].values[1].to_text() equals `2`
   - Expected: execution.rows[1].values[0].to_text() equals `Bob`
   - Expected: execution.rows[1].values[1].to_text() equals `1`
   - Expected: execution.offload.workload equals `DbStorageOffloadWorkload.JoinAggregate`
   - Expected: execution.offload.dispatch_target equals `gpu_db_join_aggregate_batch`
   - Expected: execution.result_source equals `cpu_select`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Execute an inner equi-join GROUP BY COUNT with CPU-authoritative rows")
var db = sql_offload_db()
val execution = db.query_with_offload_profile(
    "SELECT name, COUNT(*) FROM users JOIN orders ON uid = user_id GROUP BY name",
    [],
    sql_offload_profile(),
    DbStorageOffloadMode.RamOnly,
    true,
    512
).unwrap()

expect(execution.rows.len()).to_equal(2)
expect(execution.rows[0].values[0].to_text()).to_equal("Alice")
expect(execution.rows[0].values[1].to_text()).to_equal("2")
expect(execution.rows[1].values[0].to_text()).to_equal("Bob")
expect(execution.rows[1].values[1].to_text()).to_equal("1")
expect(execution.offload.workload).to_equal(DbStorageOffloadWorkload.JoinAggregate)
expect(db_storage_offload_used_gpu(execution.offload)).to_be(true)
expect(execution.offload.dispatch_target).to_equal("gpu_db_join_aggregate_batch")
expect(execution.offload.cpu_authoritative).to_be(true)
expect(execution.result_source).to_equal("cpu_select")
```

</details>

#### should validate grouped join aggregate GPU candidate rows

- Compare a bounded join aggregate candidate with the CPU SQL oracle
- var db = sql offload db
- "SELECT name, COUNT
- sql offload profile
   - Expected: execution.rows.len() equals `2`
   - Expected: execution.rows[0].values[0].to_text() equals `Alice`
   - Expected: execution.rows[0].values[1].to_text() equals `2`
   - Expected: execution.rows[1].values[0].to_text() equals `Bob`
   - Expected: execution.rows[1].values[1].to_text() equals `1`
   - Expected: execution.offload.validation_reason equals `gpu-cpu-row-match`
   - Expected: execution.offload.profile.data_path equals `GpuWdbCoarseDataPath.GpuResidentBatch`
   - Expected: execution.result_source equals `gpu_candidate_validated`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Compare a bounded join aggregate candidate with the CPU SQL oracle")
var db = sql_offload_db()
val execution = db.query_with_validated_offload_profile(
    "SELECT name, COUNT(*) FROM users JOIN orders ON uid = user_id GROUP BY name",
    [],
    sql_offload_profile(),
    DbStorageOffloadMode.RamOnly,
    true,
    512
).unwrap()

expect(execution.rows.len()).to_equal(2)
expect(execution.rows[0].values[0].to_text()).to_equal("Alice")
expect(execution.rows[0].values[1].to_text()).to_equal("2")
expect(execution.rows[1].values[0].to_text()).to_equal("Bob")
expect(execution.rows[1].values[1].to_text()).to_equal("1")
expect(db_storage_offload_used_gpu(execution.offload)).to_be(true)
expect(execution.offload.gpu_candidate_validated).to_be(true)
expect(execution.offload.validation_reason).to_equal("gpu-cpu-row-match")
expect(execution.offload.profile.data_path).to_equal(GpuWdbCoarseDataPath.GpuResidentBatch)
expect(db_storage_profile_allows_gpu(execution.offload)).to_be(true)
expect(execution.result_source).to_equal("gpu_candidate_validated")
```

</details>

#### should validate filtered projection GPU candidate row ids

- Compare a bounded scan/filter/project candidate with the CPU SQL oracle
- var db = sql offload db
- sql offload profile
   - Expected: execution.rows.len() equals `1`
   - Expected: execution.rows[0].values[0].to_text() equals `Bob`
   - Expected: execution.offload.workload equals `DbStorageOffloadWorkload.ScanFilterProject`
   - Expected: execution.offload.dispatch_target equals `gpu_db_columnar_scan_batch`
   - Expected: execution.offload.validation_reason equals `gpu-cpu-row-match`
   - Expected: execution.offload.row_ids.len() equals `1`
   - Expected: execution.offload.row_ids[0] equals `0`
   - Expected: execution.result_source equals `gpu_candidate_validated`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Compare a bounded scan/filter/project candidate with the CPU SQL oracle")
var db = sql_offload_db()
val execution = db.query_with_validated_offload_profile(
    "SELECT name FROM users WHERE uid > 1",
    [],
    sql_offload_profile(),
    DbStorageOffloadMode.RamOnly,
    true,
    512
).unwrap()

expect(execution.rows.len()).to_equal(1)
expect(execution.rows[0].values[0].to_text()).to_equal("Bob")
expect(execution.offload.workload).to_equal(DbStorageOffloadWorkload.ScanFilterProject)
expect(db_storage_offload_used_gpu(execution.offload)).to_be(true)
expect(execution.offload.dispatch_target).to_equal("gpu_db_columnar_scan_batch")
expect(execution.offload.gpu_candidate_validated).to_be(true)
expect(execution.offload.validation_reason).to_equal("gpu-cpu-row-match")
expect(execution.offload.row_ids.len()).to_equal(1)
expect(execution.offload.row_ids[0]).to_equal(0)
expect(execution.offload.cpu_authoritative).to_be(true)
expect(execution.result_source).to_equal("gpu_candidate_validated")
```

</details>

#### should replace filtered projection rows only after native candidates match

- Require strict native device evidence before Pure SQL scan/filter/project replacement
- var db = sql offload db
- sql offload profile
- gpu wdb device backend
   - Expected: execution.rows.len() equals `1`
   - Expected: execution.rows[0].values[0].to_text() equals `Bob`
   - Expected: execution.offload.execution.validation_reason equals `production-gpu-row-match`
   - Expected: execution.offload.execution.row_ids[0] equals `0`
   - Expected: execution.result_source equals `production_gpu_candidate_validated`


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Require strict native device evidence before Pure SQL scan/filter/project replacement")
var db = sql_offload_db()
val execution = db.query_with_device_backend_validated(
    "SELECT name FROM users WHERE uid > 1",
    [],
    sql_offload_profile(),
    DbStorageOffloadMode.RamOnly,
    true,
    512,
    gpu_wdb_device_backend("cuda", 11, ["gpu_db_columnar_scan_batch"], true, "cuda-device-0"),
    11,
    [0],
    100,
    210,
    69,
    "cuda-event"
).unwrap()

expect(execution.rows.len()).to_equal(1)
expect(execution.rows[0].values[0].to_text()).to_equal("Bob")
expect(db_storage_offload_used_gpu(execution.offload.execution)).to_be(true)
expect(execution.offload.execution.cpu_authoritative).to_be(false)
expect(execution.offload.execution.gpu_candidate_validated).to_be(true)
expect(execution.offload.execution.validation_reason).to_equal("production-gpu-row-match")
expect(execution.offload.execution.row_ids[0]).to_equal(0)
expect(execution.offload.device_execution.device_result.production_device_claim).to_be(true)
expect(execution.result_source).to_equal("production_gpu_candidate_validated")
```

</details>

#### should keep filtered projection CPU authoritative when native candidates mismatch

- Reject Pure SQL scan/filter/project replacement when native row IDs disagree
- var db = sql offload db
- sql offload profile
- gpu wdb device backend
   - Expected: execution.rows.len() equals `1`
   - Expected: execution.offload.execution.validation_reason equals `production-gpu-row-mismatch`
   - Expected: execution.offload.execution.dispatch_target equals `cpu_fallback`
   - Expected: execution.offload.execution.row_ids[0] equals `0`
   - Expected: execution.result_source equals `cpu_select`


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Reject Pure SQL scan/filter/project replacement when native row IDs disagree")
var db = sql_offload_db()
val execution = db.query_with_device_backend_validated(
    "SELECT name FROM users WHERE uid > 1",
    [],
    sql_offload_profile(),
    DbStorageOffloadMode.RamOnly,
    true,
    512,
    gpu_wdb_device_backend("cuda", 11, ["gpu_db_columnar_scan_batch"], true, "cuda-device-0"),
    11,
    [1],
    100,
    210,
    69,
    "cuda-event"
).unwrap()

expect(execution.rows.len()).to_equal(1)
expect(execution.offload.execution.cpu_authoritative).to_be(true)
expect(execution.offload.execution.gpu_candidate_validated).to_be(false)
expect(execution.offload.execution.validation_reason).to_equal("production-gpu-row-mismatch")
expect(execution.offload.execution.dispatch_target).to_equal("cpu_fallback")
expect(execution.offload.execution.row_ids[0]).to_equal(0)
expect(execution.offload.device_execution.device_result.production_device_claim).to_be(true)
expect(execution.result_source).to_equal("cpu_select")
```

</details>

#### should keep perf-only filtered projection device runs from replacing CPU rows

- Require production native timing before Pure SQL rows stop being CPU authoritative
- var db = sql offload db
- sql offload profile
- gpu wdb device backend
   - Expected: execution.rows.len() equals `1`
   - Expected: execution.offload.execution.validation_reason equals `production-device-not-measured`
   - Expected: execution.offload.execution.row_ids[0] equals `0`
   - Expected: execution.result_source equals `cpu_select`


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Require production native timing before Pure SQL rows stop being CPU authoritative")
var db = sql_offload_db()
val execution = db.query_with_device_backend_validated(
    "SELECT name FROM users WHERE uid > 1",
    [],
    sql_offload_profile(),
    DbStorageOffloadMode.RamOnly,
    true,
    512,
    gpu_wdb_device_backend("mock", 11, ["gpu_db_columnar_scan_batch"], false, "mock-device"),
    11,
    [0],
    100,
    210,
    69,
    "mock-clock"
).unwrap()

expect(execution.rows.len()).to_equal(1)
expect(execution.offload.execution.cpu_authoritative).to_be(true)
expect(execution.offload.execution.gpu_candidate_validated).to_be(false)
expect(execution.offload.execution.validation_reason).to_equal("production-device-not-measured")
expect(execution.offload.execution.row_ids[0]).to_equal(0)
expect(execution.offload.device_execution.device_result.production_device_claim).to_be(false)
expect(execution.result_source).to_equal("cpu_select")
```

</details>

#### should replace grouped join aggregate rows only after native candidates match

- Require strict native device evidence before Pure SQL join aggregate replacement
- var db = sql offload db
- "SELECT name, COUNT
- "SELECT name, COUNT
- sql offload profile
- gpu wdb device backend
   - Expected: execution.rows.len() equals `2`
   - Expected: execution.rows[0].values[0].to_text() equals `Alice`
   - Expected: execution.rows[0].values[1].to_text() equals `2`
   - Expected: execution.rows[1].values[0].to_text() equals `Bob`
   - Expected: execution.rows[1].values[1].to_text() equals `1`
   - Expected: execution.offload.execution.validation_reason equals `production-gpu-row-match`
   - Expected: execution.offload.execution.dispatch_target equals `gpu_db_join_aggregate_batch`
   - Expected: execution.result_source equals `production_gpu_candidate_validated`


<details>
<summary>Executable SSpec</summary>

Runnable source: 34 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Require strict native device evidence before Pure SQL join aggregate replacement")
var db = sql_offload_db()
val candidate_rows = db.query(
    "SELECT name, COUNT(*) FROM users JOIN orders ON uid = user_id GROUP BY name",
    []
).unwrap()
val execution = db.query_join_aggregate_with_device_backend_validated(
    "SELECT name, COUNT(*) FROM users JOIN orders ON uid = user_id GROUP BY name",
    [],
    sql_offload_profile(),
    DbStorageOffloadMode.RamOnly,
    true,
    512,
    gpu_wdb_device_backend("cuda", 11, ["gpu_db_join_aggregate_batch"], true, "cuda-device-0"),
    11,
    candidate_rows,
    [0, 1],
    100,
    230,
    81,
    "cuda-event"
).unwrap()

expect(execution.rows.len()).to_equal(2)
expect(execution.rows[0].values[0].to_text()).to_equal("Alice")
expect(execution.rows[0].values[1].to_text()).to_equal("2")
expect(execution.rows[1].values[0].to_text()).to_equal("Bob")
expect(execution.rows[1].values[1].to_text()).to_equal("1")
expect(execution.offload.execution.cpu_authoritative).to_be(false)
expect(execution.offload.execution.gpu_candidate_validated).to_be(true)
expect(execution.offload.execution.validation_reason).to_equal("production-gpu-row-match")
expect(execution.offload.execution.dispatch_target).to_equal("gpu_db_join_aggregate_batch")
expect(execution.offload.device_execution.device_result.production_device_claim).to_be(true)
expect(execution.result_source).to_equal("production_gpu_candidate_validated")
```

</details>

#### should keep grouped join aggregate rows CPU authoritative when native rows mismatch

- Reject Pure SQL join aggregate replacement when native SQL rows disagree
- var db = sql offload db
- "SELECT category, COUNT
- "SELECT name, COUNT
- sql offload profile
- gpu wdb device backend
   - Expected: execution.rows.len() equals `2`
   - Expected: execution.rows[0].values[0].to_text() equals `Alice`
   - Expected: execution.rows[0].values[1].to_text() equals `2`
   - Expected: execution.rows[1].values[0].to_text() equals `Bob`
   - Expected: execution.rows[1].values[1].to_text() equals `1`
   - Expected: execution.offload.execution.validation_reason equals `production-gpu-sql-row-mismatch`
   - Expected: execution.offload.execution.dispatch_target equals `cpu_fallback`
   - Expected: execution.result_source equals `cpu_select`


<details>
<summary>Executable SSpec</summary>

Runnable source: 34 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Reject Pure SQL join aggregate replacement when native SQL rows disagree")
var db = sql_offload_db()
val candidate_rows = db.query(
    "SELECT category, COUNT(*) FROM categories GROUP BY category",
    []
).unwrap()
val execution = db.query_join_aggregate_with_device_backend_validated(
    "SELECT name, COUNT(*) FROM users JOIN orders ON uid = user_id GROUP BY name",
    [],
    sql_offload_profile(),
    DbStorageOffloadMode.RamOnly,
    true,
    512,
    gpu_wdb_device_backend("cuda", 11, ["gpu_db_join_aggregate_batch"], true, "cuda-device-0"),
    11,
    candidate_rows,
    [0, 1],
    100,
    230,
    81,
    "cuda-event"
).unwrap()

expect(execution.rows.len()).to_equal(2)
expect(execution.rows[0].values[0].to_text()).to_equal("Alice")
expect(execution.rows[0].values[1].to_text()).to_equal("2")
expect(execution.rows[1].values[0].to_text()).to_equal("Bob")
expect(execution.rows[1].values[1].to_text()).to_equal("1")
expect(execution.offload.execution.cpu_authoritative).to_be(true)
expect(execution.offload.execution.gpu_candidate_validated).to_be(false)
expect(execution.offload.execution.validation_reason).to_equal("production-gpu-sql-row-mismatch")
expect(execution.offload.execution.dispatch_target).to_equal("cpu_fallback")
expect(execution.offload.device_execution.device_result.production_device_claim).to_be(true)
expect(execution.result_source).to_equal("cpu_select")
```

</details>

#### should keep validated filtered projection on CPU when GPU is unavailable

- Do not claim validation when scan/filter/project cannot dispatch to GPU
- var db = sql offload db
- db offload profile budget
   - Expected: execution.rows.len() equals `1`
   - Expected: execution.rows[0].values[0].to_text() equals `Bob`
   - Expected: execution.offload.workload equals `DbStorageOffloadWorkload.ScanFilterProject`
   - Expected: execution.offload.dispatch_target equals `cpu_fallback`
   - Expected: execution.offload.validation_reason equals `gpu-not-dispatched`
   - Expected: execution.result_source equals `cpu_select`


<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Do not claim validation when scan/filter/project cannot dispatch to GPU")
var db = sql_offload_db()
val profile = db_offload_profile(
    "pure-sql-no-scan-gpu",
    "cuda",
    1,
    4,
    ["gpu_db_columnar_scan_batch"],
    db_offload_profile_budget(8, 1024 * 1024, 1),
    false,
    true
)
val execution = db.query_with_validated_offload_profile(
    "SELECT name FROM users WHERE uid > 1",
    [],
    profile,
    DbStorageOffloadMode.RamOnly,
    true,
    512
).unwrap()

expect(execution.rows.len()).to_equal(1)
expect(execution.rows[0].values[0].to_text()).to_equal("Bob")
expect(execution.offload.workload).to_equal(DbStorageOffloadWorkload.ScanFilterProject)
expect(db_storage_offload_used_gpu(execution.offload)).to_be(false)
expect(execution.offload.dispatch_target).to_equal("cpu_fallback")
expect(execution.offload.gpu_candidate_validated).to_be(false)
expect(execution.offload.validation_reason).to_equal("gpu-not-dispatched")
expect(execution.result_source).to_equal("cpu_select")
```

</details>

#### should preserve no-hardware fallback for join aggregate SELECTs

- Keep join work CPU-authoritative when GPU hardware is unavailable
- var db = sql offload db
- db offload profile budget
   - Expected: execution.rows.len() equals `3`
   - Expected: execution.offload.dispatch_target equals `cpu_fallback`
   - Expected: execution.offload.reason equals `gpu-unavailable`
   - Expected: execution.offload.validation_reason equals `gpu-candidate-not-evaluated`
   - Expected: execution.offload.profile.data_path equals `GpuWdbCoarseDataPath.GpuResidentBatch`
   - Expected: execution.result_source equals `cpu_select`


<details>
<summary>Executable SSpec</summary>

Runnable source: 30 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Keep join work CPU-authoritative when GPU hardware is unavailable")
var db = sql_offload_db()
val profile = db_offload_profile(
    "pure-sql-no-gpu",
    "cuda",
    1,
    4,
    ["gpu_db_join_aggregate_batch"],
    db_offload_profile_budget(8, 1024 * 1024, 1),
    false,
    true
)
val execution = db.query_with_offload_profile(
    "SELECT * FROM users JOIN orders ON uid = user_id",
    [],
    profile,
    DbStorageOffloadMode.RamOnly,
    true,
    512
).unwrap()

expect(execution.rows.len()).to_equal(3)
expect(db_storage_offload_used_gpu(execution.offload)).to_be(false)
expect(execution.offload.dispatch_target).to_equal("cpu_fallback")
expect(execution.offload.reason).to_equal("gpu-unavailable")
expect(execution.offload.cpu_authoritative).to_be(true)
expect(execution.offload.gpu_candidate_validated).to_be(false)
expect(execution.offload.validation_reason).to_equal("gpu-candidate-not-evaluated")
expect(execution.offload.profile.data_path).to_equal(GpuWdbCoarseDataPath.GpuResidentBatch)
expect(execution.result_source).to_equal("cpu_select")
```

</details>

#### should report SUM aggregate SELECT work through the adapter

- Execute GROUP BY SUM with CPU-authoritative rows and offload metadata
- var db = sql offload db
- "SELECT category, SUM
- sql offload profile
   - Expected: execution.rows.len() equals `2`
   - Expected: execution.rows[0].values[0].to_text() equals `fruit`
   - Expected: execution.rows[0].values[1].to_text() equals `12`
   - Expected: execution.rows[1].values[0].to_text() equals `veggie`
   - Expected: execution.rows[1].values[1].to_text() equals `3`
   - Expected: execution.offload.workload equals `DbStorageOffloadWorkload.JoinAggregate`
   - Expected: execution.result_source equals `cpu_select`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Execute GROUP BY SUM with CPU-authoritative rows and offload metadata")
var db = sql_offload_db()
val execution = db.query_with_offload_profile(
    "SELECT category, SUM(amount) FROM sales GROUP BY category",
    [],
    sql_offload_profile(),
    DbStorageOffloadMode.RamOnly,
    true,
    512
).unwrap()

expect(execution.rows.len()).to_equal(2)
expect(execution.rows[0].values[0].to_text()).to_equal("fruit")
expect(execution.rows[0].values[1].to_text()).to_equal("12")
expect(execution.rows[1].values[0].to_text()).to_equal("veggie")
expect(execution.rows[1].values[1].to_text()).to_equal("3")
expect(execution.offload.workload).to_equal(DbStorageOffloadWorkload.JoinAggregate)
expect(db_storage_offload_used_gpu(execution.offload)).to_be(true)
expect(execution.offload.cpu_authoritative).to_be(true)
expect(execution.result_source).to_equal("cpu_select")
```

</details>

#### should validate SUM aggregate SELECT candidate rows

- Compare grouped SUM aggregate candidates with the CPU SQL oracle
- var db = sql offload db
- "SELECT category, SUM
- sql offload profile
   - Expected: execution.rows.len() equals `2`
   - Expected: execution.rows[0].values[0].to_text() equals `fruit`
   - Expected: execution.rows[0].values[1].to_text() equals `12`
   - Expected: execution.rows[1].values[0].to_text() equals `veggie`
   - Expected: execution.rows[1].values[1].to_text() equals `3`
   - Expected: execution.offload.workload equals `DbStorageOffloadWorkload.JoinAggregate`
   - Expected: execution.offload.validation_reason equals `gpu-cpu-row-match`
   - Expected: execution.result_source equals `gpu_candidate_validated`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Compare grouped SUM aggregate candidates with the CPU SQL oracle")
var db = sql_offload_db()
val execution = db.query_with_validated_offload_profile(
    "SELECT category, SUM(amount) FROM sales GROUP BY category",
    [],
    sql_offload_profile(),
    DbStorageOffloadMode.RamOnly,
    true,
    512
).unwrap()

expect(execution.rows.len()).to_equal(2)
expect(execution.rows[0].values[0].to_text()).to_equal("fruit")
expect(execution.rows[0].values[1].to_text()).to_equal("12")
expect(execution.rows[1].values[0].to_text()).to_equal("veggie")
expect(execution.rows[1].values[1].to_text()).to_equal("3")
expect(execution.offload.workload).to_equal(DbStorageOffloadWorkload.JoinAggregate)
expect(db_storage_offload_used_gpu(execution.offload)).to_be(true)
expect(execution.offload.gpu_candidate_validated).to_be(true)
expect(execution.offload.validation_reason).to_equal("gpu-cpu-row-match")
expect(execution.result_source).to_equal("gpu_candidate_validated")
```

</details>

#### should validate AVG aggregate SELECT candidate rows

- Compare grouped AVG aggregate candidates with the CPU SQL oracle
- var db = sql offload db
- "SELECT category, AVG
- sql offload profile
   - Expected: execution.rows.len() equals `2`
   - Expected: execution.rows[0].values[0].to_text() equals `fruit`
   - Expected: execution.rows[0].values[1].to_text() equals `6`
   - Expected: execution.rows[1].values[0].to_text() equals `veggie`
   - Expected: execution.rows[1].values[1].to_text() equals `3`
   - Expected: execution.offload.workload equals `DbStorageOffloadWorkload.JoinAggregate`
   - Expected: execution.offload.validation_reason equals `gpu-cpu-row-match`
   - Expected: execution.result_source equals `gpu_candidate_validated`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Compare grouped AVG aggregate candidates with the CPU SQL oracle")
var db = sql_offload_db()
val execution = db.query_with_validated_offload_profile(
    "SELECT category, AVG(amount) FROM sales GROUP BY category",
    [],
    sql_offload_profile(),
    DbStorageOffloadMode.RamOnly,
    true,
    512
).unwrap()

expect(execution.rows.len()).to_equal(2)
expect(execution.rows[0].values[0].to_text()).to_equal("fruit")
expect(execution.rows[0].values[1].to_text()).to_equal("6")
expect(execution.rows[1].values[0].to_text()).to_equal("veggie")
expect(execution.rows[1].values[1].to_text()).to_equal("3")
expect(execution.offload.workload).to_equal(DbStorageOffloadWorkload.JoinAggregate)
expect(db_storage_offload_used_gpu(execution.offload)).to_be(true)
expect(execution.offload.gpu_candidate_validated).to_be(true)
expect(execution.offload.validation_reason).to_equal("gpu-cpu-row-match")
expect(execution.result_source).to_equal("gpu_candidate_validated")
```

</details>

#### should validate MIN and MAX aggregate SELECT candidate rows

- Compare grouped MIN and MAX aggregate candidates with the CPU SQL oracle
- var db = sql offload db
- "SELECT category, MIN
- sql offload profile
- "SELECT category, MAX
- sql offload profile
   - Expected: min_execution.rows.len() equals `2`
   - Expected: min_execution.rows[0].values[0].to_text() equals `fruit`
   - Expected: min_execution.rows[0].values[1].to_text() equals `5`
   - Expected: min_execution.rows[1].values[0].to_text() equals `veggie`
   - Expected: min_execution.rows[1].values[1].to_text() equals `3`
   - Expected: min_execution.offload.workload equals `DbStorageOffloadWorkload.JoinAggregate`
   - Expected: min_execution.offload.validation_reason equals `gpu-cpu-row-match`
   - Expected: min_execution.result_source equals `gpu_candidate_validated`
   - Expected: max_execution.rows[0].values[0].to_text() equals `fruit`
   - Expected: max_execution.rows[0].values[1].to_text() equals `7`
   - Expected: max_execution.rows[1].values[0].to_text() equals `veggie`
   - Expected: max_execution.rows[1].values[1].to_text() equals `3`
   - Expected: max_execution.offload.validation_reason equals `gpu-cpu-row-match`
   - Expected: max_execution.result_source equals `gpu_candidate_validated`


<details>
<summary>Executable SSpec</summary>

Runnable source: 36 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Compare grouped MIN and MAX aggregate candidates with the CPU SQL oracle")
var db = sql_offload_db()
val min_execution = db.query_with_validated_offload_profile(
    "SELECT category, MIN(amount) FROM sales GROUP BY category",
    [],
    sql_offload_profile(),
    DbStorageOffloadMode.RamOnly,
    true,
    512
).unwrap()
val max_execution = db.query_with_validated_offload_profile(
    "SELECT category, MAX(amount) FROM sales GROUP BY category",
    [],
    sql_offload_profile(),
    DbStorageOffloadMode.RamOnly,
    true,
    512
).unwrap()

expect(min_execution.rows.len()).to_equal(2)
expect(min_execution.rows[0].values[0].to_text()).to_equal("fruit")
expect(min_execution.rows[0].values[1].to_text()).to_equal("5")
expect(min_execution.rows[1].values[0].to_text()).to_equal("veggie")
expect(min_execution.rows[1].values[1].to_text()).to_equal("3")
expect(min_execution.offload.workload).to_equal(DbStorageOffloadWorkload.JoinAggregate)
expect(db_storage_offload_used_gpu(min_execution.offload)).to_be(true)
expect(min_execution.offload.gpu_candidate_validated).to_be(true)
expect(min_execution.offload.validation_reason).to_equal("gpu-cpu-row-match")
expect(min_execution.result_source).to_equal("gpu_candidate_validated")
expect(max_execution.rows[0].values[0].to_text()).to_equal("fruit")
expect(max_execution.rows[0].values[1].to_text()).to_equal("7")
expect(max_execution.rows[1].values[0].to_text()).to_equal("veggie")
expect(max_execution.rows[1].values[1].to_text()).to_equal("3")
expect(max_execution.offload.gpu_candidate_validated).to_be(true)
expect(max_execution.offload.validation_reason).to_equal("gpu-cpu-row-match")
expect(max_execution.result_source).to_equal("gpu_candidate_validated")
```

</details>

#### should replace grouped SUM aggregate rows only after native candidates match

- Require strict native device evidence before Pure SQL SUM aggregate replacement
- var db = sql offload db
- "SELECT category, SUM
- "SELECT category, SUM
- sql offload profile
- gpu wdb device backend
   - Expected: execution.rows.len() equals `2`
   - Expected: execution.rows[0].values[0].to_text() equals `fruit`
   - Expected: execution.rows[0].values[1].to_text() equals `12`
   - Expected: execution.rows[1].values[0].to_text() equals `veggie`
   - Expected: execution.rows[1].values[1].to_text() equals `3`
   - Expected: execution.offload.execution.validation_reason equals `production-gpu-row-match`
   - Expected: execution.offload.execution.dispatch_target equals `gpu_db_join_aggregate_batch`
   - Expected: execution.result_source equals `production_gpu_candidate_validated`


<details>
<summary>Executable SSpec</summary>

Runnable source: 34 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Require strict native device evidence before Pure SQL SUM aggregate replacement")
var db = sql_offload_db()
val candidate_rows = db.query(
    "SELECT category, SUM(amount) FROM sales GROUP BY category",
    []
).unwrap()
val execution = db.query_join_aggregate_with_device_backend_validated(
    "SELECT category, SUM(amount) FROM sales GROUP BY category",
    [],
    sql_offload_profile(),
    DbStorageOffloadMode.RamOnly,
    true,
    512,
    gpu_wdb_device_backend("cuda", 11, ["gpu_db_join_aggregate_batch"], true, "cuda-device-0"),
    11,
    candidate_rows,
    [0, 1],
    100,
    230,
    81,
    "cuda-event"
).unwrap()

expect(execution.rows.len()).to_equal(2)
expect(execution.rows[0].values[0].to_text()).to_equal("fruit")
expect(execution.rows[0].values[1].to_text()).to_equal("12")
expect(execution.rows[1].values[0].to_text()).to_equal("veggie")
expect(execution.rows[1].values[1].to_text()).to_equal("3")
expect(execution.offload.execution.cpu_authoritative).to_be(false)
expect(execution.offload.execution.gpu_candidate_validated).to_be(true)
expect(execution.offload.execution.validation_reason).to_equal("production-gpu-row-match")
expect(execution.offload.execution.dispatch_target).to_equal("gpu_db_join_aggregate_batch")
expect(execution.offload.device_execution.device_result.production_device_claim).to_be(true)
expect(execution.result_source).to_equal("production_gpu_candidate_validated")
```

</details>

#### should replace grouped AVG aggregate rows only after native candidates match

- Require strict native device evidence before Pure SQL AVG aggregate replacement
- var db = sql offload db
- "SELECT category, AVG
- "SELECT category, AVG
- sql offload profile
- gpu wdb device backend
   - Expected: execution.rows.len() equals `2`
   - Expected: execution.rows[0].values[0].to_text() equals `fruit`
   - Expected: execution.rows[0].values[1].to_text() equals `6`
   - Expected: execution.rows[1].values[0].to_text() equals `veggie`
   - Expected: execution.rows[1].values[1].to_text() equals `3`
   - Expected: execution.offload.execution.validation_reason equals `production-gpu-row-match`
   - Expected: execution.offload.execution.dispatch_target equals `gpu_db_join_aggregate_batch`
   - Expected: execution.result_source equals `production_gpu_candidate_validated`


<details>
<summary>Executable SSpec</summary>

Runnable source: 34 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Require strict native device evidence before Pure SQL AVG aggregate replacement")
var db = sql_offload_db()
val candidate_rows = db.query(
    "SELECT category, AVG(amount) FROM sales GROUP BY category",
    []
).unwrap()
val execution = db.query_join_aggregate_with_device_backend_validated(
    "SELECT category, AVG(amount) FROM sales GROUP BY category",
    [],
    sql_offload_profile(),
    DbStorageOffloadMode.RamOnly,
    true,
    512,
    gpu_wdb_device_backend("cuda", 11, ["gpu_db_join_aggregate_batch"], true, "cuda-device-0"),
    11,
    candidate_rows,
    [0, 1],
    100,
    230,
    81,
    "cuda-event"
).unwrap()

expect(execution.rows.len()).to_equal(2)
expect(execution.rows[0].values[0].to_text()).to_equal("fruit")
expect(execution.rows[0].values[1].to_text()).to_equal("6")
expect(execution.rows[1].values[0].to_text()).to_equal("veggie")
expect(execution.rows[1].values[1].to_text()).to_equal("3")
expect(execution.offload.execution.cpu_authoritative).to_be(false)
expect(execution.offload.execution.gpu_candidate_validated).to_be(true)
expect(execution.offload.execution.validation_reason).to_equal("production-gpu-row-match")
expect(execution.offload.execution.dispatch_target).to_equal("gpu_db_join_aggregate_batch")
expect(execution.offload.device_execution.device_result.production_device_claim).to_be(true)
expect(execution.result_source).to_equal("production_gpu_candidate_validated")
```

</details>

#### should replace grouped MIN aggregate rows only after native candidates match

- Require strict native device evidence before Pure SQL MIN aggregate replacement
- var db = sql offload db
- "SELECT category, MIN
- "SELECT category, MIN
- sql offload profile
- gpu wdb device backend
   - Expected: execution.rows.len() equals `2`
   - Expected: execution.rows[0].values[0].to_text() equals `fruit`
   - Expected: execution.rows[0].values[1].to_text() equals `5`
   - Expected: execution.rows[1].values[0].to_text() equals `veggie`
   - Expected: execution.rows[1].values[1].to_text() equals `3`
   - Expected: execution.offload.execution.validation_reason equals `production-gpu-row-match`
   - Expected: execution.result_source equals `production_gpu_candidate_validated`


<details>
<summary>Executable SSpec</summary>

Runnable source: 33 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Require strict native device evidence before Pure SQL MIN aggregate replacement")
var db = sql_offload_db()
val candidate_rows = db.query(
    "SELECT category, MIN(amount) FROM sales GROUP BY category",
    []
).unwrap()
val execution = db.query_join_aggregate_with_device_backend_validated(
    "SELECT category, MIN(amount) FROM sales GROUP BY category",
    [],
    sql_offload_profile(),
    DbStorageOffloadMode.RamOnly,
    true,
    512,
    gpu_wdb_device_backend("cuda", 11, ["gpu_db_join_aggregate_batch"], true, "cuda-device-0"),
    11,
    candidate_rows,
    [0, 1],
    100,
    230,
    81,
    "cuda-event"
).unwrap()

expect(execution.rows.len()).to_equal(2)
expect(execution.rows[0].values[0].to_text()).to_equal("fruit")
expect(execution.rows[0].values[1].to_text()).to_equal("5")
expect(execution.rows[1].values[0].to_text()).to_equal("veggie")
expect(execution.rows[1].values[1].to_text()).to_equal("3")
expect(execution.offload.execution.cpu_authoritative).to_be(false)
expect(execution.offload.execution.gpu_candidate_validated).to_be(true)
expect(execution.offload.execution.validation_reason).to_equal("production-gpu-row-match")
expect(execution.offload.device_execution.device_result.production_device_claim).to_be(true)
expect(execution.result_source).to_equal("production_gpu_candidate_validated")
```

</details>

#### should replace grouped MAX aggregate rows only after native candidates match

- Require strict native device evidence before Pure SQL MAX aggregate replacement
- var db = sql offload db
- "SELECT category, MAX
- "SELECT category, MAX
- sql offload profile
- gpu wdb device backend
   - Expected: execution.rows.len() equals `2`
   - Expected: execution.rows[0].values[0].to_text() equals `fruit`
   - Expected: execution.rows[0].values[1].to_text() equals `7`
   - Expected: execution.rows[1].values[0].to_text() equals `veggie`
   - Expected: execution.rows[1].values[1].to_text() equals `3`
   - Expected: execution.offload.execution.validation_reason equals `production-gpu-row-match`
   - Expected: execution.result_source equals `production_gpu_candidate_validated`


<details>
<summary>Executable SSpec</summary>

Runnable source: 33 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Require strict native device evidence before Pure SQL MAX aggregate replacement")
var db = sql_offload_db()
val candidate_rows = db.query(
    "SELECT category, MAX(amount) FROM sales GROUP BY category",
    []
).unwrap()
val execution = db.query_join_aggregate_with_device_backend_validated(
    "SELECT category, MAX(amount) FROM sales GROUP BY category",
    [],
    sql_offload_profile(),
    DbStorageOffloadMode.RamOnly,
    true,
    512,
    gpu_wdb_device_backend("cuda", 11, ["gpu_db_join_aggregate_batch"], true, "cuda-device-0"),
    11,
    candidate_rows,
    [0, 1],
    100,
    230,
    81,
    "cuda-event"
).unwrap()

expect(execution.rows.len()).to_equal(2)
expect(execution.rows[0].values[0].to_text()).to_equal("fruit")
expect(execution.rows[0].values[1].to_text()).to_equal("7")
expect(execution.rows[1].values[0].to_text()).to_equal("veggie")
expect(execution.rows[1].values[1].to_text()).to_equal("3")
expect(execution.offload.execution.cpu_authoritative).to_be(false)
expect(execution.offload.execution.gpu_candidate_validated).to_be(true)
expect(execution.offload.execution.validation_reason).to_equal("production-gpu-row-match")
expect(execution.offload.device_execution.device_result.production_device_claim).to_be(true)
expect(execution.result_source).to_equal("production_gpu_candidate_validated")
```

</details>

#### should keep grouped SUM aggregate rows CPU authoritative when native rows mismatch

- Reject Pure SQL SUM aggregate replacement when native SQL rows disagree
- var db = sql offload db
- "SELECT name, COUNT
- "SELECT category, SUM
- sql offload profile
- gpu wdb device backend
   - Expected: execution.rows.len() equals `2`
   - Expected: execution.rows[0].values[0].to_text() equals `fruit`
   - Expected: execution.rows[0].values[1].to_text() equals `12`
   - Expected: execution.rows[1].values[0].to_text() equals `veggie`
   - Expected: execution.rows[1].values[1].to_text() equals `3`
   - Expected: execution.offload.execution.validation_reason equals `production-gpu-sql-row-mismatch`
   - Expected: execution.offload.execution.dispatch_target equals `cpu_fallback`
   - Expected: execution.result_source equals `cpu_select`


<details>
<summary>Executable SSpec</summary>

Runnable source: 34 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Reject Pure SQL SUM aggregate replacement when native SQL rows disagree")
var db = sql_offload_db()
val candidate_rows = db.query(
    "SELECT name, COUNT(*) FROM users JOIN orders ON uid = user_id GROUP BY name",
    []
).unwrap()
val execution = db.query_join_aggregate_with_device_backend_validated(
    "SELECT category, SUM(amount) FROM sales GROUP BY category",
    [],
    sql_offload_profile(),
    DbStorageOffloadMode.RamOnly,
    true,
    512,
    gpu_wdb_device_backend("cuda", 11, ["gpu_db_join_aggregate_batch"], true, "cuda-device-0"),
    11,
    candidate_rows,
    [0, 1],
    100,
    230,
    81,
    "cuda-event"
).unwrap()

expect(execution.rows.len()).to_equal(2)
expect(execution.rows[0].values[0].to_text()).to_equal("fruit")
expect(execution.rows[0].values[1].to_text()).to_equal("12")
expect(execution.rows[1].values[0].to_text()).to_equal("veggie")
expect(execution.rows[1].values[1].to_text()).to_equal("3")
expect(execution.offload.execution.cpu_authoritative).to_be(true)
expect(execution.offload.execution.gpu_candidate_validated).to_be(false)
expect(execution.offload.execution.validation_reason).to_equal("production-gpu-sql-row-mismatch")
expect(execution.offload.execution.dispatch_target).to_equal("cpu_fallback")
expect(execution.offload.device_execution.device_result.production_device_claim).to_be(true)
expect(execution.result_source).to_equal("cpu_select")
```

</details>

#### should report HAVING ORDER LIMIT aggregate SELECT work through the adapter

- Execute aggregate HAVING with order and limit while preserving CPU rows
- var db = sql offload db
- "SELECT category, SUM
- sql offload profile
   - Expected: execution.rows.len() equals `1`
   - Expected: execution.rows[0].values[0].to_text() equals `fruit`
   - Expected: execution.rows[0].values[1].to_text() equals `12`
   - Expected: execution.offload.workload equals `DbStorageOffloadWorkload.JoinAggregate`
   - Expected: execution.offload.dispatch_target equals `gpu_db_join_aggregate_batch`
   - Expected: execution.result_source equals `cpu_select`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Execute aggregate HAVING with order and limit while preserving CPU rows")
var db = sql_offload_db()
val execution = db.query_with_offload_profile(
    "SELECT category, SUM(amount) FROM sales GROUP BY category HAVING SUM(amount) > 3 ORDER BY category DESC LIMIT 1",
    [],
    sql_offload_profile(),
    DbStorageOffloadMode.RamOnly,
    true,
    512
).unwrap()

expect(execution.rows.len()).to_equal(1)
expect(execution.rows[0].values[0].to_text()).to_equal("fruit")
expect(execution.rows[0].values[1].to_text()).to_equal("12")
expect(execution.offload.workload).to_equal(DbStorageOffloadWorkload.JoinAggregate)
expect(db_storage_offload_used_gpu(execution.offload)).to_be(true)
expect(execution.offload.dispatch_target).to_equal("gpu_db_join_aggregate_batch")
expect(execution.offload.cpu_authoritative).to_be(true)
expect(execution.result_source).to_equal("cpu_select")
```

</details>

#### should preserve stale WAL fallback for SSD SQL aggregate observation

- Keep SSD aggregate observation on CPU when WAL generation is stale
- var db = sql offload db
- "SELECT COUNT
- sql offload profile
   - Expected: execution.rows.len() equals `1`
   - Expected: execution.rows[0].values[0].to_text() equals `3`
   - Expected: execution.offload.workload equals `DbStorageOffloadWorkload.JoinAggregate`
   - Expected: execution.offload.reason equals `stale-generation`
   - Expected: execution.offload.profile.data_path equals `GpuWdbCoarseDataPath.SsdStagedBatch`
   - Expected: execution.result_source equals `cpu_select`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Keep SSD aggregate observation on CPU when WAL generation is stale")
var db = sql_offload_db()
val execution = db.query_with_offload_profile(
    "SELECT COUNT(*) FROM categories",
    [],
    sql_offload_profile(),
    DbStorageOffloadMode.SsdAccelerated,
    false,
    512
).unwrap()

expect(execution.rows.len()).to_equal(1)
expect(execution.rows[0].values[0].to_text()).to_equal("3")
expect(execution.offload.workload).to_equal(DbStorageOffloadWorkload.JoinAggregate)
expect(db_storage_offload_used_gpu(execution.offload)).to_be(false)
expect(execution.offload.reason).to_equal("stale-generation")
expect(execution.offload.cpu_authoritative).to_be(true)
expect(execution.offload.profile.data_path).to_equal(GpuWdbCoarseDataPath.SsdStagedBatch)
expect(db_storage_profile_allows_gpu(execution.offload)).to_be(false)
expect(execution.result_source).to_equal("cpu_select")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 24 |
| Active scenarios | 24 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** [doc/02_requirements/feature/gpu_web_db_offload.md](doc/02_requirements/feature/gpu_web_db_offload.md)
- **Plan:** [doc/03_plan/agent_tasks/gpu_web_db_offload_impl_status.md](doc/03_plan/agent_tasks/gpu_web_db_offload_impl_status.md)
- **Design:** [doc/05_design/gpu_web_db_offload.md](doc/05_design/gpu_web_db_offload.md)


</details>
