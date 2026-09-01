# dbd DBFS adapter — mounted driver evidence without false durability

> Proves that the daemon can identify and bounded-read a real DbFsDriver while

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# dbd DBFS adapter — mounted driver evidence without false durability

Proves that the daemon can identify and bounded-read a real DbFsDriver while

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/apps/dbd/dbd_dbfs_adapter_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Proves that the daemon can identify and bounded-read a real DbFsDriver while
rejecting every commit before mutation because DBFS has no fsync owner yet.

## Scenarios

### dbd DBFS adapter durable admission

#### recognizes a real DBFS driver but keeps readiness blocked on fsync

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- recognizes a real DBFS driver but keeps readiness blocked on fsync
   - Expected: adapter.state equals `DbdDbfsAdapterState.MountedSyncUnsupported`
   - Expected: adapter.blocker() equals `dbfs-not-device-backed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("recognizes a real DBFS driver but keeps readiness blocked on fsync")
val adapter = _mounted_adapter()
expect(adapter.state).to_equal(DbdDbfsAdapterState.MountedSyncUnsupported)
expect(adapter.ready()).to_be(false)
expect(adapter.blocker()).to_equal("dbfs-not-device-backed")
assert_true(adapter.driver_instance_id > 0)
```

</details>

#### rejects commit before creating or mutating the journal

- rejects commit before creating or mutating the journal
   - Expected: committed.unwrap_err() equals `dbfs-not-device-backed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects commit before creating or mutating the journal")
val driver = DbFsDriver.new_hosted()
var adapter = dbd_dbfs_adapter_from_driver(DriverInstance.DbFs(driver))
val committed = adapter.commit_and_sync("/DBD.LOG", [1u8, 2u8, 3u8])
expect(committed.is_err()).to_be(true)
expect(committed.unwrap_err()).to_equal("dbfs-not-device-backed")
expect(driver.stat_path(Path(raw: "/DBD.LOG")).is_err()).to_be(true)
```

</details>

#### rejects a mounted driver that is not DBFS

- rejects a mounted driver that is not DBFS
   - Expected: adapter.state equals `DbdDbfsAdapterState.Detached`
   - Expected: adapter.blocker() equals `mounted-root-is-not-dbfs`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a mounted driver that is not DBFS")
val adapter = dbd_dbfs_adapter_from_driver(
    DriverInstance.RamFs(RamFsDriver.new()))
expect(adapter.state).to_equal(DbdDbfsAdapterState.Detached)
expect(adapter.ready()).to_be(false)
expect(adapter.blocker()).to_equal("mounted-root-is-not-dbfs")
```

</details>

### dbd DBFS adapter bounded recovery read

#### reads exact existing journal bytes through the typed driver

- reads exact existing journal bytes through the typed driver
   - Expected: read.unwrap() equals `[7u8, 8u8, 9u8]`
   - Expected: adapter.open_handles equals `0i64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reads exact existing journal bytes through the typed driver")
val driver = DbFsDriver.new_hosted()
val opened = driver.open_path(
    Path(raw: "/DBD.LOG"), OpenFlags.read_write().with_create())
expect(opened.is_ok()).to_be(true)
val handle = opened.unwrap()
expect(driver.write_bytes_handle(handle, [7u8, 8u8, 9u8]).is_ok()).to_be(true)
expect(driver.close_handle(handle).is_ok()).to_be(true)
var adapter = dbd_dbfs_adapter_from_driver(DriverInstance.DbFs(driver))
val read = adapter.read_existing_bounded("/DBD.LOG", 64)
expect(read.is_ok()).to_be(true)
expect(read.unwrap()).to_equal([7u8, 8u8, 9u8])
expect(adapter.open_handles).to_equal(0i64)
```

</details>

#### rejects missing files and invalid or oversized read bounds

- rejects missing files and invalid or oversized read bounds


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects missing files and invalid or oversized read bounds")
var adapter = _mounted_adapter()
expect(adapter.read_existing_bounded("/DBD.LOG", 64).is_err()).to_be(true)
expect(adapter.read_existing_bounded("/other", 64).is_err()).to_be(true)
expect(adapter.read_existing_bounded(
    "/DBD.LOG", DBD_DBFS_MAX_RECOVERY_BYTES + 1
).is_err()).to_be(true)
```

</details>

### dbd DBFS adapter quarantine and restart

#### restart releases the driver but preserves quarantine evidence

- restart releases the driver but preserves quarantine evidence
   - Expected: adapter.state equals `DbdDbfsAdapterState.Quarantined`
   - Expected: adapter.state equals `DbdDbfsAdapterState.Quarantined`
   - Expected: adapter.blocker() equals `dbfs-recovery-corrupt-journal`
   - Expected: adapter.generation equals `previous_generation + 1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("restart releases the driver but preserves quarantine evidence")
var adapter = _mounted_adapter()
expect(adapter.quarantine("dbfs-recovery-corrupt-journal")).to_be(true)
expect(adapter.state).to_equal(DbdDbfsAdapterState.Quarantined)
expect(adapter.read_existing_bounded("/DBD.LOG", 64).is_err()).to_be(true)
expect(adapter.commit_and_sync("/DBD.LOG", [1u8]).is_err()).to_be(true)
val previous_generation = adapter.generation
expect(adapter.reset_for_restart()).to_be(true)
expect(adapter.state).to_equal(DbdDbfsAdapterState.Quarantined)
expect(adapter.blocker()).to_equal("dbfs-recovery-corrupt-journal")
expect(adapter.driver.is_none()).to_be(true)
expect(adapter.generation).to_equal(previous_generation + 1)
expect(adapter.ready()).to_be(false)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `a5d8b0b298f5d93ecbac7f44a66b1bed9ae283700789f9d4fe2ecfb8beb0161d`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a5d8b0b298f5d93ecbac7f44a66b1bed9ae283700789f9d4fe2ecfb8beb0161d`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a5d8b0b298f5d93ecbac7f44a66b1bed9ae283700789f9d4fe2ecfb8beb0161d`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/os/apps/dbd/dbd_dbfs_adapter_spec.spl
mirror: doc/06_spec/01_unit/os/apps/dbd/dbd_dbfs_adapter_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/apps/dbd/dbd_dbfs_adapter_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/apps/dbd/dbd_dbfs_adapter_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/apps/dbd/dbd_dbfs_adapter_spec.spl:31:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'recognizes a real DBFS driver but keeps readiness blocked on fsync' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/apps/dbd/dbd_dbfs_adapter_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects commit before creating or mutating the journal' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/apps/dbd/dbd_dbfs_adapter_spec.spl:50:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects a mounted driver that is not DBFS' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
