# dbfs_durable_commit_spec

> DBFS durable commit and recovery specification.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# dbfs_durable_commit_spec

DBFS durable commit and recovery specification.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/02_integration/storage/dbfs/dbfs_durable_commit_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

DBFS durable commit and recovery specification.

The backing probe separates volatile controller state from durable media.  A
power cut discards volatile bytes, so reconstruction never relies on the
driver's in-memory inode table.

## Scenarios

### DBFS durable device commit

#### reconstructs exact bytes after an acknowledged fsync and power cut

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- reconstructs exact bytes after an acknowledged fsync and power cut
   - Expected: driver.durability_serialization_blocker() equals `ready`
   - Expected: dev.flush_count() equals `1`
   - Expected: reopened_text(dev, "/state", 32).unwrap() equals `committed-state`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("reconstructs exact bytes after an acknowledged fsync and power cut")
val dev = DurableCrashDevice.new(32, 512)
val driver = DbFsDriver.open_on_device(dev, 0, 32).unwrap()
expect(driver.durability_serialization_ready()).to_be(true)
expect(driver.durability_serialization_blocker()).to_equal("ready")
var mounts = MountTable.new()
mounts.mount("/", DriverInstance.DbFs(driver: driver), MountOptions.default()).unwrap()
val mounted = mounts.lookup_text("/").unwrap()
expect(FsCapabilitySet(bits: mounted.active_caps).has(Capability.DurableSync)).to_be(true)
val handle = mounts.open("/state", OpenFlags.create_write()).unwrap()
mounts.write(handle, "committed-state").unwrap()
mounts.fsync(handle).unwrap()
expect(dev.flush_count()).to_equal(1)
dev.power_cut()
expect(reopened_text(dev, "/state", 32).unwrap()).to_equal("committed-state")
```

</details>

#### fails closed on flush failure and preserves the prior acknowledged checkpoint

- fails closed on flush failure and preserves the prior acknowledged checkpoint
   - Expected: driver.fsync(handle).unwrap_err() equals `FsError.IoError(code: 0u32)`
   - Expected: reopened_text(dev, "/state", 32).unwrap() equals `old`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("fails closed on flush failure and preserves the prior acknowledged checkpoint")
val dev = DurableCrashDevice.new(32, 512)
val driver = DbFsDriver.open_on_device(dev, 0, 32).unwrap()
val handle = driver.open_path(Path(raw: "/state"), OpenFlags.create_write()).unwrap()
driver.write_handle(handle, "old").unwrap()
driver.fsync(handle).unwrap()
driver.write_handle(handle, "new").unwrap()
dev.set_flush_failure(true)
expect(driver.fsync(handle).unwrap_err()).to_equal(FsError.IoError(code: 0u32))
dev.set_flush_failure(false)
dev.power_cut()
expect(reopened_text(dev, "/state", 32).unwrap()).to_equal("old")
```

</details>

#### rejects a higher torn checkpoint whose referenced blob never reached media

- rejects a higher torn checkpoint whose referenced blob never reached media
   - Expected: reopened_text(dev, "/state", 32).unwrap() equals `old`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("rejects a higher torn checkpoint whose referenced blob never reached media")
val dev = DurableCrashDevice.new(32, 512)
val driver = DbFsDriver.open_on_device(dev, 0, 32).unwrap()
val handle = driver.open_path(Path(raw: "/state"), OpenFlags.create_write()).unwrap()
driver.write_handle(handle, "old").unwrap()
driver.fsync(handle).unwrap()
driver.write_handle(handle, "new").unwrap()
dev.persist_checkpoint_sector_without_data(31u64)
dev.power_cut()
expect(reopened_text(dev, "/state", 32).unwrap()).to_equal("old")
```

</details>

#### reports corruption when neither bounded checkpoint slot validates

- reports corruption when neither bounded checkpoint slot validates
   - Expected: DbFsDriver.open_on_device(dev, 0, 32).unwrap_err() equals `FsError.Corrupt`
   - Expected: dbfs_device_registration_count() equals `owners_before`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("reports corruption when neither bounded checkpoint slot validates")
val dev = DurableCrashDevice.new(32, 512)
val driver = DbFsDriver.open_on_device(dev, 0, 32).unwrap()
val handle = driver.open_path(Path(raw: "/state"), OpenFlags.create_write()).unwrap()
driver.write_handle(handle, "old").unwrap()
driver.fsync(handle).unwrap()
dev.corrupt_durable_sector(30u64)
dev.corrupt_durable_sector(31u64)
dev.power_cut()
val owners_before = dbfs_device_registration_count()
expect(DbFsDriver.open_on_device(dev, 0, 32).unwrap_err()).to_equal(FsError.Corrupt)
expect(dbfs_device_registration_count()).to_equal(owners_before)
```

</details>

#### rejects an unavailable durability backend instead of accepting a no-op

- rejects an unavailable durability backend instead of accepting a no-op
   - Expected: driver.fsync(handle).unwrap_err() equals `FsError.IoError(code: 0u32)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("rejects an unavailable durability backend instead of accepting a no-op")
val dev = MemBlockDevice.new(32u64, 512u32)
val driver = DbFsDriver.open_on_device(dev, 0, 32).unwrap()
val handle = driver.open_path(Path(raw: "/state"), OpenFlags.create_write()).unwrap()
driver.write_handle(handle, "volatile").unwrap()
expect(driver.fsync(handle).unwrap_err()).to_equal(FsError.IoError(code: 0u32))
```

</details>

#### bounds the namespace checkpoint and rolls back the rejected entry

- bounds the namespace checkpoint and rolls back the rejected entry
   - Expected: driver.open_path(Path(raw: "/overflow"), OpenFlags.create_write()).unwrap_err() equals `FsError.TooLarge`
   - Expected: driver.stat_path(Path(raw: "/overflow")).unwrap_err() equals `FsError.NotFound`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("bounds the namespace checkpoint and rolls back the rejected entry")
val dev = DurableCrashDevice.new(160, 4096)
val driver = DbFsDriver.open_on_device(dev, 0, 160).unwrap()
var i: i64 = 0
while i < 64:
    driver.open_path(Path(raw: "/f" + i.to_text()), OpenFlags.create_write()).unwrap()
    i = i + 1
expect(driver.open_path(Path(raw: "/overflow"), OpenFlags.create_write()).unwrap_err()).to_equal(FsError.TooLarge)
expect(driver.stat_path(Path(raw: "/overflow")).unwrap_err()).to_equal(FsError.NotFound)
```

</details>

#### serializes interleaved commit transitions without crossing device owners

- serializes interleaved commit transitions without crossing device owners
   - Expected: reopened_text(left, "/state", 32).unwrap() equals `left-2`
   - Expected: reopened_text(right, "/state", 32).unwrap() equals `right-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("serializes interleaved commit transitions without crossing device owners")
val left = DurableCrashDevice.new(32, 512)
val right = DurableCrashDevice.new(32, 512)
val left_driver = DbFsDriver.open_on_device(left, 0, 32).unwrap()
val right_driver = DbFsDriver.open_on_device(right, 0, 32).unwrap()
val left_handle = left_driver.open_path(
    Path(raw: "/state"), OpenFlags.create_write()).unwrap()
val right_handle = right_driver.open_path(
    Path(raw: "/state"), OpenFlags.create_write()).unwrap()
left_driver.write_handle(left_handle, "left-1").unwrap()
right_driver.write_handle(right_handle, "right-1").unwrap()
left_driver.write_handle(left_handle, "left-2").unwrap()
right_driver.fsync(right_handle).unwrap()
left_driver.fsync(left_handle).unwrap()
left.power_cut()
right.power_cut()
expect(reopened_text(left, "/state", 32).unwrap()).to_equal("left-2")
expect(reopened_text(right, "/state", 32).unwrap()).to_equal("right-1")
```

</details>

#### keeps descriptor and namespace visibility coherent across unlink

- keeps descriptor and namespace visibility coherent across unlink
   - Expected: driver.read_handle(handle, 10).unwrap() equals `lease-data`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("keeps descriptor and namespace visibility coherent across unlink")
val dev = DurableCrashDevice.new(32, 512)
val driver = DbFsDriver.open_on_device(dev, 0, 32).unwrap()
val handle = driver.open_path(
    Path(raw: "/leased"), OpenFlags.create_write()).unwrap()
driver.write_handle(handle, "lease-data").unwrap()
driver.unlink_path("/leased").unwrap()
expect(driver.stat_path(Path(raw: "/leased")).unwrap_err()).to_equal(
    FsError.NotFound)
expect(driver.read_handle(handle, 10).unwrap()).to_equal("lease-data")
driver.close_handle(handle).unwrap()
expect(driver.read_handle(handle, 10).unwrap_err()).to_equal(
    FsError.InvalidArg)
```

</details>

#### uses one append cursor for passthrough bytes and committed file blobs

- uses one append cursor for passthrough bytes and committed file blobs
   - Expected: driver.write_passthrough(prefix).unwrap() equals `1`
   - Expected: reopened_text(dev, "/state", 32).unwrap() equals `after-prefix`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("uses one append cursor for passthrough bytes and committed file blobs")
val dev = DurableCrashDevice.new(32, 512)
val driver = DbFsDriver.open_on_device(dev, 0, 32).unwrap()
var prefix: [u8] = []
prefix.push(0xA5u8)
expect(driver.write_passthrough(prefix).unwrap()).to_equal(1)
val handle = driver.open_path(
    Path(raw: "/state"), OpenFlags.create_write()).unwrap()
driver.write_handle(handle, "after-prefix").unwrap()
driver.fsync(handle).unwrap()
dev.power_cut()
expect(reopened_text(dev, "/state", 32).unwrap()).to_equal("after-prefix")
```

</details>

#### flushes unbound passthrough bytes even without a pending checkpoint

- flushes unbound passthrough bytes even without a pending checkpoint
   - Expected: driver.write_passthrough([0xA5u8]).unwrap() equals `1`
   - Expected: dev.flush_count() equals `flushes_before + 1`
   - Expected: dev.read_sector(1u64).unwrap()[0] equals `0xA5u8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("flushes unbound passthrough bytes even without a pending checkpoint")
val dev = DurableCrashDevice.new(32, 512)
val driver = DbFsDriver.open_on_device(dev, 0, 32).unwrap()
val handle = driver.open_path(
    Path(raw: "/sync-anchor"), OpenFlags.create_write()).unwrap()
driver.fsync(handle).unwrap()
val flushes_before = dev.flush_count()
expect(driver.write_passthrough([0xA5u8]).unwrap()).to_equal(1)
driver.fsync(handle).unwrap()
expect(dev.flush_count()).to_equal(flushes_before + 1)
dev.power_cut()
expect(dev.read_sector(1u64).unwrap()[0]).to_equal(0xA5u8)
```

</details>

#### rejects the SimpleOS no-op mutex provider with a stable blocker

- rejects the SimpleOS no-op mutex provider with a stable blocker
   - Expected: dbfs_device_mutex_provider_blocker("linux") equals `ready`
   - Expected: DbFsDriver.device_durability_blocker() equals `ready`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("rejects the SimpleOS no-op mutex provider with a stable blocker")
expect(dbfs_device_mutex_provider_blocker(
    "x86_64-baremetal-simpleos")).to_equal(
        DBFS_DEVICE_SERIALIZATION_MISSING)
expect(dbfs_device_mutex_provider_blocker("unknown")).to_equal(
    DBFS_DEVICE_SERIALIZATION_MISSING)
expect(dbfs_device_mutex_provider_blocker("linux")).to_equal("ready")
expect(DbFsDriver.device_durability_blocker()).to_equal("ready")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-INTEGRATION`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `2ce3243b73905a79a0810a0cb1ebb06fec0b2acdff3debaa326069e133d548b1`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `2ce3243b73905a79a0810a0cb1ebb06fec0b2acdff3debaa326069e133d548b1`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `2ce3243b73905a79a0810a0cb1ebb06fec0b2acdff3debaa326069e133d548b1`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/02_integration/storage/dbfs/dbfs_durable_commit_spec.spl
mirror: doc/06_spec/02_integration/storage/dbfs/dbfs_durable_commit_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/02_integration/storage/dbfs/dbfs_durable_commit_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/02_integration/storage/dbfs/dbfs_durable_commit_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/02_integration/storage/dbfs/dbfs_durable_commit_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/02_integration/storage/dbfs/dbfs_durable_commit_spec.spl:165:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reconstructs exact bytes after an acknowledged fsync and power cut' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/storage/dbfs/dbfs_durable_commit_spec.spl:183:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'fails closed on flush failure and preserves the prior acknowledged checkpoint' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/storage/dbfs/dbfs_durable_commit_spec.spl:198:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects a higher torn checkpoint whose referenced blob never reached media' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
