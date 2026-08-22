# positioned_filesystem_backends_spec

> Verifies the positioned filesystem backends behaviour end to end so maintainers of this

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# positioned_filesystem_backends_spec

Verifies the positioned filesystem backends behaviour end to end so maintainers of this

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/sosix/positioned_filesystem_backends_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Verifies the positioned filesystem backends behaviour end to end so maintainers of this
component and reviewers of its spec share one pinned definition.
## Operator workflow
Run `bin/simple test <this spec>`; read the per-scenario verdicts in
the `Results:` summary. Each scenario asserts an observable outcome.
## Compatibility and limitations
Covers the currently shipped behaviour only; performance, stress and
unrelated sibling features are out of scope.

## Scenarios

### SOSIX positioned filesystem backends

#### should round-trip binary DBFS bytes with overwrite and sparse extension

- Verify: should round-trip binary DBFS bytes with overwrite and sparse extension
- Exercise NVFS and DBFS positioned owners
   - Expected: backend.write_at(object_id, 2, [0u8, 255u8]).unwrap() equals `2u64`
   - Expected: backend.read_at(object_id, 0, 8).unwrap() equals `[0u8, 0u8, 0u8, 255u8]`
   - Expected: backend.write_at(object_id, 1, [7u8]).unwrap() equals `1u64`
   - Expected: backend.read_at(object_id, 0, 8).unwrap() equals `[0u8, 7u8, 0u8, 255u8]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Verify: should round-trip binary DBFS bytes with overwrite and sparse extension")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Exercise NVFS and DBFS positioned owners")
val object_id = mount_dbfs_object("/dbfs.bin")
val backend = SosixDbfsPositionedVfsBackendV1()
expect(backend.write_at(object_id, 2, [0u8, 255u8]).unwrap()).to_equal(2u64)
expect(backend.read_at(object_id, 0, 8).unwrap()).to_equal([0u8, 0u8, 0u8, 255u8])
expect(backend.write_at(object_id, 1, [7u8]).unwrap()).to_equal(1u64)
expect(backend.read_at(object_id, 0, 8).unwrap()).to_equal([0u8, 7u8, 0u8, 255u8])
```

</details>

#### should round-trip binary NVFS bytes without changing read position

- Verify: should round-trip binary NVFS bytes without changing read position
- Exercise NVFS and DBFS positioned owners
   - Expected: backend.write_at(object_id, 0, [10u8, 20u8, 30u8, 40u8]).unwrap() equals `4u64`
   - Expected: backend.read_at(object_id, 2, 2).unwrap() equals `[30u8, 40u8]`
   - Expected: backend.read_at(object_id, 0, 2).unwrap() equals `[10u8, 20u8]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SQ-021
step("Verify: should round-trip binary NVFS bytes without changing read position")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Exercise NVFS and DBFS positioned owners")
val object_id = mount_nvfs_object("/nvfs.bin")
val backend = SosixNvfsPositionedVfsBackendV1()
expect(backend.write_at(object_id, 0, [10u8, 20u8, 30u8, 40u8]).unwrap()).to_equal(4u64)
expect(backend.read_at(object_id, 2, 2).unwrap()).to_equal([30u8, 40u8])
expect(backend.read_at(object_id, 0, 2).unwrap()).to_equal([10u8, 20u8])
```

</details>

#### should reject cross-filesystem and retired object identities

- Verify: should reject cross-filesystem and retired object identities
- Validate positioned filesystem source contracts
   - Expected: nvfs.read_at(object_id, 0, 1).unwrap_err() equals `nvfs-positioned-unsupported`
   - Expected: dbfs.read_at(object_id, 0, 1).unwrap_err() equals `dbfs-positioned-stale-file-object`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SQ-021
step("Verify: should reject cross-filesystem and retired object identities")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Validate positioned filesystem source contracts")
val object_id = mount_dbfs_object("/kind.bin")
val nvfs = SosixNvfsPositionedVfsBackendV1()
val dbfs = SosixDbfsPositionedVfsBackendV1()
expect(nvfs.read_at(object_id, 0, 1).unwrap_err()).to_equal("nvfs-positioned-unsupported")
g_vfs_positioned_close(object_id).unwrap()
expect(dbfs.read_at(object_id, 0, 1).unwrap_err()).to_equal("dbfs-positioned-stale-file-object")
```

</details>

#### should reject raw and overflowing object requests before driver dispatch

- Verify: should reject raw and overflowing object requests before driver dispatch
- Validate positioned filesystem source contracts
   - Expected: backend.read_at(1u64, 0, 1).unwrap_err() equals `dbfs-positioned-stale-file-object`
   - Expected: backend.read_at(1u64, 0xffffffffffffffffu64, 2).unwrap_err() equals `dbfs-positioned-invalid-argument`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SQ-021
step("Verify: should reject raw and overflowing object requests before driver dispatch")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Validate positioned filesystem source contracts")
val backend = SosixDbfsPositionedVfsBackendV1()
expect(backend.read_at(1u64, 0, 1).unwrap_err()).to_equal("dbfs-positioned-stale-file-object")
expect(backend.read_at(1u64, 0xffffffffffffffffu64, 2).unwrap_err()).to_equal("dbfs-positioned-invalid-argument")
```

</details>

#### should keep colliding raw driver handles distinct behind virtual objects

- Verify: should keep colliding raw driver handles distinct behind virtual objects
- Validate positioned filesystem source contracts


<details>
<summary>Executable SSpec</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SQ-021 REQ-SQ-022
step("Verify: should keep colliding raw driver handles distinct behind virtual objects")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Validate positioned filesystem source contracts")
var table = MountTable.new()
table.mount(
    "/", DriverInstance.Nvfs(NvfsDriver.new("collision-nvfs")),
    MountOptions.default()).unwrap()
table.mount(
    "/db", DriverInstance.DbFs(DbFsDriver.new_hosted()),
    MountOptions.default()).unwrap()
val nvfs_object = table.open("/nvfs.bin", OpenFlags.create_write()).unwrap()
val dbfs_object = table.open("/db/dbfs.bin", OpenFlags.create_write()).unwrap()
expect(nvfs_object.id == dbfs_object.id).to_be(false)
expect(table.positioned_write_bytes(
    nvfs_object.id, PositionedDriverKind.Nvfs, 0u64, [11u8]).unwrap()).to_equal(1u64)
expect(table.positioned_write_bytes(
    dbfs_object.id, PositionedDriverKind.Dbfs, 0u64, [22u8]).unwrap()).to_equal(1u64)
expect(table.positioned_read_bytes(
    nvfs_object.id, PositionedDriverKind.Nvfs, 0u64, 1u64).unwrap()).to_equal([11u8])
expect(table.positioned_read_bytes(
    dbfs_object.id, PositionedDriverKind.Dbfs, 0u64, 1u64).unwrap()).to_equal([22u8])
expect(table.positioned_read_bytes(
    nvfs_object.id, PositionedDriverKind.Auto, 0u64, 1u64).unwrap()).to_equal([11u8])
expect(table.positioned_write_bytes(
    dbfs_object.id, PositionedDriverKind.Auto, 0u64, [33u8]).unwrap()).to_equal(1u64)
expect(table.positioned_read_bytes(
    dbfs_object.id, PositionedDriverKind.Auto, 0u64, 1u64).unwrap()).to_equal([33u8])
```

</details>

<details>
<summary>Advanced: should publish a complete FAT32 NVFS DBFS and durable-sync routing matrix</summary>

#### should publish a complete FAT32 NVFS DBFS and durable-sync routing matrix

- Verify: should publish a complete FAT32 NVFS DBFS and durable-sync routing matrix
- Validate every shared filesystem routing entry point
   - Expected: g_vfs_fat32_read_at(0u64, 0u64, 1u64).unwrap_err() equals `FsError.InvalidArg`
   - Expected: g_vfs_fat32_write_at(0u64, 0u64, [1u8]).unwrap_err() equals `FsError.InvalidArg`
   - Expected: g_vfs_nvfs_read_at(0u64, 0u64, 1u64).unwrap_err() equals `FsError.InvalidArg`
   - Expected: g_vfs_nvfs_write_at(0u64, 0u64, [1u8]).unwrap_err() equals `FsError.InvalidArg`
   - Expected: g_vfs_dbfs_read_at(0u64, 0u64, 1u64).unwrap_err() equals `FsError.InvalidArg`
   - Expected: g_vfs_dbfs_write_at(0u64, 0u64, [1u8]).unwrap_err() equals `FsError.InvalidArg`
   - Expected: g_vfs_fsync(0u64).unwrap_err() equals `FsError.StaleHandle`
   - Expected: g_vfs_fdatasync(0u64).unwrap_err() equals `FsError.StaleHandle`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SQ-021 REQ-SQ-022
step("Verify: should publish a complete FAT32 NVFS DBFS and durable-sync routing matrix")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Validate every shared filesystem routing entry point")
expect(g_vfs_fat32_read_at(0u64, 0u64, 1u64).unwrap_err()).to_equal(FsError.InvalidArg)
expect(g_vfs_fat32_write_at(0u64, 0u64, [1u8]).unwrap_err()).to_equal(FsError.InvalidArg)
expect(g_vfs_nvfs_read_at(0u64, 0u64, 1u64).unwrap_err()).to_equal(FsError.InvalidArg)
expect(g_vfs_nvfs_write_at(0u64, 0u64, [1u8]).unwrap_err()).to_equal(FsError.InvalidArg)
expect(g_vfs_dbfs_read_at(0u64, 0u64, 1u64).unwrap_err()).to_equal(FsError.InvalidArg)
expect(g_vfs_dbfs_write_at(0u64, 0u64, [1u8]).unwrap_err()).to_equal(FsError.InvalidArg)
expect(g_vfs_fsync(0u64).unwrap_err()).to_equal(FsError.StaleHandle)
expect(g_vfs_fdatasync(0u64).unwrap_err()).to_equal(FsError.StaleHandle)
```

</details>


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

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `d7f6ff3f0cdf3bd080b3aa319f5defcf0e075fd52dab8f179f031a2fb5c45572`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `d7f6ff3f0cdf3bd080b3aa319f5defcf0e075fd52dab8f179f031a2fb5c45572`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `d7f6ff3f0cdf3bd080b3aa319f5defcf0e075fd52dab8f179f031a2fb5c45572`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/01_unit/os/sosix/positioned_filesystem_backends_spec.spl
mirror: doc/06_spec/01_unit/os/sosix/positioned_filesystem_backends_spec.md (current)
findings: 9 blockers: 0
  narrative=100 structure=70 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/sosix/positioned_filesystem_backends_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/01_unit/os/sosix/positioned_filesystem_backends_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/sosix/positioned_filesystem_backends_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, traceability, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/sosix/positioned_filesystem_backends_spec.spl:56:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should round-trip binary DBFS bytes with overwrite and sparse extension' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/os/sosix/positioned_filesystem_backends_spec.spl:69:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should round-trip binary NVFS bytes without changing read position' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/os/sosix/positioned_filesystem_backends_spec.spl:81:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject cross-filesystem and retired object identities' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/os/sosix/positioned_filesystem_backends_spec.spl:94:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject raw and overflowing object requests before driver dispatch' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/os/sosix/positioned_filesystem_backends_spec.spl:104:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should keep colliding raw driver handles distinct behind virtual objects' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/os/sosix/positioned_filesystem_backends_spec.spl:134:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should publish a complete FAT32 NVFS DBFS and durable-sync routing matrix' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
