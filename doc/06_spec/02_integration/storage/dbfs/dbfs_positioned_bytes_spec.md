# dbfs_positioned_bytes_spec

> The canonical DBFS byte owner must preserve arbitrary bytes, return short EOF

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# dbfs_positioned_bytes_spec

The canonical DBFS byte owner must preserve arbitrary bytes, return short EOF

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/02_integration/storage/dbfs/dbfs_positioned_bytes_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
## Operator workflow
## Compatibility and limitations


The canonical DBFS byte owner must preserve arbitrary bytes, return short EOF
reads, keep overwrite suffixes, zero-fill holes, reject invalid signed ranges,
and reject stale handles without routing through the legacy text primitives.

## Scenarios

### DBFS binary positioned I/O

#### returns an owned short binary read from a nonzero offset

- Verify: returns an owned short binary read from a nonzero offset
- Read through EOF without padding
   - Expected: got equals `[0x80u8, 0x41u8, 0x7fu8]`
   - Expected: driver.pread_bytes_handle(handle, 5, 1).unwrap() equals `[]`
- Keep each result independently owned
   - Expected: driver.pread_bytes_handle(handle, 2, 1).unwrap() equals `[0x80u8]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Verify: returns an owned short binary read from a nonzero offset")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val (driver, handle) = open_positioned_fixture("/dbfs-short-read.bin")
val seed: [u8] = [0x00u8, 0xffu8, 0x80u8, 0x41u8, 0x7fu8]
driver.write_bytes_handle(handle, seed).unwrap()

step("Read through EOF without padding")
val got = driver.pread_bytes_handle(handle, 2, 8).unwrap()
expect(got).to_equal([0x80u8, 0x41u8, 0x7fu8])
expect(driver.pread_bytes_handle(handle, 5, 1).unwrap()).to_equal([])

step("Keep each result independently owned")
got[0] = 0x11u8
expect(driver.pread_bytes_handle(handle, 2, 1).unwrap()).to_equal([0x80u8])
```

</details>

#### preserves binary prefix and suffix around an overwrite

- Verify: preserves binary prefix and suffix around an overwrite
- Overwrite only the selected byte range


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Verify: preserves binary prefix and suffix around an overwrite")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val (driver, handle) = open_positioned_fixture("/dbfs-overwrite.bin")
driver.write_bytes_handle(
    handle, [0x00u8, 0xffu8, 0x80u8, 0x7fu8]).unwrap()

step("Overwrite only the selected byte range")
expect(driver.pwrite_bytes_handle(
    handle, 1, [0xfeu8, 0x00u8]).unwrap()).to_equal(2)  # oracle: pinned constant asserted by this scenario
expect(driver.pread_bytes_handle(handle, 0, 8).unwrap()).to_equal(
    [0x00u8, 0xfeu8, 0x00u8, 0x7fu8])
```

</details>

#### zero-fills a hole and reports the exact new size

- Verify: zero-fills a hole and reports the exact new size
- Write beyond EOF
   - Expected: driver.stat_path(Path(raw: "/dbfs-hole.bin")).unwrap().size equals `6)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Verify: zero-fills a hole and reports the exact new size")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val (driver, handle) = open_positioned_fixture("/dbfs-hole.bin")
driver.write_bytes_handle(handle, [0x31u8, 0x32u8]).unwrap()

step("Write beyond EOF")
expect(driver.pwrite_bytes_handle(
    handle, 5, [0xffu8]).unwrap()).to_equal(1)  # oracle: pinned constant asserted by this scenario
expect(driver.pread_bytes_handle(handle, 0, 9).unwrap()).to_equal(
    [0x31u8, 0x32u8, 0u8, 0u8, 0u8, 0xffu8])
expect(driver.stat_path(Path(raw: "/dbfs-hole.bin")).unwrap().size).to_equal(6)  # oracle: pinned constant asserted by this scenario
```

</details>

#### rejects invalid ranges before mutating file bytes

- Verify: rejects invalid ranges before mutating file bytes
- Reject negative, overflowing, and impractically large ranges
- Retain the original bytes


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Verify: rejects invalid ranges before mutating file bytes")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val (driver, handle) = open_positioned_fixture("/dbfs-invalid.bin")
driver.write_bytes_handle(handle, [0x41u8, 0x42u8]).unwrap()

step("Reject negative, overflowing, and impractically large ranges")
expect(driver.pread_bytes_handle(
    handle, -1, 1).unwrap_err()).to_equal(FsError.InvalidArg)
expect(driver.pread_bytes_handle(
    handle, 0, -1).unwrap_err()).to_equal(FsError.InvalidArg)
expect(driver.pwrite_bytes_handle(
    handle, -1, [0x99u8]).unwrap_err()).to_equal(FsError.InvalidArg)
expect(driver.pwrite_bytes_handle(
    handle, 9223372036854775807, [0x99u8]).unwrap_err()).to_equal(
        FsError.InvalidArg)
expect(driver.pwrite_bytes_handle(
    handle, 1099511627776, [0x99u8]).unwrap_err()).to_equal(
        FsError.TooLarge)

step("Retain the original bytes")
expect(driver.pread_bytes_handle(handle, 0, 2).unwrap()).to_equal(
    [0x41u8, 0x42u8])
```

</details>

#### rejects closed and unknown handles as stale

- Verify: rejects closed and unknown handles as stale
- Reject the retired handle
- Reject a handle that was never allocated


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Verify: rejects closed and unknown handles as stale")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val (driver, handle) = open_positioned_fixture("/dbfs-stale.bin")
driver.write_bytes_handle(handle, [0x41u8]).unwrap()
driver.close_handle(handle).unwrap()

step("Reject the retired handle")
expect(driver.pread_bytes_handle(
    handle, 0, 1).unwrap_err()).to_equal(FsError.StaleHandle)
expect(driver.pwrite_bytes_handle(
    handle, 0, [0x42u8]).unwrap_err()).to_equal(FsError.StaleHandle)

step("Reject a handle that was never allocated")
val unknown = FileHandle(id: 9223372036854775807u64)
expect(driver.pread_bytes_handle(
    unknown, 0, 1).unwrap_err()).to_equal(FsError.StaleHandle)
```

</details>

#### commits positioned bytes through a device-backed driver

- Verify: commits positioned bytes through a device-backed driver
   - Expected: opened.is_ok() is true
- Commit an overwrite through the DBFS arena
- Reopen the same device region and replay the committed bytes


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Verify: commits positioned bytes through a device-backed driver")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val dev = MemBlockDevice.new(1024u64, 512u32)
val opened = DbFsDriver.open_on_device(dev, 64i64, 256i64)
expect(opened.is_ok()).to_equal(true)
val driver = opened.unwrap()
val path = Path(raw: "/dbfs-device-positioned.bin")
val handle = driver.open_path(
    path, OpenFlags.read_write().with_create()).unwrap()
driver.write_bytes_handle(
    handle, [0x00u8, 0xffu8, 0x80u8, 0x41u8]).unwrap()

step("Commit an overwrite through the DBFS arena")
expect(driver.pwrite_bytes_handle(
    handle, 1, [0x22u8, 0x00u8]).unwrap()).to_equal(2)  # oracle: pinned constant asserted by this scenario
expect(driver.pread_bytes_handle(handle, 0, 4).unwrap()).to_equal(
    [0x00u8, 0x22u8, 0x00u8, 0x41u8])

step("Reopen the same device region and replay the committed bytes")
driver.close_handle(handle).unwrap()
val replayed = DbFsDriver.open_on_device(dev, 64i64, 256i64).unwrap()
val replayed_handle = replayed.open_path(path, OpenFlags.read_only()).unwrap()
expect(replayed.pread_bytes_handle(
    replayed_handle, 0, 4).unwrap()).to_equal(
        [0x00u8, 0x22u8, 0x00u8, 0x41u8])
```

</details>

#### does not publish a positioned image that exceeds remaining device capacity

- Verify: does not publish a positioned image that exceeds remaining device capacity
- Reject the copy-on-write image before allocating or publishing it
- Keep the prior inode and durable namespace authoritative
   - Expected: driver.stat_path(path).unwrap().size equals `2)  # oracle: pinned constant asserted by this scenario`
   - Expected: replayed.stat_path(path).unwrap().size equals `2)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Verify: does not publish a positioned image that exceeds remaining device capacity")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val dev = MemBlockDevice.new(32u64, 512u32)
val driver = DbFsDriver.open_on_device(dev, 8i64, 3i64).unwrap()
val path = Path(raw: "/dbfs-full-device.bin")
val handle = driver.open_path(
    path, OpenFlags.read_write().with_create()).unwrap()
driver.write_bytes_handle(handle, [0x41u8, 0x42u8]).unwrap()

step("Reject the copy-on-write image before allocating or publishing it")
expect(driver.pwrite_bytes_handle(
    handle, 510, [0x99u8]).unwrap_err()).to_equal(FsError.TooLarge)

step("Keep the prior inode and durable namespace authoritative")
expect(driver.stat_path(path).unwrap().size).to_equal(2)  # oracle: pinned constant asserted by this scenario
expect(driver.pread_bytes_handle(handle, 0, 4).unwrap()).to_equal(
    [0x41u8, 0x42u8])
driver.close_handle(handle).unwrap()
val replayed = DbFsDriver.open_on_device(dev, 8i64, 3i64).unwrap()
val replayed_handle = replayed.open_path(path, OpenFlags.read_only()).unwrap()
expect(replayed.stat_path(path).unwrap().size).to_equal(2)  # oracle: pinned constant asserted by this scenario
expect(replayed.pread_bytes_handle(
    replayed_handle, 0, 4).unwrap()).to_equal([0x41u8, 0x42u8])
```

</details>

#### rolls back inode publication when the namespace commit fails

- Verify: rolls back inode publication when the namespace commit fails
- Inject a failure at the namespace publication boundary
- Retain the prior in-memory and durable inode image
   - Expected: driver.stat_path(path).unwrap().size equals `2)  # oracle: pinned constant asserted by this scenario`
   - Expected: replayed.stat_path(path).unwrap().size equals `2)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SQ-021
step("Verify: rolls back inode publication when the namespace commit fails")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val dev = NamespaceCommitFailBlockDevice.new(64u64, 19u64)
val driver = DbFsDriver.open_on_device(dev, 16i64, 4i64).unwrap()
val path = Path(raw: "/dbfs-commit-failure.bin")
val handle = driver.open_path(
    path, OpenFlags.read_write().with_create()).unwrap()
driver.write_bytes_handle(handle, [0x51u8, 0x52u8]).unwrap()

step("Inject a failure at the namespace publication boundary")
expect(driver.pwrite_bytes_handle(
    handle, 1, [0x99u8]).unwrap_err()).to_equal(
        FsError.IoError(code: 0))

step("Retain the prior in-memory and durable inode image")
expect(driver.stat_path(path).unwrap().size).to_equal(2)  # oracle: pinned constant asserted by this scenario
expect(driver.pread_bytes_handle(handle, 0, 4).unwrap()).to_equal(
    [0x51u8, 0x52u8])
driver.close_handle(handle).unwrap()
val replayed = DbFsDriver.open_on_device(dev, 16i64, 4i64).unwrap()
val replayed_handle = replayed.open_path(path, OpenFlags.read_only()).unwrap()
expect(replayed.stat_path(path).unwrap().size).to_equal(2)  # oracle: pinned constant asserted by this scenario
expect(replayed.pread_bytes_handle(
    replayed_handle, 0, 4).unwrap()).to_equal([0x51u8, 0x52u8])
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `3bedec8d0fa331704f9a7afa510e92198266c0f5c72f511d5fc8afdafde0365a`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `3bedec8d0fa331704f9a7afa510e92198266c0f5c72f511d5fc8afdafde0365a`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `3bedec8d0fa331704f9a7afa510e92198266c0f5c72f511d5fc8afdafde0365a`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/02_integration/storage/dbfs/dbfs_positioned_bytes_spec.spl
mirror: doc/06_spec/02_integration/storage/dbfs/dbfs_positioned_bytes_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/02_integration/storage/dbfs/dbfs_positioned_bytes_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/02_integration/storage/dbfs/dbfs_positioned_bytes_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/02_integration/storage/dbfs/dbfs_positioned_bytes_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, traceability, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
