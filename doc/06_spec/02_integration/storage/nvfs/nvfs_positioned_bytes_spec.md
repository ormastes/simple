# nvfs_positioned_bytes_spec

> The POSIX-compatible NVFS driver must preserve arbitrary bytes, return short

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# nvfs_positioned_bytes_spec

The POSIX-compatible NVFS driver must preserve arbitrary bytes, return short

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/02_integration/storage/nvfs/nvfs_positioned_bytes_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
## Operator workflow
## Compatibility and limitations


The POSIX-compatible NVFS driver must preserve arbitrary bytes, return short
reads at EOF, create zero-filled holes, and reject invalid signed ranges before
delegating to its DBFS byte owner.

## Scenarios

### NVFS binary positioned I/O

#### replays positioned bytes from a block device after native reopen

- Verify: replays positioned bytes from a block device after native reopen
- Create a device-backed native NVFS driver
   - Expected: first.name equals `nvfs-positioned-device-first`
   - Expected: first.pwrite(handle, 0, payload).unwrap() equals `4)  # oracle: pinned constant asserted by this scenario`
- Open a fresh driver on the same device region
   - Expected: second.pread(reopened, 0, out).unwrap() equals `4)  # oracle: pinned constant asserted by this scenario`
   - Expected: out equals `payload`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Verify: replays positioned bytes from a block device after native reopen")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val dev = RamBlockDevice.new_empty()
val path = Path(raw: "/nvfs-device-positioned.bin")

step("Create a device-backed native NVFS driver")
val first = NvfsDriver.new_on_device(
    "nvfs-positioned-device-first", dev, 2048, 128).unwrap()
expect(first.name).to_equal("nvfs-positioned-device-first")
val handle = first.open(
    path, OpenFlags.read_write().with_create()).unwrap()
val payload: [u8] = [0x00u8, 0xffu8, 0x80u8, 0x41u8]
expect(first.pwrite(handle, 0, payload).unwrap()).to_equal(4)  # oracle: pinned constant asserted by this scenario
first.close(handle).unwrap()

step("Open a fresh driver on the same device region")
val second = NvfsDriver.new_on_device(
    "nvfs-positioned-device-second", dev, 2048, 128).unwrap()
val reopened = second.open(path, OpenFlags.read_only()).unwrap()
var out: [u8] = [0u8, 0u8, 0u8, 0u8]
expect(second.pread(reopened, 0, out).unwrap()).to_equal(4)  # oracle: pinned constant asserted by this scenario
expect(out).to_equal(payload)
```

</details>

#### exposes positioned binary I/O from the POSIX device constructor

- Verify: exposes positioned binary I/O from the POSIX device constructor
- Patch and read arbitrary bytes through the device-backed facade
   - Expected: driver.pwrite(handle, 2, [0x00u8, 0xffu8]).unwrap() equals `2)  # oracle: pinned constant asserted by this scenario`
   - Expected: driver.pread(handle, 0, out).unwrap() equals `4)  # oracle: pinned constant asserted by this scenario`
   - Expected: out equals `[0u8, 0u8, 0x00u8, 0xffu8]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Verify: exposes positioned binary I/O from the POSIX device constructor")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val dev = RamBlockDevice.new_empty()
val driver = NvfsPosixDriver.new_on_device(
    "nvfs-posix-device", dev, 4096, 128).unwrap()
val handle = driver.open(
    Path(raw: "/nvfs-posix-device.bin"),
    OpenFlags.read_write().with_create()).unwrap()

step("Patch and read arbitrary bytes through the device-backed facade")
expect(driver.pwrite(handle, 2, [0x00u8, 0xffu8]).unwrap()).to_equal(2)  # oracle: pinned constant asserted by this scenario
var out: [u8] = [0xaau8, 0xaau8, 0xaau8, 0xaau8]
expect(driver.pread(handle, 0, out).unwrap()).to_equal(4)  # oracle: pinned constant asserted by this scenario
expect(out).to_equal([0u8, 0u8, 0x00u8, 0xffu8])
```

</details>

#### returns an owned short binary read from a nonzero offset

- Verify: returns an owned short binary read from a nonzero offset
- Seed bytes that are not safe to round-trip through text
   - Expected: driver.pwrite(handle, 0, seed).unwrap() equals `5)  # oracle: pinned constant asserted by this scenario`
- Read past EOF without padding the caller buffer
   - Expected: read_count equals `3)  # oracle: pinned constant asserted by this scenario`
   - Expected: out[0] equals `0x80u8`
   - Expected: out[1] equals `0x41u8`
   - Expected: out[2] equals `0x7fu8`
   - Expected: out[3] equals `0xaau8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Verify: returns an owned short binary read from a nonzero offset")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Seed bytes that are not safe to round-trip through text")
val (driver, handle) = open_positioned_fixture(
    "nvfs-positioned-short-read", "/positioned-short-read.bin")
val seed: [u8] = [0x00u8, 0xffu8, 0x80u8, 0x41u8, 0x7fu8]
expect(driver.pwrite(handle, 0, seed).unwrap()).to_equal(5)  # oracle: pinned constant asserted by this scenario

step("Read past EOF without padding the caller buffer")
var out: [u8] = [0xaau8, 0xaau8, 0xaau8, 0xaau8, 0xaau8]
val read_count = driver.pread(handle, 2, out).unwrap()
expect(read_count).to_equal(3)  # oracle: pinned constant asserted by this scenario
expect(out[0]).to_equal(0x80u8)
expect(out[1]).to_equal(0x41u8)
expect(out[2]).to_equal(0x7fu8)
expect(out[3]).to_equal(0xaau8)
```

</details>

#### preserves binary prefix and suffix around a positioned overwrite

- Verify: preserves binary prefix and suffix around a positioned overwrite
   - Expected: driver.pwrite(handle, 0, seed).unwrap() equals `4)  # oracle: pinned constant asserted by this scenario`
- Overwrite only the selected binary range
   - Expected: driver.pwrite(handle, 1, patch).unwrap() equals `2)  # oracle: pinned constant asserted by this scenario`
   - Expected: driver.pread(handle, 0, out).unwrap() equals `4)  # oracle: pinned constant asserted by this scenario`
   - Expected: out equals `[0x00u8, 0xfeu8, 0x00u8, 0x7fu8]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Verify: preserves binary prefix and suffix around a positioned overwrite")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val (driver, handle) = open_positioned_fixture(
    "nvfs-positioned-overwrite", "/positioned-overwrite.bin")
val seed: [u8] = [0x00u8, 0xffu8, 0x80u8, 0x7fu8]
expect(driver.pwrite(handle, 0, seed).unwrap()).to_equal(4)  # oracle: pinned constant asserted by this scenario

step("Overwrite only the selected binary range")
val patch: [u8] = [0xfeu8, 0x00u8]
expect(driver.pwrite(handle, 1, patch).unwrap()).to_equal(2)  # oracle: pinned constant asserted by this scenario
var out: [u8] = [0u8, 0u8, 0u8, 0u8]
expect(driver.pread(handle, 0, out).unwrap()).to_equal(4)  # oracle: pinned constant asserted by this scenario
expect(out).to_equal([0x00u8, 0xfeu8, 0x00u8, 0x7fu8])
```

</details>

#### zero-fills a positioned-write hole and retains it across reopen

- Verify: zero-fills a positioned-write hole and retains it across reopen
   - Expected: driver.pwrite(handle, 0, [0x31u8, 0x32u8]).unwrap() equals `2)  # oracle: pinned constant asserted by this scenario`
- Write beyond EOF and require a zero-filled gap
   - Expected: driver.pwrite(handle, 5, [0xffu8]).unwrap() equals `1)  # oracle: pinned constant asserted by this scenario`
- Reopen through the persisted-file mirror
   - Expected: driver.pread(reopened, 0, out).unwrap() equals `6)  # oracle: pinned constant asserted by this scenario`
   - Expected: out equals `[0x31u8, 0x32u8, 0u8, 0u8, 0u8, 0xffu8]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Verify: zero-fills a positioned-write hole and retains it across reopen")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val path = "/positioned-hole.bin"
val (driver, handle) = open_positioned_fixture(
    "nvfs-positioned-hole", path)
expect(driver.pwrite(handle, 0, [0x31u8, 0x32u8]).unwrap()).to_equal(2)  # oracle: pinned constant asserted by this scenario

step("Write beyond EOF and require a zero-filled gap")
expect(driver.pwrite(handle, 5, [0xffu8]).unwrap()).to_equal(1)  # oracle: pinned constant asserted by this scenario
driver.close(handle).unwrap()

step("Reopen through the persisted-file mirror")
val reopened = driver.open(Path(raw: path), OpenFlags.read_only()).unwrap()
var out: [u8] = [0xaau8, 0xaau8, 0xaau8, 0xaau8, 0xaau8, 0xaau8]
expect(driver.pread(reopened, 0, out).unwrap()).to_equal(6)  # oracle: pinned constant asserted by this scenario
expect(out).to_equal([0x31u8, 0x32u8, 0u8, 0u8, 0u8, 0xffu8])
```

</details>

#### rejects negative and overflowing ranges without mutation

- Verify: rejects negative and overflowing ranges without mutation
   - Expected: driver.pwrite(handle, 0, [0x41u8, 0x42u8]).unwrap() equals `2)  # oracle: pinned constant asserted by this scenario`
- Reject invalid ranges at the NVFS boundary
   - Expected: driver.pwrite(handle, -1, [0x99u8]).unwrap_err() equals `FsError.InvalidArg`
- Prove rejected writes left the file unchanged
   - Expected: driver.pread(handle, 0, out).unwrap() equals `2)  # oracle: pinned constant asserted by this scenario`
   - Expected: out equals `[0x41u8, 0x42u8]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SQ-021
step("Verify: rejects negative and overflowing ranges without mutation")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val (driver, handle) = open_positioned_fixture(
    "nvfs-positioned-invalid", "/positioned-invalid.bin")
expect(driver.pwrite(handle, 0, [0x41u8, 0x42u8]).unwrap()).to_equal(2)  # oracle: pinned constant asserted by this scenario

step("Reject invalid ranges at the NVFS boundary")
var rejected_read: [u8] = [0u8]
expect(driver.pread(
    handle, -1, rejected_read).unwrap_err()).to_equal(FsError.InvalidArg)
expect(driver.pwrite(handle, -1, [0x99u8]).unwrap_err()).to_equal(FsError.InvalidArg)
expect(driver.pwrite(
    handle, 9223372036854775807, [0x99u8]).unwrap_err()).to_equal(FsError.InvalidArg)

step("Prove rejected writes left the file unchanged")
var out: [u8] = [0u8, 0u8]
expect(driver.pread(handle, 0, out).unwrap()).to_equal(2)  # oracle: pinned constant asserted by this scenario
expect(out).to_equal([0x41u8, 0x42u8])
```

</details>

### native NVFS binary positioned I/O

#### uses byte-exact pread and pwrite at arbitrary valid offsets

- Verify: uses byte-exact pread and pwrite at arbitrary valid offsets
   - Expected: driver.pwrite(handle, 0, seed).unwrap() equals `4)  # oracle: pinned constant asserted by this scenario`
- Patch the native facade without a text conversion
   - Expected: driver.pwrite(handle, 1, [0xfeu8, 0x00u8]).unwrap() equals `2)  # oracle: pinned constant asserted by this scenario`
   - Expected: driver.pread(handle, 1, out).unwrap() equals `3)  # oracle: pinned constant asserted by this scenario`
   - Expected: out[0] equals `0xfeu8`
   - Expected: out[1] equals `0x00u8`
   - Expected: out[2] equals `0x7fu8`
   - Expected: out[3] equals `0xaau8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Verify: uses byte-exact pread and pwrite at arbitrary valid offsets")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val (driver, handle) = open_native_positioned_fixture(
    "nvfs-native-positioned", "/native-positioned.bin")
val seed: [u8] = [0x00u8, 0xffu8, 0x80u8, 0x7fu8]
expect(driver.pwrite(handle, 0, seed).unwrap()).to_equal(4)  # oracle: pinned constant asserted by this scenario

step("Patch the native facade without a text conversion")
expect(driver.pwrite(handle, 1, [0xfeu8, 0x00u8]).unwrap()).to_equal(2)  # oracle: pinned constant asserted by this scenario
var out: [u8] = [0xaau8, 0xaau8, 0xaau8, 0xaau8, 0xaau8]
expect(driver.pread(handle, 1, out).unwrap()).to_equal(3)  # oracle: pinned constant asserted by this scenario
expect(out[0]).to_equal(0xfeu8)
expect(out[1]).to_equal(0x00u8)
expect(out[2]).to_equal(0x7fu8)
expect(out[3]).to_equal(0xaau8)
```

</details>

#### keeps compatibility write offset-zero-only while pwrite is positioned

- Verify: keeps compatibility write offset-zero-only while pwrite is positioned
   - Expected: driver.write(handle, 0, [0x41u8, 0x42u8]).unwrap() equals `2)  # oracle: pinned constant asserted by this scenario`
- Keep ordinary write policy separate from positioned pwrite
   - Expected: driver.pwrite(handle, 1, [0x43u8]).unwrap() equals `1)  # oracle: pinned constant asserted by this scenario`
   - Expected: driver.pread(handle, 0, out).unwrap() equals `2)  # oracle: pinned constant asserted by this scenario`
   - Expected: out equals `[0x41u8, 0x43u8]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SQ-021
step("Verify: keeps compatibility write offset-zero-only while pwrite is positioned")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val (driver, handle) = open_native_positioned_fixture(
    "nvfs-native-write-policy", "/native-write-policy.bin")
expect(driver.write(handle, 0, [0x41u8, 0x42u8]).unwrap()).to_equal(2)  # oracle: pinned constant asserted by this scenario

step("Keep ordinary write policy separate from positioned pwrite")
expect(driver.write(
    handle, 1, [0x99u8]).unwrap_err()).to_equal(FsError.Unsupported)
expect(driver.pwrite(handle, 1, [0x43u8]).unwrap()).to_equal(1)  # oracle: pinned constant asserted by this scenario
var out: [u8] = [0u8, 0u8]
expect(driver.pread(handle, 0, out).unwrap()).to_equal(2)  # oracle: pinned constant asserted by this scenario
expect(out).to_equal([0x41u8, 0x43u8])
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

- Canonical SPipe generation for source `0c16b02f922bd86627b75e5544ee3b69bf94b609f6d446d9003b328d798a9ee3`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `0c16b02f922bd86627b75e5544ee3b69bf94b609f6d446d9003b328d798a9ee3`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `0c16b02f922bd86627b75e5544ee3b69bf94b609f6d446d9003b328d798a9ee3`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/02_integration/storage/nvfs/nvfs_positioned_bytes_spec.spl
mirror: doc/06_spec/02_integration/storage/nvfs/nvfs_positioned_bytes_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/02_integration/storage/nvfs/nvfs_positioned_bytes_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/02_integration/storage/nvfs/nvfs_positioned_bytes_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/02_integration/storage/nvfs/nvfs_positioned_bytes_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, traceability, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
