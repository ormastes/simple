# nvfs_no_regression_spec

> Purpose: NvfsDriver mounts and exposes the root inode

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# nvfs_no_regression_spec

Purpose: NvfsDriver mounts and exposes the root inode

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/02_integration/storage/dbfs/nvfs_no_regression_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: NvfsDriver mounts and exposes the root inode
Audience: compiler and tooling engineers who maintain this spec

NVFS No-Regression Specification

Verifies the live NVFS driver surfaces still work after the blob-backend refactor:
  - native NvfsDriver open/read/write/stat
  - Posix shim open/pwrite/ftruncate/stat

## Scenarios

### NVFS no-regression — NvfsDriver

#### NvfsDriver mounts and exposes the root inode

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- NvfsDriver mounts and exposes the root inode
- Verify: NvfsDriver mounts and exposes the root inode
   - Expected: root.id equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("NvfsDriver mounts and exposes the root inode")
step("Verify: NvfsDriver mounts and exposes the root inode")
# @req: REQ-STORAGE-NvfsNoRegr-001
val d = make_nvfs()
val root = d.root().unwrap()
expect(root.id).to_equal(1)  # oracle: value fixed by the spec contract
```

</details>

#### NvfsDriver open + write + read round-trips bytes

- NvfsDriver open + write + read round-trips bytes
- Verify: NvfsDriver open + write + read round-trips bytes
   - Expected: n equals `7`
   - Expected: got[0] equals `110`
   - Expected: got[6] equals `107`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("NvfsDriver open + write + read round-trips bytes")
step("Verify: NvfsDriver open + write + read round-trips bytes")
# @req: REQ-STORAGE-NvfsNoRegr-001
val d = make_nvfs()
val fh = d.open(Path(raw: "/nvfs_reg.bin"), OpenFlags.create_write()).unwrap()
val payload: [u8] = [110, 118, 102, 115, 45, 111, 107]
d.write(fh, 0, payload).unwrap()
var got: [u8] = [0, 0, 0, 0, 0, 0, 0]
val n = d.read(fh, 0, got).unwrap()
expect(n).to_equal(7)  # oracle: value fixed by the spec contract
expect(got[0]).to_equal(110)  # oracle: value fixed by the spec contract
expect(got[6]).to_equal(107)  # oracle: value fixed by the spec contract
```

</details>

#### NvfsDriver stat returns correct size after write

- NvfsDriver stat returns correct size after write
- Verify: NvfsDriver stat returns correct size after write
   - Expected: stat.size equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("NvfsDriver stat returns correct size after write")
step("Verify: NvfsDriver stat returns correct size after write")
# @req: REQ-STORAGE-NvfsNoRegr-001
val d = make_nvfs()
val fh = d.open(Path(raw: "/size_test.bin"), OpenFlags.create_write()).unwrap()
val payload: [u8] = [49, 50, 51, 52, 53]
d.write(fh, 0, payload).unwrap()
d.close(fh).unwrap()
val stat = d.stat(Path(raw: "/size_test.bin")).unwrap()
expect(stat.size).to_equal(5)  # oracle: value fixed by the spec contract
```

</details>

#### NvfsDriver pwrite updates the requested range without moving data

- NvfsDriver pwrite updates the requested range without moving data
- Verify: NvfsDriver pwrite updates the requested range without moving data
   - Expected: d.pwrite(fh, 1, patch).unwrap() equals `1`
   - Expected: d.pread(fh, 0, got).unwrap() equals `4`
   - Expected: got equals `[1u8, 9u8, 3u8, 4u8]`
   - Expected: d.fstat(fh).unwrap().size equals `4u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("NvfsDriver pwrite updates the requested range without moving data")
step("Verify: NvfsDriver pwrite updates the requested range without moving data")
# @req: REQ-STORAGE-NvfsNoRegr-001
val d = make_nvfs()
val fh = d.open(Path(raw: "/append_only.bin"), OpenFlags.create_write()).unwrap()
val payload: [u8] = [1, 2, 3, 4]
d.write(fh, 0, payload).unwrap()
val patch: [u8] = [9]
expect(d.pwrite(fh, 1, patch).unwrap()).to_equal(1)
var got: [u8] = [0, 0, 0, 0]
expect(d.pread(fh, 0, got).unwrap()).to_equal(4)
expect(got).to_equal([1u8, 9u8, 3u8, 4u8])
expect(d.fstat(fh).unwrap().size).to_equal(4u64)
```

</details>

#### NvfsDriver rejects negative and overflowing positioned ranges

- NvfsDriver rejects negative and overflowing positioned ranges
   - Expected: d.pread(fh, -1, one).unwrap_err() equals `FsError.InvalidArg`
   - Expected: d.pwrite(fh, 9223372036854775807, [1u8]).unwrap_err() equals `FsError.InvalidArg`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("NvfsDriver rejects negative and overflowing positioned ranges")
val d = make_nvfs()
val fh = d.open(Path(raw: "/range.bin"), OpenFlags.create_write()).unwrap()
var one: [u8] = [0]
expect(d.pread(fh, -1, one).unwrap_err()).to_equal(FsError.InvalidArg)
expect(d.pwrite(fh, 9223372036854775807, [1u8]).unwrap_err()).to_equal(FsError.InvalidArg)
```

</details>

### NVFS no-regression — NvfsPosixDriver

#### NvfsPosixDriver mounts and exposes the root inode

- NvfsPosixDriver mounts and exposes the root inode
- Verify: NvfsPosixDriver mounts and exposes the root inode
   - Expected: root.id equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("NvfsPosixDriver mounts and exposes the root inode")
step("Verify: NvfsPosixDriver mounts and exposes the root inode")
# @req: REQ-STORAGE-NvfsNoRegr-001
val d = make_nvfs_posix()
val root = d.root().unwrap()
expect(root.id).to_equal(1)  # oracle: value fixed by the spec contract
```

</details>

#### NvfsPosixDriver open + write + read round-trips bytes

- NvfsPosixDriver open + write + read round-trips bytes
- Verify: NvfsPosixDriver open + write + read round-trips bytes
   - Expected: n equals `8`
   - Expected: got[0] equals `112`
   - Expected: got[7] equals `107`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("NvfsPosixDriver open + write + read round-trips bytes")
step("Verify: NvfsPosixDriver open + write + read round-trips bytes")
# @req: REQ-STORAGE-NvfsNoRegr-001
val d = make_nvfs_posix()
val fh = d.open(Path(raw: "/posix_reg.txt"), OpenFlags.create_write().with_append()).unwrap()
val payload: [u8] = [112, 111, 115, 105, 120, 45, 111, 107]
d.write(fh, 0, payload).unwrap()
var got: [u8] = [0, 0, 0, 0, 0, 0, 0, 0]
val n = d.read(fh, 0, got).unwrap()
expect(n).to_equal(8)  # oracle: value fixed by the spec contract
expect(got[0]).to_equal(112)  # oracle: value fixed by the spec contract
expect(got[7]).to_equal(107)  # oracle: value fixed by the spec contract
```

</details>

#### NvfsPosixDriver pwrite updates bytes in place

- NvfsPosixDriver pwrite updates bytes in place
- Verify: NvfsPosixDriver pwrite updates bytes in place
   - Expected: n equals `4`
   - Expected: got[0] equals `65`
   - Expected: got[2] equals `66`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("NvfsPosixDriver pwrite updates bytes in place")
step("Verify: NvfsPosixDriver pwrite updates bytes in place")
# @req: REQ-STORAGE-NvfsNoRegr-001
val d = make_nvfs_posix()
val fh = d.open(Path(raw: "/rewrite.txt"), OpenFlags.create_write().with_append()).unwrap()
val seed: [u8] = [65, 65, 65, 65]
d.write(fh, 0, seed).unwrap()
val patch: [u8] = [66, 66]
d.pwrite(fh, 2, patch).unwrap()
var got: [u8] = [0, 0, 0, 0]
val n = d.pread(fh, 0, got).unwrap()
expect(n).to_equal(4)  # oracle: value fixed by the spec contract
expect(got[0]).to_equal(65)  # oracle: value fixed by the spec contract
expect(got[2]).to_equal(66)  # oracle: value fixed by the spec contract
```

</details>

#### NvfsPosixDriver stat returns updated size after ftruncate

- NvfsPosixDriver stat returns updated size after ftruncate
- Verify: NvfsPosixDriver stat returns updated size after ftruncate
   - Expected: stat.size equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("NvfsPosixDriver stat returns updated size after ftruncate")
step("Verify: NvfsPosixDriver stat returns updated size after ftruncate")
# @req: REQ-STORAGE-NvfsNoRegr-001
val d = make_nvfs_posix()
val fh = d.open(Path(raw: "/file.txt"), OpenFlags.create_write().with_append()).unwrap()
val payload: [u8] = [1, 2, 3, 4]
d.write(fh, 0, payload).unwrap()
d.ftruncate(fh, 10).unwrap()
val stat = d.fstat(fh).unwrap()
expect(stat.size).to_equal(10)  # oracle: value fixed by the spec contract
```

</details>

#### NvfsPosixDriver preserves sparse positioned-write semantics

- NvfsPosixDriver preserves sparse positioned-write semantics
   - Expected: d.pwrite(fh, 3, [0xAAu8]).unwrap() equals `1`
   - Expected: d.pread(fh, 0, got).unwrap() equals `4`
   - Expected: got equals `[0u8, 0u8, 0u8, 0xAAu8]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("NvfsPosixDriver preserves sparse positioned-write semantics")
val d = make_nvfs_posix()
val fh = d.open(Path(raw: "/sparse.bin"), OpenFlags.write_only().with_create()).unwrap()
expect(d.pwrite(fh, 3, [0xAAu8]).unwrap()).to_equal(1)
var got: [u8] = [9, 9, 9, 9]
expect(d.pread(fh, 0, got).unwrap()).to_equal(4)
expect(got).to_equal([0u8, 0u8, 0u8, 0xAAu8])
```

</details>

#### NvfsPosixDriver rejects negative and overflowing positioned ranges

- NvfsPosixDriver rejects negative and overflowing positioned ranges
   - Expected: d.pread(fh, -1, one).unwrap_err() equals `FsError.InvalidArg`
   - Expected: d.pwrite(fh, 9223372036854775807, [1u8]).unwrap_err() equals `FsError.InvalidArg`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("NvfsPosixDriver rejects negative and overflowing positioned ranges")
val d = make_nvfs_posix()
val fh = d.open(Path(raw: "/range-posix.bin"), OpenFlags.write_only().with_create()).unwrap()
var one: [u8] = [0]
expect(d.pread(fh, -1, one).unwrap_err()).to_equal(FsError.InvalidArg)
expect(d.pwrite(fh, 9223372036854775807, [1u8]).unwrap_err()).to_equal(FsError.InvalidArg)
```

</details>

#### opens an existing NVFS file for execution without creating misses

- opens an existing NVFS file for execution without creating misses
   - Expected: binding.backend_name equals `nvfs-posix-regression`
   - Expected: binding.size equals `4`
   - Expected: table.open_for_execute("/nvfs/missing.smf", ExecuteTrust.Trusted).is_err() is true
   - Expected: table.stat("/nvfs/missing.smf").is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("opens an existing NVFS file for execution without creating misses")
var table = MountTable.new()
table.mount("/nvfs", DriverInstance.NvfsPosix(make_nvfs_posix()), MountOptions.default()).unwrap()
val created = table.open("/nvfs/program.smf", OpenFlags.create_write()).unwrap()
table.write(created, "SMF1").unwrap()
table.close(created).unwrap()
val binding = table.open_for_execute("/nvfs/program.smf", ExecuteTrust.Trusted).unwrap()
expect(binding.backend_name).to_equal("nvfs-posix-regression")
expect(binding.size).to_equal(4)
table.close(binding.file_handle).unwrap()
expect(table.open_for_execute("/nvfs/missing.smf", ExecuteTrust.Trusted).is_err()).to_equal(true)
expect(table.stat("/nvfs/missing.smf").is_err()).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-INTEGRATION`
- `REQ-STORAGE-NvfsNoRegr-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `e4daefbd2f82c9d711a37f7a23c4fe84dba2c90bb91cec58182affbdf9ebc8a5`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e4daefbd2f82c9d711a37f7a23c4fe84dba2c90bb91cec58182affbdf9ebc8a5`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e4daefbd2f82c9d711a37f7a23c4fe84dba2c90bb91cec58182affbdf9ebc8a5`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/02_integration/storage/dbfs/nvfs_no_regression_spec.spl
mirror: doc/06_spec/02_integration/storage/dbfs/nvfs_no_regression_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/02_integration/storage/dbfs/nvfs_no_regression_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/02_integration/storage/dbfs/nvfs_no_regression_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/02_integration/storage/dbfs/nvfs_no_regression_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 5 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/02_integration/storage/dbfs/nvfs_no_regression_spec.spl:44:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'NvfsDriver mounts and exposes the root inode' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/storage/dbfs/nvfs_no_regression_spec.spl:53:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'NvfsDriver open + write + read round-trips bytes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/storage/dbfs/nvfs_no_regression_spec.spl:68:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'NvfsDriver stat returns correct size after write' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
