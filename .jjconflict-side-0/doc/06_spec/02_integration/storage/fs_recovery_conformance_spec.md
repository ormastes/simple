# fs_recovery_conformance_spec

> Purpose: This spec proves portable filesystem recovery and durability matrix.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# fs_recovery_conformance_spec

Purpose: This spec proves portable filesystem recovery and durability matrix.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/02_integration/storage/fs_recovery_conformance_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: This spec proves portable filesystem recovery and durability matrix.
Audience: Maintainers of the Simple integration suite reviewing this behavior.

## Scenarios

### portable filesystem recovery and durability matrix

#### FAT32 publishes sync only through an acknowledged device flush

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- FAT32 publishes sync only through an acknowledged device flush
   - Expected: _bank_flush_count(device.bank_id) equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-FSRECOVERYCONFORMANCE-001
step("FAT32 publishes sync only through an acknowledged device flush")
val device = RecoveryDevice.new(true)
_seed_fat32(device.bank_id)
var core = Fat32Core.new(device)
core.mount().unwrap()
expect(core.durable_flush_supported).to_be(true)
val handle = core.alloc_file_handle(2u32, 0, false).unwrap()
core.sync_durable(handle).unwrap()
expect(_bank_flush_count(device.bank_id)).to_equal(2)
```

</details>

#### FAT32 rejects stale recycled handles and unavailable durability

- FAT32 rejects stale recycled handles and unavailable durability
- FAT32 rejects stale recycled handles and unavailable durability
   - Expected: core.get_open_file(first).unwrap_err() equals `invalid file handle`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("FAT32 rejects stale recycled handles and unavailable durability")
step("FAT32 rejects stale recycled handles and unavailable durability")
val durable_device = RecoveryDevice.new(true)
_seed_fat32(durable_device.bank_id)
var core = Fat32Core.new(durable_device)
core.mount().unwrap()
val first = core.alloc_file_handle(2u32, 0, false).unwrap()
core.close(first).unwrap()
val second = core.alloc_file_handle(2u32, 0, false).unwrap()
expect(second.id).to_be_greater_than(first.id)
expect(core.get_open_file(first).unwrap_err()).to_equal("invalid file handle")

val volatile_device = RecoveryDevice.new(false)
_seed_fat32(volatile_device.bank_id)
var volatile_core = Fat32Core.new(volatile_device)
volatile_core.mount().unwrap()
expect(volatile_core.durable_flush_supported).to_be(false)
```

</details>

#### NVFS reconstructs only the newest checksum-valid committed length

- NVFS reconstructs only the newest checksum-valid committed length
- NVFS reconstructs only the newest checksum-valid committed length
   - Expected: arena_append_impl(arena, [0x41u8], 0) equals `1`
   - Expected: arena_append_impl(arena, [0x42u8], 0) equals `1`
   - Expected: arena_durable_sequence_impl(base) equals `2u64`
   - Expected: arena_durable_len_impl(base) equals `2`
   - Expected: arena_durable_sequence_impl(base) equals `1u64`
   - Expected: arena_durable_len_impl(base) equals `1`
   - Expected: bytes.len() equals `1`
   - Expected: bytes[0] equals `0x41u8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("NVFS reconstructs only the newest checksum-valid committed length")
step("NVFS reconstructs only the newest checksum-valid committed length")
val device = RecoveryDevice.new(true)
nvfs_arena_set_block_device(device)
val base = 8
val arena = arena_create_nvme_impl(0, 4096, base, 16)
expect(arena).to_be_greater_than(0)
expect(arena_append_impl(arena, [0x41u8], 0)).to_equal(1)
expect(arena_fsync_impl(arena)).to_be(true)
expect(arena_append_impl(arena, [0x42u8], 0)).to_equal(1)
expect(arena_fsync_impl(arena)).to_be(true)
expect(arena_durable_sequence_impl(base)).to_equal(2u64)
expect(arena_durable_len_impl(base)).to_equal(2)

# Slot 1 (offset 32) is the second commit. A crash-torn newest slot
# must fall back to the intact first commit.
_bank_corrupt(device.bank_id, base, 32)
expect(arena_durable_sequence_impl(base)).to_equal(1u64)
expect(arena_durable_len_impl(base)).to_equal(1)
val recovered = arena_recover_nvme_impl(0, 4096, base, 16)
expect(recovered).to_be_greater_than(0)
val bytes = arena_readv_impl(recovered, 0, 8)
expect(bytes.len()).to_equal(1)
expect(bytes[0]).to_equal(0x41u8)
```

</details>

#### NVFS rejects fully corrupt and capacity-incompatible recovery

- NVFS rejects fully corrupt and capacity-incompatible recovery
- NVFS rejects fully corrupt and capacity-incompatible recovery
   - Expected: arena_append_impl(arena, [0x11u8, 0x22u8], 0) equals `2`
   - Expected: arena_recover_nvme_impl(0, 4096, base, 1) equals `-1`
   - Expected: arena_durable_len_impl(base) equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("NVFS rejects fully corrupt and capacity-incompatible recovery")
step("NVFS rejects fully corrupt and capacity-incompatible recovery")
val device = RecoveryDevice.new(true)
nvfs_arena_set_block_device(device)
val base = 40
val arena = arena_create_nvme_impl(0, 4096, base, 16)
expect(arena_append_impl(arena, [0x11u8, 0x22u8], 0)).to_equal(2)
expect(arena_fsync_impl(arena)).to_be(true)
expect(arena_recover_nvme_impl(0, 4096, base, 1)).to_equal(-1)
_bank_corrupt(device.bank_id, base, 0)
expect(arena_durable_len_impl(base)).to_equal(-1)
```

</details>

#### NVFS refuses a commit when the device owner rejects flush

- NVFS refuses a commit when the device owner rejects flush
- NVFS refuses a commit when the device owner rejects flush
   - Expected: arena_append_impl(arena, [0x7Fu8], 0) equals `1`
   - Expected: arena_durable_len_impl(base) equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("NVFS refuses a commit when the device owner rejects flush")
step("NVFS refuses a commit when the device owner rejects flush")
val device = RecoveryDevice.new(false)
nvfs_arena_set_block_device(device)
val base = 64
val arena = arena_create_nvme_impl(0, 4096, base, 8)
expect(arena_append_impl(arena, [0x7Fu8], 0)).to_equal(1)
expect(arena_fsync_impl(arena)).to_be(false)
expect(arena_durable_len_impl(base)).to_equal(-1)
```

</details>

#### NVFS-POSIX preserves portable names and fails closed on sync

- NVFS-POSIX preserves portable names and fails closed on sync
- NVFS-POSIX preserves portable names and fails closed on sync
   - Expected: driver.write(handle, 0, [0x61u8, 0x62u8]) equals `2`
   - Expected: driver.fsync(handle).unwrap_err() equals `FsError.Unsupported`
   - Expected: driver.read(reopened, 0, read_buf) equals `2`
   - Expected: driver.open_path(Path(raw: "portable/../escape"), OpenFlags.read_only()).unwrap_err() equals `FsError.InvalidArg`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("NVFS-POSIX preserves portable names and fails closed on sync")
step("NVFS-POSIX preserves portable names and fails closed on sync")
var driver = NvfsPosixDriver.new("nvfs-posix")
val handle = driver.open_path(Path(raw: "portable/name"), OpenFlags.create_write()).unwrap()
expect(driver.write(handle, 0, [0x61u8, 0x62u8])).to_equal(2)
expect(driver.fsync(handle).unwrap_err()).to_equal(FsError.Unsupported)
driver.close_handle(handle).unwrap()
val reopened = driver.open_path(Path(raw: "portable/name"), OpenFlags.read_only()).unwrap()
var read_buf = _zeros(2)
expect(driver.read(reopened, 0, read_buf)).to_equal(2)
expect(driver.open_path(Path(raw: "portable/../escape"), OpenFlags.read_only()).unwrap_err()).to_equal(FsError.InvalidArg)
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

- `REQ-SSPEC-INTEGRATION`
- `REQ-FSRECOVERYCONFORMANCE-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `1acf2de81c77bba5188ff62c42f2ea80a348606a6af8d13f82c22167be02180e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `1acf2de81c77bba5188ff62c42f2ea80a348606a6af8d13f82c22167be02180e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `1acf2de81c77bba5188ff62c42f2ea80a348606a6af8d13f82c22167be02180e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/02_integration/storage/fs_recovery_conformance_spec.spl
mirror: doc/06_spec/02_integration/storage/fs_recovery_conformance_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/02_integration/storage/fs_recovery_conformance_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/02_integration/storage/fs_recovery_conformance_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/02_integration/storage/fs_recovery_conformance_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 13 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/02_integration/storage/fs_recovery_conformance_spec.spl:147:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'FAT32 publishes sync only through an acknowledged device flush' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/storage/fs_recovery_conformance_spec.spl:159:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'FAT32 rejects stale recycled handles and unavailable durability' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/storage/fs_recovery_conformance_spec.spl:179:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'NVFS reconstructs only the newest checksum-valid committed length' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
