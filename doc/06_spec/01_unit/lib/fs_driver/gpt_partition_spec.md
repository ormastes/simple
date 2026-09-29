# Gpt Partition Specification

> Tests covering host-neutral GPT partition boundary.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Gpt Partition Specification

## Scenarios

### host-neutral GPT partition boundary

#### matches the standard IEEE CRC32 known-answer value

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- matches the standard IEEE CRC32 known-answer value
   - Expected: gpt_crc32([49u8, 50u8, 51u8, 52u8, 53u8, 54u8, 55u8, 56u8, 57u8]) equals `0xcbf43926u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("matches the standard IEEE CRC32 known-answer value")
expect(gpt_crc32([49u8, 50u8, 51u8, 52u8, 53u8, 54u8, 55u8, 56u8, 57u8])).to_equal(0xcbf43926u32)
```

</details>

#### creates a geometry-only formatting plan without touching a device

- creates a geometry-only formatting plan without touching a device
   - Expected: plan.primary_header_lba equals `1u64`
   - Expected: plan.first_usable_lba equals `34u64`
   - Expected: plan.backup_header_lba equals `4095u64`
   - Expected: plan.last_usable_lba equals `4062u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("creates a geometry-only formatting plan without touching a device")
val plan = gpt_format_plan(512u32, 4096u64, 128u32).unwrap()
expect(plan.primary_header_lba).to_equal(1u64)
expect(plan.first_usable_lba).to_equal(34u64)
expect(plan.backup_header_lba).to_equal(4095u64)
expect(plan.last_usable_lba).to_equal(4062u64)
```

</details>

#### rejects impossible formatting geometry

- rejects impossible formatting geometry
   - Expected: gpt_format_plan(256u32, 4096u64, 128u32).unwrap_err() equals `gpt-format-sector-size-too-small`
   - Expected: gpt_format_plan(512u32, 40u64, 128u32).unwrap_err() equals `gpt-format-device-too-small`
   - Expected: gpt_format_plan(512u32, 4096u64, 129u32).unwrap_err() equals `gpt-format-entry-count-out-of-range`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects impossible formatting geometry")
expect(gpt_format_plan(256u32, 4096u64, 128u32).unwrap_err()).to_equal("gpt-format-sector-size-too-small")
expect(gpt_format_plan(512u32, 40u64, 128u32).unwrap_err()).to_equal("gpt-format-device-too-small")
expect(gpt_format_plan(512u32, 4096u64, 129u32).unwrap_err()).to_equal("gpt-format-entry-count-out-of-range")
```

</details>

#### parses a valid primary table and returns an exact bounded partition

- parses a valid primary table and returns an exact bounded partition
   - Expected: table.partitions.len() equals `1`
   - Expected: part.first_lba equals `34u64`
   - Expected: gpt_partition_sector_count(part).unwrap() equals `30u64`
   - Expected: gpt_partition_window_reason(part, 128u64) equals `ready`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("parses a valid primary table and returns an exact bounded partition")
val table = gpt_read_primary(_valid_gpt_device(), 128u64).unwrap()
expect(table.partitions.len()).to_equal(1)
val part = table.partitions[0]
expect(part.first_lba).to_equal(34u64)
expect(gpt_partition_sector_count(part).unwrap()).to_equal(30u64)
expect(gpt_partition_window_reason(part, 128u64)).to_equal("ready")
```

</details>

#### fails closed when the header CRC or caller lease bound is wrong

- fails closed when the header CRC or caller lease bound is wrong
   - Expected: gpt_read_primary(mem, 128u64).unwrap_err() equals `gpt-header-crc-mismatch`
   - Expected: gpt_read_primary(_valid_gpt_device(), 64u64).unwrap_err() equals `gpt-header-geometry-invalid`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("fails closed when the header CRC or caller lease bound is wrong")
val mem = _valid_gpt_device()
val dev: BlockDevice = mem
var header = dev.read_sector(1u64).unwrap()
header[20] = 1u8
dev.write_sector(1u64, header)
expect(gpt_read_primary(mem, 128u64).unwrap_err()).to_equal("gpt-header-crc-mismatch")
expect(gpt_read_primary(_valid_gpt_device(), 64u64).unwrap_err()).to_equal("gpt-header-geometry-invalid")
```

</details>

#### rejects reversed and out-of-bounds windows before lease creation

- rejects reversed and out-of-bounds windows before lease creation
   - Expected: gpt_partition_sector_count(reversed).unwrap_err() equals `gpt-partition-reversed`
   - Expected: gpt_partition_window_reason(outside, 16u64) equals `gpt-partition-out-of-bounds`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects reversed and out-of-bounds windows before lease creation")
val reversed = GptPartition(index: 1u32, first_lba: 9u64, last_lba: 8u64, type_guid_lo: 1u64, type_guid_hi: 0u64, unique_guid_lo: 0u64, unique_guid_hi: 0u64)
val outside = GptPartition(index: 2u32, first_lba: 8u64, last_lba: 16u64, type_guid_lo: 1u64, type_guid_hi: 0u64, unique_guid_lo: 0u64, unique_guid_hi: 0u64)
expect(gpt_partition_sector_count(reversed).unwrap_err()).to_equal("gpt-partition-reversed")
expect(gpt_partition_window_reason(outside, 16u64)).to_equal("gpt-partition-out-of-bounds")
```

</details>

#### writes and validates mirrored GPT metadata for one aligned partition

- writes and validates mirrored GPT metadata for one aligned partition
   - Expected: created.first_lba equals `2048u64`
   - Expected: created.last_lba equals `plan.last_usable_lba`
   - Expected: mbr[450] equals `0xeeu8`
   - Expected: mbr[510] equals `0x55u8`
   - Expected: mbr[511] equals `0xaau8`
   - Expected: backup[0] equals `0x45u8`
   - Expected: backup[7] equals `0x54u8`
   - Expected: gpt_read_primary(mem, 8192u64).unwrap().partitions.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("writes and validates mirrored GPT metadata for one aligned partition")
val mem = MemBlockDevice.new(8192u64, 512u32)
val plan = gpt_format_plan(512u32, 8192u64, 128u32).unwrap()
val request = GptSinglePartitionRequest(
    first_lba: 2048u64,
    last_lba: plan.last_usable_lba,
    type_guid_lo: 0x11d2f81fc12a7328u64,
    type_guid_hi: 0x3bc93ec9a0004bbau64,
    unique_guid_lo: 0x0123456789abcdefu64,
    unique_guid_hi: 0xfedcba9876543210u64,
    disk_guid_lo: 0x1020304050607080u64,
    disk_guid_hi: 0x90a0b0c0d0e0f001u64
)
val created = gpt_create_single_partition(mem, plan, request).unwrap()
expect(created.first_lba).to_equal(2048u64)
expect(created.last_lba).to_equal(plan.last_usable_lba)
val dev: BlockDevice = mem
val mbr = dev.read_sector(0u64).unwrap()
expect(mbr[450]).to_equal(0xeeu8)
expect(mbr[510]).to_equal(0x55u8)
expect(mbr[511]).to_equal(0xaau8)
val backup = dev.read_sector(plan.backup_header_lba).unwrap()
expect(backup[0]).to_equal(0x45u8)
expect(backup[7]).to_equal(0x54u8)
expect(gpt_read_primary(mem, 8192u64).unwrap().partitions.len()).to_equal(1)
```

</details>

#### rejects destructive GPT geometry that is not 1 MiB aligned

- rejects destructive GPT geometry that is not 1 MiB aligned
   - Expected: gpt_create_single_partition(mem, plan, request).unwrap_err() equals `gpt-create-partition-not-1mib-aligned`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects destructive GPT geometry that is not 1 MiB aligned")
val mem = MemBlockDevice.new(8192u64, 512u32)
val plan = gpt_format_plan(512u32, 8192u64, 128u32).unwrap()
val request = GptSinglePartitionRequest(
    first_lba: 34u64,
    last_lba: plan.last_usable_lba,
    type_guid_lo: 1u64,
    type_guid_hi: 1u64,
    unique_guid_lo: 2u64,
    unique_guid_hi: 2u64,
    disk_guid_lo: 3u64,
    disk_guid_hi: 3u64
)
expect(gpt_create_single_partition(mem, plan, request).unwrap_err()).to_equal("gpt-create-partition-not-1mib-aligned")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/fs_driver/gpt_partition_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering host-neutral GPT partition boundary.
- host-neutral GPT partition boundary

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `d1e8dd4af444ed0398578318b80217c5d4d7f27f7bfa3b33160d37b42d6a77bf`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `d1e8dd4af444ed0398578318b80217c5d4d7f27f7bfa3b33160d37b42d6a77bf`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `d1e8dd4af444ed0398578318b80217c5d4d7f27f7bfa3b33160d37b42d6a77bf`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/lib/fs_driver/gpt_partition_spec.spl
mirror: doc/06_spec/01_unit/lib/fs_driver/gpt_partition_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/fs_driver/gpt_partition_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/fs_driver/gpt_partition_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/fs_driver/gpt_partition_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/fs_driver/gpt_partition_spec.spl:77:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'matches the standard IEEE CRC32 known-answer value' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/fs_driver/gpt_partition_spec.spl:82:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates a geometry-only formatting plan without touching a device' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/fs_driver/gpt_partition_spec.spl:91:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects impossible formatting geometry' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
