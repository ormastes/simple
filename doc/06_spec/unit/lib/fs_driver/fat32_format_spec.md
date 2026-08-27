# Fat32 Format Specification

> Tests covering host-neutral authorized FAT32 formatting.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Fat32 Format Specification

## Scenarios

### host-neutral authorized FAT32 formatting

#### plans strict FAT32 geometry without touching media

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- plans strict FAT32 geometry without touching media
   - Expected: plan.reserved_sectors equals `32u32`
   - Expected: plan.fat_count equals `2u32`
   - Expected: plan.root_cluster equals `2u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("plans strict FAT32 geometry without touching media")
val plan = fat32_format_plan(512u32, 70000u64, 1u32).unwrap()
expect(plan.cluster_count).to_be_greater_than(65524u64)
expect(plan.reserved_sectors).to_equal(32u32)
expect(plan.fat_count).to_equal(2u32)
expect(plan.root_cluster).to_equal(2u32)
expect(plan.fat_sectors.to_u64() * 512u64 / 4u64).to_be_greater_than(plan.cluster_count + 1u64)
```

</details>

#### rejects small media and invalid cluster geometry

- rejects small media and invalid cluster geometry
   - Expected: fat32_format_plan(512u32, 4096u64, 1u32).unwrap_err() equals `fat32-format-not-fat32-cluster-count`
   - Expected: fat32_format_plan(512u32, 70000u64, 3u32).unwrap_err() equals `fat32-format-invalid-sectors-per-cluster`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects small media and invalid cluster geometry")
expect(fat32_format_plan(512u32, 4096u64, 1u32).unwrap_err()).to_equal("fat32-format-not-fat32-cluster-count")
expect(fat32_format_plan(512u32, 70000u64, 3u32).unwrap_err()).to_equal("fat32-format-invalid-sectors-per-cluster")
```

</details>

#### requires identity-bound authorization before the first write

- requires identity-bound authorization before the first write
   - Expected: fat32_format(mem, plan, denied, 1u32, "SIMPLEOS").unwrap_err() equals `fat32-format-authorization-required`
   - Expected: first[510] equals `0u8`
   - Expected: first[511] equals `0u8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("requires identity-bound authorization before the first write")
val mem = MemBlockDevice.new(70000u64, 512u32)
val plan = fat32_format_plan(512u32, 70000u64, 1u32).unwrap()
val denied = Fat32FormatAuthorization(approved: false, identity_hash: "", challenge: "")
expect(fat32_format(mem, plan, denied, 1u32, "SIMPLEOS").unwrap_err()).to_equal("fat32-format-authorization-required")
val dev: BlockDevice = mem
val first = dev.read_sector(0u64).unwrap()
expect(first[510]).to_equal(0u8)
expect(first[511]).to_equal(0u8)
```

</details>

#### creates mirrored FAT32 metadata and an allocated empty root cluster

- creates mirrored FAT32 metadata and an allocated empty root cluster
   - Expected: fat32_format(mem, plan, authority, 0x12345678u32, "SIMPLEOS").unwrap() is true
   - Expected: _u16_le(boot, 11) equals `512u32`
   - Expected: boot[13] equals `1u8`
   - Expected: _u16_le(boot, 14) equals `32u32`
   - Expected: boot[16] equals `2u8`
   - Expected: _u32_le(boot, 36) equals `plan.fat_sectors`
   - Expected: _u32_le(boot, 44) equals `2u32`
   - Expected: boot[510] equals `0x55u8`
   - Expected: boot[511] equals `0xaau8`
   - Expected: backup_boot equals `boot`
   - Expected: _u32_le(fsinfo, 0) equals `0x41615252u32`
   - Expected: _u32_le(fsinfo, 484) equals `0x61417272u32`
   - Expected: fat0 equals `fat1`
   - Expected: _u32_le(fat0, 0) equals `0x0ffffff8u32`
   - Expected: _u32_le(fat0, 8) equals `0x0fffffffu32`
   - Expected: root[0] equals `0u8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates mirrored FAT32 metadata and an allocated empty root cluster")
val mem = MemBlockDevice.new(70000u64, 512u32)
val plan = fat32_format_plan(512u32, 70000u64, 1u32).unwrap()
val authority = Fat32FormatAuthorization(approved: true, identity_hash: "sha256:device", challenge: "exact-device-challenge")
expect(fat32_format(mem, plan, authority, 0x12345678u32, "SIMPLEOS").unwrap()).to_equal(true)
val dev: BlockDevice = mem
val boot = dev.read_sector(0u64).unwrap()
expect(_u16_le(boot, 11)).to_equal(512u32)
expect(boot[13]).to_equal(1u8)
expect(_u16_le(boot, 14)).to_equal(32u32)
expect(boot[16]).to_equal(2u8)
expect(_u32_le(boot, 36)).to_equal(plan.fat_sectors)
expect(_u32_le(boot, 44)).to_equal(2u32)
expect(boot[510]).to_equal(0x55u8)
expect(boot[511]).to_equal(0xaau8)
val backup_boot = dev.read_sector(6u64).unwrap()
expect(backup_boot).to_equal(boot)
val fsinfo = dev.read_sector(1u64).unwrap()
expect(_u32_le(fsinfo, 0)).to_equal(0x41615252u32)
expect(_u32_le(fsinfo, 484)).to_equal(0x61417272u32)
val fat0 = dev.read_sector(32u64).unwrap()
val fat1 = dev.read_sector(32u64 + plan.fat_sectors.to_u64()).unwrap()
expect(fat0).to_equal(fat1)
expect(_u32_le(fat0, 0)).to_equal(0x0ffffff8u32)
expect(_u32_le(fat0, 8)).to_equal(0x0fffffffu32)
val root = dev.read_sector(plan.data_start_lba).unwrap()
expect(root[0]).to_equal(0u8)
```

</details>

#### mounts, writes, unmounts, remounts, reads, and lists through the shared FAT32 core

- mounts, writes, unmounts, remounts, reads, and lists through the shared FAT32 core
   - Expected: fat32_format(mem, plan, authority, 0x12345678u32, "SIMPLEOS").is_ok() is true
   - Expected: writer.mount().is_ok() is true
   - Expected: writer.write(handle, payload, payload.len()).unwrap() equals `payload.len()`
   - Expected: writer.close(handle).is_ok() is true
   - Expected: writer.unmount().is_ok() is true
   - Expected: reader.mount().is_ok() is true
   - Expected: entries.len() equals `1`
   - Expected: entries[0].name equals `proof.txt`
   - Expected: reader.read(read_handle, readback, readback.len()).unwrap() equals `payload.len()`
   - Expected: readback equals `payload`


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("mounts, writes, unmounts, remounts, reads, and lists through the shared FAT32 core")
val mem = MemBlockDevice.new(70000u64, 512u32)
val plan = fat32_format_plan(512u32, 70000u64, 1u32).unwrap()
val authority = Fat32FormatAuthorization(approved: true, identity_hash: "sha256:device", challenge: "exact-device-challenge")
expect(fat32_format(mem, plan, authority, 0x12345678u32, "SIMPLEOS").is_ok()).to_equal(true)
var writer = Fat32Core.new(mem)
expect(writer.mount().is_ok()).to_equal(true)
val handle = writer.create_file("/proof.txt").unwrap()
val payload: [u8] = [115u8, 105u8, 109u8, 112u8, 108u8, 101u8, 111u8, 115u8]
expect(writer.write(handle, payload, payload.len()).unwrap()).to_equal(payload.len())
expect(writer.close(handle).is_ok()).to_equal(true)
expect(writer.unmount().is_ok()).to_equal(true)

var reader = Fat32Core.new(mem)
expect(reader.mount().is_ok()).to_equal(true)
val entries = reader.readdir("/").unwrap()
expect(entries.len()).to_equal(1)
expect(entries[0].name).to_equal("proof.txt")
val read_handle = reader.open("/proof.txt").unwrap()
var readback: [u8] = [0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8]
expect(reader.read(read_handle, readback, readback.len()).unwrap()).to_equal(payload.len())
expect(readback).to_equal(payload)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/fs_driver/fat32_format_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering host-neutral authorized FAT32 formatting.
- host-neutral authorized FAT32 formatting

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
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

- Canonical SPipe generation for source `c954de43da71d4e928acd6c6d67524b5ad23db50186264d1e7b3727363ddc809`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `c954de43da71d4e928acd6c6d67524b5ad23db50186264d1e7b3727363ddc809`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `c954de43da71d4e928acd6c6d67524b5ad23db50186264d1e7b3727363ddc809`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/unit/lib/fs_driver/fat32_format_spec.spl
mirror: doc/06_spec/unit/lib/fs_driver/fat32_format_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/fs_driver/fat32_format_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/fs_driver/fat32_format_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/fs_driver/fat32_format_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/lib/fs_driver/fat32_format_spec.spl:21:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'plans strict FAT32 geometry without touching media' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/fs_driver/fat32_format_spec.spl:31:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects small media and invalid cluster geometry' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/fs_driver/fat32_format_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'requires identity-bound authorization before the first write' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
