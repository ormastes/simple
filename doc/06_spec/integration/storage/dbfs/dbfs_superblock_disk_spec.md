# Dbfs Superblock Disk Specification

> Tests covering DBFS superblock — blank disk, DBFS superblock — format and probe, DBFS superblock — read-back fields, NVFS and DBFS coexistence.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Dbfs Superblock Disk Specification

## Scenarios

### DBFS superblock — blank disk

#### probe returns false on a blank disk

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- probe returns false on a blank disk
   - Expected: found is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("probe returns false on a blank disk")
var dev = _make_device("blank")
dbfs_superblock_set_device(dev)
val found = dbfs_superblock_probe_disk()
expect(found).to_equal(false)
```

</details>

### DBFS superblock — format and probe

#### format returns true

- format returns true
   - Expected: ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("format returns true")
var dev = _make_device("format")
dbfs_superblock_set_device(dev)
val ok = dbfs_superblock_format_disk(0xAAAABBBBCCCCDDDDu64, 0x1111222233334444u64)
expect(ok).to_equal(true)
```

</details>

#### probe returns true after format

- probe returns true after format
   - Expected: fmt_ok is true
   - Expected: found is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("probe returns true after format")
var dev = _make_device("probe_after_format")
dbfs_superblock_set_device(dev)
val fmt_ok = dbfs_superblock_format_disk(0x0102030405060708u64, 0x0807060504030201u64)
expect(fmt_ok).to_equal(true)
val found = dbfs_superblock_probe_disk()
expect(found).to_equal(true)
```

</details>

### DBFS superblock — read-back fields

#### read-back has correct magic and version

- read-back has correct magic and version
   - Expected: fmt_ok is true
   - Expected: sb.magic equals `DBFS_MAGIC`
   - Expected: sb.version equals `DBFS_VERSION`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("read-back has correct magic and version")
var dev = _make_device("readback_magic")
dbfs_superblock_set_device(dev)
val fmt_ok = dbfs_superblock_format_disk(0xDEADBEEF00000001u64, 0x00000002CAFEBABEu64)
expect(fmt_ok).to_equal(true)
val sb = dbfs_superblock_read_from_disk()
expect(sb.magic).to_equal(DBFS_MAGIC)
expect(sb.version).to_equal(DBFS_VERSION)
```

</details>

#### read-back has correct uuid fields

- read-back has correct uuid fields
   - Expected: fmt_ok is true
   - Expected: sb.uuid_hi equals `uuid_hi`
   - Expected: sb.uuid_lo equals `uuid_lo`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("read-back has correct uuid fields")
var dev = _make_device("readback_uuid")
dbfs_superblock_set_device(dev)
# Use values that fit cleanly in i64 to avoid interpreter u64 arithmetic edge cases
val uuid_hi: u64 = 0xCAFEu64
val uuid_lo: u64 = 0xBABE1234u64
val fmt_ok = dbfs_superblock_format_disk(uuid_hi, uuid_lo)
expect(fmt_ok).to_equal(true)
val sb = dbfs_superblock_read_from_disk()
expect(sb.uuid_hi).to_equal(uuid_hi)
expect(sb.uuid_lo).to_equal(uuid_lo)
```

</details>

#### read-back has mount_generation of 1 after format

- read-back has mount_generation of 1 after format
   - Expected: fmt_ok is true
   - Expected: sb.mount_generation equals `1u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("read-back has mount_generation of 1 after format")
var dev = _make_device("readback_gen")
dbfs_superblock_set_device(dev)
val fmt_ok = dbfs_superblock_format_disk(1u64, 2u64)
expect(fmt_ok).to_equal(true)
val sb = dbfs_superblock_read_from_disk()
expect(sb.mount_generation).to_equal(1u64)
```

</details>

#### read-back valid field is true

- read-back valid field is true
   - Expected: fmt_ok is true
   - Expected: sb.valid is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("read-back valid field is true")
var dev = _make_device("readback_valid")
dbfs_superblock_set_device(dev)
val fmt_ok = dbfs_superblock_format_disk(5u64, 6u64)
expect(fmt_ok).to_equal(true)
val sb = dbfs_superblock_read_from_disk()
expect(sb.valid).to_equal(true)
```

</details>

### NVFS and DBFS coexistence

#### NVFS probe and DBFS probe are both true after formatting both

- NVFS probe and DBFS probe are both true after formatting both
   - Expected: nvfs_ok is true
   - Expected: dbfs_ok is true
   - Expected: nvfs_found is true
   - Expected: dbfs_found is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("NVFS probe and DBFS probe are both true after formatting both")
var dev = _make_device("coexist")
nvfs_superblock_set_device(dev)
val nvfs_ok = nvfs_superblock_format_disk(0xAABBCCDDEEFF0011u64, 0x1100FFEEDDCCBB0Au64)
expect(nvfs_ok).to_equal(true)
dbfs_superblock_set_device(dev)
val dbfs_ok = dbfs_superblock_format_disk(0x1234567890ABCDEFu64, 0xFEDCBA0987654321u64)
expect(dbfs_ok).to_equal(true)
val nvfs_found = nvfs_superblock_probe_disk()
expect(nvfs_found).to_equal(true)
val dbfs_found = dbfs_superblock_probe_disk()
expect(dbfs_found).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/integration/storage/dbfs/dbfs_superblock_disk_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering DBFS superblock — blank disk, DBFS superblock — format and probe, DBFS superblock — read-back fields, NVFS and DBFS coexistence.
- DBFS superblock — blank disk
- DBFS superblock — format and probe
- DBFS superblock — read-back fields
- NVFS and DBFS coexistence

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

- `REQ-SSPEC-INTEGRATION`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `1daecf0fe12840b336434d8fdcfceb8c4a2221af5c4ef8dce46e3388bfbc7101`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `1daecf0fe12840b336434d8fdcfceb8c4a2221af5c4ef8dce46e3388bfbc7101`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `1daecf0fe12840b336434d8fdcfceb8c4a2221af5c4ef8dce46e3388bfbc7101`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/integration/storage/dbfs/dbfs_superblock_disk_spec.spl
mirror: doc/06_spec/integration/storage/dbfs/dbfs_superblock_disk_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/integration/storage/dbfs/dbfs_superblock_disk_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/integration/storage/dbfs/dbfs_superblock_disk_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/integration/storage/dbfs/dbfs_superblock_disk_spec.spl:47:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'probe returns false on a blank disk' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/storage/dbfs/dbfs_superblock_disk_spec.spl:57:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'format returns true' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/storage/dbfs/dbfs_superblock_disk_spec.spl:65:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'probe returns true after format' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
