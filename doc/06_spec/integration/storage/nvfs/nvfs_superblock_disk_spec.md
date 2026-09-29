# Nvfs Superblock Disk Specification

> Tests covering NVFS superblock disk I/O.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Nvfs Superblock Disk Specification

## Scenarios

### NVFS superblock disk I/O

#### device registration works

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- device registration works
   - Expected: nvfs_superblock_has_device() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("device registration works")
var dev = _make_device()
nvfs_superblock_set_device(dev)
expect(nvfs_superblock_has_device()).to_equal(true)
```

</details>

#### probe returns false on blank disk

- probe returns false on blank disk
   - Expected: found is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("probe returns false on blank disk")
var dev = _make_device()
nvfs_superblock_set_device(dev)
val found = nvfs_superblock_probe_disk()
expect(found).to_equal(false)
```

</details>

#### format returns true on valid device

- format returns true on valid device
   - Expected: ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("format returns true on valid device")
var dev = _make_device()
nvfs_superblock_set_device(dev)
val ok = nvfs_superblock_format_disk(0x1234u64, 0x5678u64)
expect(ok).to_equal(true)
```

</details>

#### raw sector write and read round-trips

- raw sector write and read round-trips
   - Expected: w is true
   - Expected: rd.len() >= 512 is true
   - Expected: rd[0] equals `0xAA`
   - Expected: rd[1] equals `0xBB`
   - Expected: rd[511] equals `0xFF`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("raw sector write and read round-trips")
var dev = _make_device()
nvfs_superblock_set_device(dev)
var buf = rt_bytes_alloc(512)
buf[0] = 0xAAu8
buf[1] = 0xBBu8
buf[511] = 0xFFu8
val w = nvfs_raw_write_sector(0u64, buf)
expect(w).to_equal(true)
val rd = nvfs_raw_read_sector(0u64)
expect(rd.len() >= 512).to_equal(true)
expect(rd[0]).to_equal(0xAA)
expect(rd[1]).to_equal(0xBB)
expect(rd[511]).to_equal(0xFF)
```

</details>

#### probe returns true after format

- probe returns true after format
   - Expected: ok is true
   - Expected: found is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("probe returns true after format")
var dev = _make_device()
nvfs_superblock_set_device(dev)
val ok = nvfs_superblock_format_disk(0xAAAAu64, 0xBBBBu64)
expect(ok).to_equal(true)
val found = nvfs_superblock_probe_disk()
expect(found).to_equal(true)
```

</details>

#### read-back after format has correct fields

- read-back after format has correct fields
   - Expected: ok is true
   - Expected: sb.valid is true
   - Expected: sb.magic equals `NVFS_MAGIC`
   - Expected: sb.version equals `NVFS_VERSION`
   - Expected: sb.uuid_hi equals `0x1111u64`
   - Expected: sb.uuid_lo equals `0x2222u64`
   - Expected: sb.mount_generation equals `1u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("read-back after format has correct fields")
var dev = _make_device()
nvfs_superblock_set_device(dev)
val ok = nvfs_superblock_format_disk(0x1111u64, 0x2222u64)
expect(ok).to_equal(true)
val sb = nvfs_superblock_read_from_disk()
expect(sb.valid).to_equal(true)
expect(sb.magic).to_equal(NVFS_MAGIC)
expect(sb.version).to_equal(NVFS_VERSION)
expect(sb.uuid_hi).to_equal(0x1111u64)
expect(sb.uuid_lo).to_equal(0x2222u64)
expect(sb.mount_generation).to_equal(1u64)
```

</details>

#### rejects a corrupt replica and reconstructs from the intact peer

- rejects a corrupt replica and reconstructs from the intact peer
   - Expected: recovered.replica_id equals `1u8`
   - Expected: recovered.uuid_hi equals `0x3333u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("rejects a corrupt replica and reconstructs from the intact peer")
var dev = _make_device()
nvfs_superblock_set_device(dev)
expect(nvfs_superblock_format_disk(0x3333u64, 0x4444u64)).to_be(true)
var replica_a = nvfs_raw_read_sector(0u64)
replica_a[8] = replica_a[8] ^ 0x5Au8
expect(nvfs_raw_write_sector(0u64, replica_a)).to_be(true)
val recovered = nvfs_superblock_read_from_disk()
expect(recovered.valid).to_be(true)
expect(recovered.replica_id).to_equal(1u8)
expect(recovered.uuid_hi).to_equal(0x3333u64)
```

</details>

#### fails closed when both replicas are corrupt

- fails closed when both replicas are corrupt


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("fails closed when both replicas are corrupt")
var dev = _make_device()
nvfs_superblock_set_device(dev)
expect(nvfs_superblock_format_disk(0x5555u64, 0x6666u64)).to_be(true)
var replica_a = nvfs_raw_read_sector(0u64)
var replica_b = nvfs_raw_read_sector(1u64)
replica_a[16] = replica_a[16] ^ 0x33u8
replica_b[16] = replica_b[16] ^ 0x77u8
expect(nvfs_raw_write_sector(0u64, replica_a)).to_be(true)
expect(nvfs_raw_write_sector(1u64, replica_b)).to_be(true)
expect(nvfs_superblock_probe_disk()).to_be(false)
expect(nvfs_superblock_read_from_disk().valid).to_be(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/integration/storage/nvfs/nvfs_superblock_disk_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering NVFS superblock disk I/O.
- NVFS superblock disk I/O

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

- Canonical SPipe generation for source `29cef573a18eb037f1fc83e965c00e8a1d2a04f477ecdea006b695e6d24c58a9`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `29cef573a18eb037f1fc83e965c00e8a1d2a04f477ecdea006b695e6d24c58a9`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `29cef573a18eb037f1fc83e965c00e8a1d2a04f477ecdea006b695e6d24c58a9`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/integration/storage/nvfs/nvfs_superblock_disk_spec.spl
mirror: doc/06_spec/integration/storage/nvfs/nvfs_superblock_disk_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/integration/storage/nvfs/nvfs_superblock_disk_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/integration/storage/nvfs/nvfs_superblock_disk_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/integration/storage/nvfs/nvfs_superblock_disk_spec.spl:38:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'device registration works' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/storage/nvfs/nvfs_superblock_disk_spec.spl:45:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'probe returns false on blank disk' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/storage/nvfs/nvfs_superblock_disk_spec.spl:53:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'format returns true on valid device' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
