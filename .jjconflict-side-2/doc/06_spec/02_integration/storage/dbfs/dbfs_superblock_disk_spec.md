# Dbfs Superblock Disk Specification

> 1. var dev =  make device

<!-- sdn-diagram:id=dbfs_superblock_disk_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=dbfs_superblock_disk_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

dbfs_superblock_disk_spec -> std
dbfs_superblock_disk_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=dbfs_superblock_disk_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Dbfs Superblock Disk Specification

## Scenarios

### DBFS superblock — blank disk

#### probe returns false on a blank disk

1. var dev =  make device

2. dbfs superblock set device
   - Expected: found is false


<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var dev = _make_device("blank")
dbfs_superblock_set_device(dev)
val found = dbfs_superblock_probe_disk()
expect(found).to_equal(false)
```

</details>

### DBFS superblock — format and probe

#### format returns true

1. var dev =  make device

2. dbfs superblock set device
   - Expected: ok is true


<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var dev = _make_device("format")
dbfs_superblock_set_device(dev)
val ok = dbfs_superblock_format_disk(0xAAAABBBBCCCCDDDDu64, 0x1111222233334444u64)
expect(ok).to_equal(true)
```

</details>

#### probe returns true after format

1. var dev =  make device

2. dbfs superblock set device
   - Expected: fmt_ok is true
   - Expected: found is true


<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. var dev =  make device

2. dbfs superblock set device
   - Expected: fmt_ok is true
   - Expected: sb.magic equals `DBFS_MAGIC`
   - Expected: sb.version equals `DBFS_VERSION`


<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. var dev =  make device

2. dbfs superblock set device
   - Expected: fmt_ok is true
   - Expected: sb.uuid_hi equals `uuid_hi`
   - Expected: sb.uuid_lo equals `uuid_lo`


<details>
<summary>Executable SPipe</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. var dev =  make device

2. dbfs superblock set device
   - Expected: fmt_ok is true
   - Expected: sb.mount_generation equals `1u64`


<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var dev = _make_device("readback_gen")
dbfs_superblock_set_device(dev)
val fmt_ok = dbfs_superblock_format_disk(1u64, 2u64)
expect(fmt_ok).to_equal(true)
val sb = dbfs_superblock_read_from_disk()
expect(sb.mount_generation).to_equal(1u64)
```

</details>

#### read-back valid field is true

1. var dev =  make device

2. dbfs superblock set device
   - Expected: fmt_ok is true
   - Expected: sb.valid is true


<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. var dev =  make device

2. nvfs superblock set device
   - Expected: nvfs_ok is true

3. dbfs superblock set device
   - Expected: dbfs_ok is true
   - Expected: nvfs_found is true
   - Expected: dbfs_found is true


<details>
<summary>Executable SPipe</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
| Source | `test/02_integration/storage/dbfs/dbfs_superblock_disk_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
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
