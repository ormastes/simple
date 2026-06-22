# mem_block_device_spec

> MemBlockDevice Specification

<!-- sdn-diagram:id=mem_block_device_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=mem_block_device_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

mem_block_device_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=mem_block_device_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# mem_block_device_spec

MemBlockDevice Specification

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/02_integration/storage/dbfs/mem_block_device_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

MemBlockDevice Specification

Verifies MemBlockDevice implements BlockDevice with in-memory sector storage:
  new, sector_size, read_sector, write_sector round-trip, bytes, write_to_file

## Scenarios

### MemBlockDevice — construction

#### AC-2: new creates device with correct sector_count

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Arrange / Act
val dev = MemBlockDevice.new(128u64, 512u32)
# Assert — sector_count accessor (fails until impl exists)
expect(dev.sector_count()).to_equal(128u64)
```

</details>

#### AC-2: new creates device with correct sector_size

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dev = MemBlockDevice.new(64u64, 512u32)
expect(dev.sector_size()).to_equal(512u32)
```

</details>

#### AC-2: bytes() length equals sector_count * sector_size

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dev = MemBlockDevice.new(4u64, 512u32)
val b = dev.bytes()
expect(b.len()).to_equal(2048)
```

</details>

### MemBlockDevice — read_sector / write_sector round-trip

#### AC-2: write_sector then read_sector preserves all bytes

1. var sector = dev read sector
   - Expected: ok.is_ok() is true
   - Expected: back[0] equals `0xDBu8`
   - Expected: back[511] equals `0xA5u8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dev = MemBlockDevice.new(8u64, 512u32)
var sector = dev.read_sector(0u64).unwrap()
# Write a known pattern
sector[0] = 0xDBu8
sector[1] = 0xFSu8
sector[511] = 0xA5u8
val ok = dev.write_sector(0u64, sector)
expect(ok.is_ok()).to_equal(true)
val back = dev.read_sector(0u64).unwrap()
expect(back[0]).to_equal(0xDBu8)
expect(back[511]).to_equal(0xA5u8)
```

</details>

#### AC-2: write to sector 3 does not corrupt sector 0

1. var s0 = dev read sector
2. var s3 = dev read sector
   - Expected: check0[0] equals `0x11u8`
   - Expected: check3[0] equals `0x22u8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dev = MemBlockDevice.new(8u64, 512u32)
var s0 = dev.read_sector(0u64).unwrap()
s0[0] = 0x11u8
val _ = dev.write_sector(0u64, s0)
var s3 = dev.read_sector(3u64).unwrap()
s3[0] = 0x22u8
val _ = dev.write_sector(3u64, s3)
val check0 = dev.read_sector(0u64).unwrap()
expect(check0[0]).to_equal(0x11u8)
val check3 = dev.read_sector(3u64).unwrap()
expect(check3[0]).to_equal(0x22u8)
```

</details>

#### AC-2: read_sector out of range returns error

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dev = MemBlockDevice.new(4u64, 512u32)
val result = dev.read_sector(99u64)
expect(result.is_ok()).to_equal(false)
```

</details>

### MemBlockDevice — write_to_file

#### AC-2: write_to_file creates file at the given path

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dev = MemBlockDevice.new(4u64, 512u32)
val path = "/tmp/mem_block_device_spec_test.img"
val result = dev.write_to_file(path)
expect(result.is_ok()).to_equal(true)
expect(rt_file_exists(path)).to_equal(true)
```

</details>

#### AC-2: write_to_file produces file of correct size

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dev = MemBlockDevice.new(4u64, 512u32)
val path = "/tmp/mem_block_device_spec_size_test.img"
val _ = dev.write_to_file(path)
expect(rt_file_size(path)).to_equal(2048)
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
