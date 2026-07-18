# FAT32 read() — Wave-4c Spec

> Verifies that `Fat32Filesystem.read(dev, handle, buf)`:

<!-- sdn-diagram:id=fat32_read_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=fat32_read_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

fat32_read_spec -> std
fat32_read_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=fat32_read_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# FAT32 read() — Wave-4c Spec

Verifies that `Fat32Filesystem.read(dev, handle, buf)`:

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/kernel/fs/fat32_read_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

**Bug:** fat32_no_cycle_guard_chain_walk_2026-06-11  FINDING-T1
Verifies that `Fat32Filesystem.read(dev, handle, buf)`:
  1. Multi-cluster file: assembles bytes in chain order across clusters.
  2. File smaller than cluster: truncates at file_size, no padding bytes.
  3. Corrupt/cyclic chain: read() returns Err(EIO) and does NOT hang.
  4. Single-cluster file: reads exactly file_size bytes.
  5. Already-at-EOF handle: returns Ok(0) without touching dev.
  6. buf smaller than file: reads only buf.len() bytes.

Geometry used throughout:
  fat_start_sector=32, data_start_sector=64, bytes_per_sector=512,
  sectors_per_cluster=1, data_clusters=100.
  Cluster N → LBA = data_start_sector + (N - 2).
  FAT entry for cluster N: 4-byte little-endian at sector 32 byte-offset N*4.

## Scenarios

### fat32 read() — wave-4c cluster-chain wiring

### single-cluster file

#### reads exactly file_size bytes from a single cluster

- var fat =  zero sector
- fat =  fat put
- var data sec =  fill sector
- var dev = MockReadDev new
- dev = dev with sector
- dev = dev with sector
- var fs =  make fs
- var buf =  make buf
   - Expected: result.is_ok() is true
   - Expected: result.unwrap() equals `10u64`
   - Expected: buf[0] equals `0xAAu8`
   - Expected: buf[9] equals `0xAAu8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# File: cluster 2 → EOC. Content: 0xAA repeated. file_size=10.
var fat = _zero_sector()
fat = _fat_put(fat, 2u32, _eoc())
var data_sec = _fill_sector(0xAAu8)
var dev = MockReadDev.new()
dev = dev.with_sector(_fat_sector_lba(), fat)
dev = dev.with_sector(_cluster_lba(2u32), data_sec)
var fs = _make_fs()
val h = _make_handle(2u32, 10u64)
var buf = _make_buf(10)
val result = fs.read(dev, h, buf)
expect(result.is_ok()).to_equal(true)
expect(result.unwrap()).to_equal(10u64)
expect(buf[0]).to_equal(0xAAu8)
expect(buf[9]).to_equal(0xAAu8)
```

</details>

#### reads up to buf.len() when buf is smaller than file_size

- var fat =  zero sector
- fat =  fat put
- var data sec =  fill sector
- var dev = MockReadDev new
- dev = dev with sector
- dev = dev with sector
- var fs =  make fs
- var buf =  make buf
   - Expected: result.is_ok() is true
   - Expected: result.unwrap() equals `20u64`
   - Expected: buf[ci] equals `0xBBu8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var fat = _zero_sector()
fat = _fat_put(fat, 2u32, _eoc())
var data_sec = _fill_sector(0xBBu8)
var dev = MockReadDev.new()
dev = dev.with_sector(_fat_sector_lba(), fat)
dev = dev.with_sector(_cluster_lba(2u32), data_sec)
var fs = _make_fs()
val h = _make_handle(2u32, 512u64)
var buf = _make_buf(20)
val result = fs.read(dev, h, buf)
expect(result.is_ok()).to_equal(true)
expect(result.unwrap()).to_equal(20u64)
var ci = 0
while ci < 20:
    expect(buf[ci]).to_equal(0xBBu8)
    ci = ci + 1
```

</details>

#### file smaller than cluster — last cluster bytes are NOT returned

- var fat =  zero sector
- fat =  fat put
- var data sec =  zero sector
- var dev = MockReadDev new
- dev = dev with sector
- dev = dev with sector
- var fs =  make fs
- var buf =  make buf
   - Expected: result.is_ok() is true
   - Expected: result.unwrap() equals `3u64`
   - Expected: buf[0] equals `0x11u8`
   - Expected: buf[1] equals `0x22u8`
   - Expected: buf[2] equals `0x33u8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# file_size=3 in a 512-byte cluster — only bytes 0..2 returned.
var fat = _zero_sector()
fat = _fat_put(fat, 2u32, _eoc())
var data_sec = _zero_sector()
data_sec[0] = 0x11u8
data_sec[1] = 0x22u8
data_sec[2] = 0x33u8
data_sec[3] = 0xFFu8   # beyond file_size — must NOT appear in output
var dev = MockReadDev.new()
dev = dev.with_sector(_fat_sector_lba(), fat)
dev = dev.with_sector(_cluster_lba(2u32), data_sec)
var fs = _make_fs()
val h = _make_handle(2u32, 3u64)
var buf = _make_buf(512)
val result = fs.read(dev, h, buf)
expect(result.is_ok()).to_equal(true)
expect(result.unwrap()).to_equal(3u64)
expect(buf[0]).to_equal(0x11u8)
expect(buf[1]).to_equal(0x22u8)
expect(buf[2]).to_equal(0x33u8)
```

</details>

### multi-cluster file

#### two-cluster file assembles bytes in chain order

- var fat =  zero sector
- fat =  fat put
- fat =  fat put
- var sec2 =  fill sector
- var sec3 =  fill sector
- var dev = MockReadDev new
- dev = dev with sector
- dev = dev with sector
- dev = dev with sector
- var fs =  make fs
- var buf =  make buf
   - Expected: result.is_ok() is true
   - Expected: result.unwrap() equals `1024u64`
   - Expected: buf[0] equals `0xAAu8`
   - Expected: buf[511] equals `0xAAu8`
   - Expected: buf[512] equals `0xBBu8`
   - Expected: buf[1023] equals `0xBBu8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Cluster 2 → cluster 3 → EOC. Cluster 2 filled 0xAA, cluster 3 filled 0xBB.
# file_size = 1024 (two full 512-byte clusters).
var fat = _zero_sector()
fat = _fat_put(fat, 2u32, 3u32)
fat = _fat_put(fat, 3u32, _eoc())
var sec2 = _fill_sector(0xAAu8)
var sec3 = _fill_sector(0xBBu8)
var dev = MockReadDev.new()
dev = dev.with_sector(_fat_sector_lba(), fat)
dev = dev.with_sector(_cluster_lba(2u32), sec2)
dev = dev.with_sector(_cluster_lba(3u32), sec3)
var fs = _make_fs()
val h = _make_handle(2u32, 1024u64)
var buf = _make_buf(1024)
val result = fs.read(dev, h, buf)
expect(result.is_ok()).to_equal(true)
expect(result.unwrap()).to_equal(1024u64)
# First 512 bytes from cluster 2 must be 0xAA
expect(buf[0]).to_equal(0xAAu8)
expect(buf[511]).to_equal(0xAAu8)
# Bytes 512-1023 from cluster 3 must be 0xBB
expect(buf[512]).to_equal(0xBBu8)
expect(buf[1023]).to_equal(0xBBu8)
```

</details>

#### three-cluster file (2->3->4) assembles all clusters in order

- var fat =  zero sector
- fat =  fat put
- fat =  fat put
- fat =  fat put
- var sec2 =  fill sector
- var sec3 =  fill sector
- var sec4 =  fill sector
- var dev = MockReadDev new
- dev = dev with sector
- dev = dev with sector
- dev = dev with sector
- dev = dev with sector
- var fs =  make fs
- var buf =  make buf
   - Expected: result.is_ok() is true
   - Expected: result.unwrap() equals `1536u64`
   - Expected: buf[0] equals `0x01u8`
   - Expected: buf[511] equals `0x01u8`
   - Expected: buf[512] equals `0x02u8`
   - Expected: buf[1023] equals `0x02u8`
   - Expected: buf[1024] equals `0x03u8`
   - Expected: buf[1535] equals `0x03u8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var fat = _zero_sector()
fat = _fat_put(fat, 2u32, 3u32)
fat = _fat_put(fat, 3u32, 4u32)
fat = _fat_put(fat, 4u32, _eoc())
var sec2 = _fill_sector(0x01u8)
var sec3 = _fill_sector(0x02u8)
var sec4 = _fill_sector(0x03u8)
var dev = MockReadDev.new()
dev = dev.with_sector(_fat_sector_lba(), fat)
dev = dev.with_sector(_cluster_lba(2u32), sec2)
dev = dev.with_sector(_cluster_lba(3u32), sec3)
dev = dev.with_sector(_cluster_lba(4u32), sec4)
var fs = _make_fs()
val h = _make_handle(2u32, 1536u64)
var buf = _make_buf(1536)
val result = fs.read(dev, h, buf)
expect(result.is_ok()).to_equal(true)
expect(result.unwrap()).to_equal(1536u64)
expect(buf[0]).to_equal(0x01u8)
expect(buf[511]).to_equal(0x01u8)
expect(buf[512]).to_equal(0x02u8)
expect(buf[1023]).to_equal(0x02u8)
expect(buf[1024]).to_equal(0x03u8)
expect(buf[1535]).to_equal(0x03u8)
```

</details>

#### multi-cluster file smaller than last cluster is truncated

- var fat =  zero sector
- fat =  fat put
- fat =  fat put
- var sec2 =  fill sector
- var sec3 =  zero sector
- var dev = MockReadDev new
- dev = dev with sector
- dev = dev with sector
- dev = dev with sector
- var fs =  make fs
- var buf =  make buf
   - Expected: result.is_ok() is true
   - Expected: result.unwrap() equals `520u64`
   - Expected: buf[0] equals `0xAAu8`
   - Expected: buf[511] equals `0xAAu8`
   - Expected: buf[512] equals `0x01u8`
   - Expected: buf[519] equals `0x08u8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 31 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Cluster 2 → cluster 3 → EOC. file_size=520 (8 bytes into cluster 3).
var fat = _zero_sector()
fat = _fat_put(fat, 2u32, 3u32)
fat = _fat_put(fat, 3u32, _eoc())
var sec2 = _fill_sector(0xAAu8)
var sec3 = _zero_sector()
sec3[0] = 0x01u8
sec3[1] = 0x02u8
sec3[2] = 0x03u8
sec3[3] = 0x04u8
sec3[4] = 0x05u8
sec3[5] = 0x06u8
sec3[6] = 0x07u8
sec3[7] = 0x08u8
sec3[8] = 0xFFu8   # beyond file_size — must NOT appear
var dev = MockReadDev.new()
dev = dev.with_sector(_fat_sector_lba(), fat)
dev = dev.with_sector(_cluster_lba(2u32), sec2)
dev = dev.with_sector(_cluster_lba(3u32), sec3)
var fs = _make_fs()
val h = _make_handle(2u32, 520u64)
var buf = _make_buf(520)
val result = fs.read(dev, h, buf)
expect(result.is_ok()).to_equal(true)
expect(result.unwrap()).to_equal(520u64)
# All of cluster 2
expect(buf[0]).to_equal(0xAAu8)
expect(buf[511]).to_equal(0xAAu8)
# Exactly 8 bytes from cluster 3
expect(buf[512]).to_equal(0x01u8)
expect(buf[519]).to_equal(0x08u8)
```

</details>

### EOF and empty

#### handle already at EOF returns Ok(0)

- var dev = MockReadDev new
- var fs =  make fs
- var h =  make handle
- var buf =  make buf
   - Expected: result.is_ok() is true
   - Expected: result.unwrap() equals `0u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var dev = MockReadDev.new()
var fs = _make_fs()
var h = _make_handle(2u32, 100u64)
h.offset = 100u64
var buf = _make_buf(10)
val result = fs.read(dev, h, buf)
expect(result.is_ok()).to_equal(true)
expect(result.unwrap()).to_equal(0u64)
```

</details>

#### zero-length buf returns Ok(0) without touching dev

- var dev = MockReadDev new
- var fs =  make fs
- var buf =  make buf
   - Expected: result.is_ok() is true
   - Expected: result.unwrap() equals `0u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var dev = MockReadDev.new()
var fs = _make_fs()
val h = _make_handle(2u32, 100u64)
var buf = _make_buf(0)
val result = fs.read(dev, h, buf)
expect(result.is_ok()).to_equal(true)
expect(result.unwrap()).to_equal(0u64)
```

</details>

### corrupt chain during read

#### cyclic FAT chain during read returns Err and does not hang

- var fat =  zero sector
- fat =  fat put
- fat =  fat put
- var dev = MockReadDev new
- dev = dev with sector
- var fs =  make fs
- var buf =  make buf
   - Expected: result.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# 2→3→2 cycle, fuel=2: read_cluster_chain returns Err → read returns Err(EIO)
var fat = _zero_sector()
fat = _fat_put(fat, 2u32, 3u32)
fat = _fat_put(fat, 3u32, 2u32)
var dev = MockReadDev.new()
dev = dev.with_sector(_fat_sector_lba(), fat)
var fs = _make_fs()
val h = _make_handle(2u32, 1024u64)
var buf = _make_buf(1024)
val result = fs.read(dev, h, buf)
expect(result.is_err()).to_equal(true)
```

</details>

#### FREE cluster mid-chain during read returns Err

- var fat =  zero sector
- fat =  fat put
- fat =  fat put
- var dev = MockReadDev new
- dev = dev with sector
- var fs =  make fs
- var buf =  make buf
   - Expected: result.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var fat = _zero_sector()
fat = _fat_put(fat, 2u32, 3u32)
fat = _fat_put(fat, 3u32, 0u32)
var dev = MockReadDev.new()
dev = dev.with_sector(_fat_sector_lba(), fat)
var fs = _make_fs()
val h = _make_handle(2u32, 1024u64)
var buf = _make_buf(1024)
val result = fs.read(dev, h, buf)
expect(result.is_err()).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
