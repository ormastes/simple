# FAT32 read() — Wave-4c Spec

> Verifies that `Fat32Filesystem.read(dev, handle, buf)`:

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
| Updated | 2026-08-26 |
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

- reads exactly file_size bytes from a single cluster
   - Expected: result.is_ok() is true
   - Expected: result.unwrap() equals `10u64`
   - Expected: buf[0] equals `0xAAu8`
   - Expected: buf[9] equals `0xAAu8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reads exactly file_size bytes from a single cluster")
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

- reads up to buf.len() when buf is smaller than file_size
   - Expected: result.is_ok() is true
   - Expected: result.unwrap() equals `20u64`
   - Expected: buf[ci] equals `0xBBu8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reads up to buf.len() when buf is smaller than file_size")
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

- file smaller than cluster — last cluster bytes are NOT returned
   - Expected: result.is_ok() is true
   - Expected: result.unwrap() equals `3u64`
   - Expected: buf[0] equals `0x11u8`
   - Expected: buf[1] equals `0x22u8`
   - Expected: buf[2] equals `0x33u8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("file smaller than cluster — last cluster bytes are NOT returned")
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

- two-cluster file assembles bytes in chain order
   - Expected: result.is_ok() is true
   - Expected: result.unwrap() equals `1024u64`
   - Expected: buf[0] equals `0xAAu8`
   - Expected: buf[511] equals `0xAAu8`
   - Expected: buf[512] equals `0xBBu8`
   - Expected: buf[1023] equals `0xBBu8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("two-cluster file assembles bytes in chain order")
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

- three-cluster file (2->3->4) assembles all clusters in order
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

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("three-cluster file (2->3->4) assembles all clusters in order")
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

- multi-cluster file smaller than last cluster is truncated
   - Expected: result.is_ok() is true
   - Expected: result.unwrap() equals `520u64`
   - Expected: buf[0] equals `0xAAu8`
   - Expected: buf[511] equals `0xAAu8`
   - Expected: buf[512] equals `0x01u8`
   - Expected: buf[519] equals `0x08u8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 33 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("multi-cluster file smaller than last cluster is truncated")
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

- handle already at EOF returns Ok(0)
   - Expected: result.is_ok() is true
   - Expected: result.unwrap() equals `0u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handle already at EOF returns Ok(0)")
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

- zero-length buf returns Ok(0) without touching dev
   - Expected: result.is_ok() is true
   - Expected: result.unwrap() equals `0u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("zero-length buf returns Ok(0) without touching dev")
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

- cyclic FAT chain during read returns Err and does not hang
   - Expected: result.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("cyclic FAT chain during read returns Err and does not hang")
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

- FREE cluster mid-chain during read returns Err
   - Expected: result.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("FREE cluster mid-chain during read returns Err")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `475ca647be03da0150eccaf7bc1378e9d313238f31122e1d90b5dac41ec0a615`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `475ca647be03da0150eccaf7bc1378e9d313238f31122e1d90b5dac41ec0a615`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `475ca647be03da0150eccaf7bc1378e9d313238f31122e1d90b5dac41ec0a615`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/os/kernel/fs/fat32_read_spec.spl
mirror: doc/06_spec/01_unit/os/kernel/fs/fat32_read_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/kernel/fs/fat32_read_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/kernel/fs/fat32_read_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/kernel/fs/fat32_read_spec.spl:139:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reads exactly file_size bytes from a single cluster' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/kernel/fs/fat32_read_spec.spl:158:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reads up to buf.len() when buf is smaller than file_size' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/kernel/fs/fat32_read_spec.spl:178:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'file smaller than cluster — last cluster bytes are NOT returned' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
