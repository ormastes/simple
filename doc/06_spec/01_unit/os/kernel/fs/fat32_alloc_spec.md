# FAT32 Allocator — Wave-4d Spec

> Verifies:

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# FAT32 Allocator — Wave-4d Spec

Verifies:

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/kernel/fs/fat32_alloc_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

**Bug:** fat32_no_cycle_guard_chain_walk_2026-06-11  FINDING-T2
Verifies:
  1. allocate_cluster picks cluster 2 from an empty FAT and marks it EOC.
  2. allocate_cluster skips clusters already in use.
  3. Full FAT (all clusters used) → Err(ENOSPC=-28).
  4. append_cluster links chain_end → new_cluster correctly.
  5. write() to a fresh handle allocates a cluster and stores bytes
     readable back via read().
  6. Multi-cluster write extends the chain.
  7. _write_fat_entry preserves the top 4 reserved bits.

Geometry used throughout:
  fat_start=32, data_start=64, bps=512, spc=1, data_clusters=8.
  Cluster N → LBA = 64 + (N - 2).
  FAT entry for cluster N: 4-byte little-endian at sector 32 byte-offset N*4.

## Scenarios

### fat32 allocator — wave-4d

### allocate_cluster

#### allocates cluster 2 from an empty FAT and marks it EOC

- allocates cluster 2 from an empty FAT and marks it EOC
   - Expected: result.unwrap() equals `2u32`
   - Expected: entry2 equals `_eoc()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("allocates cluster 2 from an empty FAT and marks it EOC")
# Empty FAT: all entries are 0 (FREE).
val fat = _zero_sector()
var dev = MockAllocDev.new()
dev = dev.with_sector(_fat_lba(), fat)
val fs = _make_fs()
val result = fs.allocate_cluster(dev)
assert_true(result.is_ok())
expect(result.unwrap()).to_equal(2u32)
# Verify the FAT sector was written with EOC at cluster 2.
val written_fat_result = dev.read_sector(_fat_lba())
assert_true(written_fat_result.is_ok())
val written_fat = written_fat_result.unwrap()
val entry2 = _read_fat32_entry(written_fat, 2u32)
expect(entry2).to_equal(_eoc())
```

</details>

#### skips used clusters and allocates the first free one

- skips used clusters and allocates the first free one
   - Expected: result.unwrap() equals `4u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("skips used clusters and allocates the first free one")
# Mark clusters 2 and 3 as used (EOC); cluster 4 is free.
var fat = _zero_sector()
fat = _fat_put(fat, 2u32, _eoc())
fat = _fat_put(fat, 3u32, _eoc())
var dev = MockAllocDev.new()
dev = dev.with_sector(_fat_lba(), fat)
val fs = _make_fs()
val result = fs.allocate_cluster(dev)
assert_true(result.is_ok())
expect(result.unwrap()).to_equal(4u32)
```

</details>

#### returns Err(ENOSPC=-28) when all clusters are used

- returns Err(ENOSPC=-28) when all clusters are used
   - Expected: result.unwrap_err() equals `-28`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("returns Err(ENOSPC=-28) when all clusters are used")
# data_clusters=8 means clusters 2..9 are valid.
# Mark all 8 as used.
var fat = _zero_sector()
var ci: u32 = 2u32
while ci < 10u32:
    fat = _fat_put(fat, ci, _eoc())
    ci = ci + 1u32
var dev = MockAllocDev.new()
dev = dev.with_sector(_fat_lba(), fat)
val fs = _make_fs()
val result = fs.allocate_cluster(dev)
assert_true(result.is_err())
expect(result.unwrap_err()).to_equal(-28)
```

</details>

### append_cluster

#### links chain_end to new_cluster in the FAT

- links chain_end to new_cluster in the FAT
   - Expected: entry2 equals `3u32`
   - Expected: entry3 equals `_eoc()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("links chain_end to new_cluster in the FAT")
# cluster 2 is EOC (chain end), cluster 3 is EOC (freshly allocated).
var fat = _zero_sector()
fat = _fat_put(fat, 2u32, _eoc())
fat = _fat_put(fat, 3u32, _eoc())
var dev = MockAllocDev.new()
dev = dev.with_sector(_fat_lba(), fat)
val fs = _make_fs()
val result = fs.append_cluster(dev, 2u32, 3u32)
assert_true(result.is_ok())
# cluster 2 should now point to cluster 3.
val written_fat_result = dev.read_sector(_fat_lba())
assert_true(written_fat_result.is_ok())
val written_fat = written_fat_result.unwrap()
val entry2 = _read_fat32_entry(written_fat, 2u32)
expect(entry2).to_equal(3u32)
# cluster 3 should still be EOC.
val entry3 = _read_fat32_entry(written_fat, 3u32)
expect(entry3).to_equal(_eoc())
```

</details>

#### keeps EOC at new tail after append

- keeps EOC at new tail after append
   - Expected: _read_fat32_entry(wf, 2u32) equals `3u32`
   - Expected: _read_fat32_entry(wf, 3u32) equals `4u32`
   - Expected: _read_fat32_entry(wf, 4u32) equals `_eoc()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("keeps EOC at new tail after append")
var fat = _zero_sector()
fat = _fat_put(fat, 2u32, _eoc())
fat = _fat_put(fat, 3u32, _eoc())
fat = _fat_put(fat, 4u32, _eoc())
var dev = MockAllocDev.new()
dev = dev.with_sector(_fat_lba(), fat)
val fs = _make_fs()
# Append 3 after 2, then 4 after 3.
val r1 = fs.append_cluster(dev, 2u32, 3u32)
assert_true(r1.is_ok())
val r2 = fs.append_cluster(dev, 3u32, 4u32)
assert_true(r2.is_ok())
val written_fat_result = dev.read_sector(_fat_lba())
assert_true(written_fat_result.is_ok())
val wf = written_fat_result.unwrap()
# 2 → 3 → 4 → EOC
expect(_read_fat32_entry(wf, 2u32)).to_equal(3u32)
expect(_read_fat32_entry(wf, 3u32)).to_equal(4u32)
expect(_read_fat32_entry(wf, 4u32)).to_equal(_eoc())
```

</details>

### _write_fat_entry preserves reserved top 4 bits

#### preserves bits 28-31 of existing entry when writing

- preserves bits 28-31 of existing entry when writing
   - Expected: byte3 equals `0xF0u8`
   - Expected: rb[off5] equals `0x03u8`
   - Expected: rb[off5 + 1] equals `0x00u8`
   - Expected: rb[off5 + 2] equals `0x00u8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("preserves bits 28-31 of existing entry when writing")
# Plant an entry at cluster 5 with top nibble 0xF0 (bits 28-31 set).
var fat = _zero_sector()
val off5 = (5u32 * 4u32).to_i32()
# Write raw bytes: value = 0xF0000000 (top nibble set, lower 28 bits zero).
fat[off5 + 3] = 0xF0u8
var dev = MockAllocDev.new()
dev = dev.with_sector(_fat_lba(), fat)
val fs = _make_fs()
# Write value 0x00000003 — should result in on-disk word 0xF0000003.
val wr = fs._write_fat_entry(dev, 5u32, 3u32)
assert_true(wr.is_ok())
val read_back_result = dev.read_sector(_fat_lba())
assert_true(read_back_result.is_ok())
val rb = read_back_result.unwrap()
# Check raw byte 3 of entry 5: top nibble preserved = 0xF0.
val byte3 = rb[off5 + 3]
expect(byte3).to_equal(0xF0u8)
# Bottom 3 bytes encode value 3 = 0x00000003.
expect(rb[off5]).to_equal(0x03u8)
expect(rb[off5 + 1]).to_equal(0x00u8)
expect(rb[off5 + 2]).to_equal(0x00u8)
```

</details>

### write()

#### allocates a cluster and stores bytes on a fresh handle

- allocates a cluster and stores bytes on a fresh handle
   - Expected: h.start_cluster equals `2u32`
   - Expected: h.file_size equals `10u64`
   - Expected: rd.unwrap() equals `10u64`
   - Expected: rbuf[0] equals `0xBBu8`
   - Expected: rbuf[9] equals `0xBBu8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("allocates a cluster and stores bytes on a fresh handle")
var fat = _zero_sector()
var dev = MockAllocDev.new()
dev = dev.with_sector(_fat_lba(), fat)
val fs = _make_fs()
val h0 = _make_fresh_handle()
val data = _fill_bytes(0xBBu8, 10)
val wr = fs.write(dev, h0, data)
assert_true(wr.is_ok())
var h = wr.unwrap()
# h.start_cluster should be set to cluster 2.
expect(h.start_cluster).to_equal(2u32)
# h.file_size should now be 10.
expect(h.file_size).to_equal(10u64)
# Read back the bytes via read().
var rbuf = _make_buf(10)
h.offset = 0u64
val rd = fs.read(dev, h, rbuf)
assert_true(rd.is_ok())
expect(rd.unwrap()).to_equal(10u64)
expect(rbuf[0]).to_equal(0xBBu8)
expect(rbuf[9]).to_equal(0xBBu8)
```

</details>

#### multi-cluster write extends the chain

- multi-cluster write extends the chain
   - Expected: h.file_size equals `600u64`
   - Expected: rd.unwrap() equals `600u64`
   - Expected: rbuf[0] equals `0xCCu8`
   - Expected: rbuf[599] equals `0xCCu8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("multi-cluster write extends the chain")
# Write 600 bytes — spans 2 sectors = 2 clusters (spc=1, bps=512).
var fat = _zero_sector()
var dev = MockAllocDev.new()
dev = dev.with_sector(_fat_lba(), fat)
val fs = _make_fs()
val h0 = _make_fresh_handle()
val data = _fill_bytes(0xCCu8, 600)
val wr = fs.write(dev, h0, data)
assert_true(wr.is_ok())
var h = wr.unwrap()
expect(h.file_size).to_equal(600u64)
# Read back.
var rbuf = _make_buf(600)
h.offset = 0u64
val rd = fs.read(dev, h, rbuf)
assert_true(rd.is_ok())
expect(rd.unwrap()).to_equal(600u64)
expect(rbuf[0]).to_equal(0xCCu8)
expect(rbuf[599]).to_equal(0xCCu8)
```

</details>

#### write to full FAT returns Err(ENOSPC)

- write to full FAT returns Err(ENOSPC)
   - Expected: wr.unwrap_err() equals `-28`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("write to full FAT returns Err(ENOSPC)")
# Mark all 8 clusters used.
var fat = _zero_sector()
var ci: u32 = 2u32
while ci < 10u32:
    fat = _fat_put(fat, ci, _eoc())
    ci = ci + 1u32
var dev = MockAllocDev.new()
dev = dev.with_sector(_fat_lba(), fat)
val fs = _make_fs()
val h0 = _make_fresh_handle()
val data = _fill_bytes(0xAAu8, 10)
val wr = fs.write(dev, h0, data)
assert_true(wr.is_err())
expect(wr.unwrap_err()).to_equal(-28)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-OS`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `ba6653efeaa88cfbc1e878f38e8f89c1de794f60a8ed360d65bc035e82790a8e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ba6653efeaa88cfbc1e878f38e8f89c1de794f60a8ed360d65bc035e82790a8e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ba6653efeaa88cfbc1e878f38e8f89c1de794f60a8ed360d65bc035e82790a8e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/os/kernel/fs/fat32_alloc_spec.spl
mirror: doc/06_spec/01_unit/os/kernel/fs/fat32_alloc_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/kernel/fs/fat32_alloc_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/kernel/fs/fat32_alloc_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/kernel/fs/fat32_alloc_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/os/kernel/fs/fat32_alloc_spec.spl:163:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'allocates cluster 2 from an empty FAT and marks it EOC' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/kernel/fs/fat32_alloc_spec.spl:181:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'skips used clusters and allocates the first free one' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/kernel/fs/fat32_alloc_spec.spl:195:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns Err(ENOSPC=-28) when all clusters are used' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
