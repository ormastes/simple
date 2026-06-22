# Zstd Typed Specification

> <details>

<!-- sdn-diagram:id=zstd_typed_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=zstd_typed_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

zstd_typed_spec -> std
zstd_typed_spec -> lib
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=zstd_typed_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 33 | 33 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Zstd Typed Specification

## Scenarios

### FseTable scaffold

#### symbol spread invariant: each symbol gets exactly counts[s] slots

- assert equal
- assert equal
- assert equal
- assert equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val counts_arr: [i64] = [4, 4, 4, 4]
val tbl = FseTable.from_normalized_counts(counts_arr, 4)
val s0 = tbl.slots_for_symbol(0)
val s1 = tbl.slots_for_symbol(1)
val s2 = tbl.slots_for_symbol(2)
val s3 = tbl.slots_for_symbol(3)
assert_equal(s0, 4)
assert_equal(s1, 4)
assert_equal(s2, 4)
assert_equal(s3, 4)
```

</details>

#### total occupied slots == 1<<table_log

- assert equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val counts_arr: [i64] = [4, 4, 4, 4]
val tbl = FseTable.from_normalized_counts(counts_arr, 4)
val total = tbl.slots_for_symbol(0) + tbl.slots_for_symbol(1) + tbl.slots_for_symbol(2) + tbl.slots_for_symbol(3)
assert_equal(total, 16)
```

</details>

#### table_size returns 1<<table_log

- assert equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val counts_arr: [i64] = [2, 2]
val tbl = FseTable.from_normalized_counts(counts_arr, 2)
val sz = tbl.table_size()
assert_equal(sz, 4)
```

</details>

#### symbol distribution 2-sym: each gets exactly 2 slots in 4-slot table

- assert equal
- assert equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val counts_arr: [i64] = [2, 2]
val tbl = FseTable.from_normalized_counts(counts_arr, 2)
val s0 = tbl.slots_for_symbol(0)
val s1 = tbl.slots_for_symbol(1)
assert_equal(s0, 2)
assert_equal(s1, 2)
```

</details>

#### decode_symbol_stub returns valid symbol for any state

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val counts_arr: [i64] = [4, 4, 4, 4]
val tbl = FseTable.from_normalized_counts(counts_arr, 4)
val sym_at_0 = tbl.decode_symbol_stub(0)
# sym must be in 0..3 (a valid symbol index)
val ok = (sym_at_0 >= 0 and sym_at_0 <= 3)
assert_true(ok)
```

</details>

### Frame header interop KATs

#### magic bytes are 28 B5 2F FD

- assert equal
- assert equal
- assert equal
- assert equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
assert_equal(ZSTD_MAGIC_B0, 0x28)
assert_equal(ZSTD_MAGIC_B1, 0xB5)
assert_equal(ZSTD_MAGIC_B2, 0x2F)
assert_equal(ZSTD_MAGIC_B3, 0xFD)
```

</details>

#### frame header for size=5 is exactly 6 bytes

- assert equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val hdr = zstd_frame_header_bytes(5)
assert_equal(hdr.len(), 6)
```

</details>

#### frame header for size=5: magic b0 = 0x28

- assert equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val hdr = zstd_frame_header_bytes(5)
assert_equal(hdr[0].to_i64(), 0x28)
```

</details>

#### frame header for size=5: magic b1 = 0xB5

- assert equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val hdr = zstd_frame_header_bytes(5)
assert_equal(hdr[1].to_i64(), 0xB5)
```

</details>

#### frame header for size=5: magic b2 = 0x2F

- assert equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val hdr = zstd_frame_header_bytes(5)
assert_equal(hdr[2].to_i64(), 0x2F)
```

</details>

#### frame header for size=5: magic b3 = 0xFD

- assert equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val hdr = zstd_frame_header_bytes(5)
assert_equal(hdr[3].to_i64(), 0xFD)
```

</details>

#### frame header for size=5: FHD byte = 0x20 (SS=1, FCS=1B, no checksum)

- assert equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val hdr = zstd_frame_header_bytes(5)
assert_equal(hdr[4].to_i64(), 0x20)
```

</details>

#### frame header for size=5: FCS byte = 5

- assert equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val hdr = zstd_frame_header_bytes(5)
assert_equal(hdr[5].to_i64(), 5)
```

</details>

#### frame header for size=0 is exactly 6 bytes

- assert equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val hdr = zstd_frame_header_bytes(0)
assert_equal(hdr.len(), 6)
```

</details>

#### frame header for size=0: FHD = 0x20

- assert equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val hdr = zstd_frame_header_bytes(0)
assert_equal(hdr[4].to_i64(), 0x20)
```

</details>

#### frame header for size=0: FCS = 0

- assert equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val hdr = zstd_frame_header_bytes(0)
assert_equal(hdr[5].to_i64(), 0)
```

</details>

#### frame header for size=255 has 1-byte FCS = 255

- assert equal
- assert equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val hdr = zstd_frame_header_bytes(255)
assert_equal(hdr.len(), 6)
assert_equal(hdr[5].to_i64(), 255)
```

</details>

### Block header encoding KATs

#### raw block size=5 last: value=41, b0=0x29

- assert equal
- assert equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bh = zstd_block_header_bytes(5, ZSTD_BLOCK_RAW, true)
assert_equal(bh.len(), 3)
val v = (5 << 3) | (0 << 1) | 1
assert_equal(bh[0].to_i64(), v & 0xFF)
```

</details>

#### raw block size=5 last: b1=0, b2=0

- assert equal
- assert equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bh = zstd_block_header_bytes(5, ZSTD_BLOCK_RAW, true)
assert_equal(bh[1].to_i64(), 0)
assert_equal(bh[2].to_i64(), 0)
```

</details>

#### empty raw block last: v=1 -> [01 00 00]

- assert equal
- assert equal
- assert equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bh = zstd_block_header_bytes(0, ZSTD_BLOCK_RAW, true)
assert_equal(bh[0].to_i64(), 1)
assert_equal(bh[1].to_i64(), 0)
assert_equal(bh[2].to_i64(), 0)
```

</details>

#### not-last raw block: last_block bit = 0

- assert equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bh = zstd_block_header_bytes(10, ZSTD_BLOCK_RAW, false)
val v = (10 << 3) | 0
assert_equal(bh[0].to_i64(), v & 0xFF)
```

</details>

#### RLE block type=1 embedded in header

- assert equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bh = zstd_block_header_bytes(8, ZSTD_BLOCK_RLE, true)
val v = (8 << 3) | (1 << 1) | 1
assert_equal(bh[0].to_i64(), v & 0xFF)
```

</details>

#### large block size uses all 3 bytes

- assert equal
- assert equal
- assert equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# size = 0x8000 = 32768 → v = (32768<<3)|1 = 262145 = 0x040001
val bh = zstd_block_header_bytes(32768, ZSTD_BLOCK_RAW, true)
val v = (32768 << 3) | 1
assert_equal(bh[0].to_i64(), v & 0xFF)
assert_equal(bh[1].to_i64(), (v >> 8) & 0xFF)
assert_equal(bh[2].to_i64(), (v >> 16) & 0xFF)
```

</details>

### Round-trip: raw compress/decompress

#### empty input round-trips

- assert true
- assert equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val empty: [u8] = []
val compressed = zstd_compress_raw(empty)
val res = zstd_decompress(compressed)
assert_true(res.ok)
assert_equal(res.data.len(), 0)
```

</details>

#### single byte round-trips

- inp push
- assert true
- assert equal
- assert equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var inp: [u8] = []
inp.push(42u8)
val compressed = zstd_compress_raw(inp)
val res = zstd_decompress(compressed)
assert_true(res.ok)
assert_equal(res.data.len(), 1)
assert_equal(res.data[0].to_i64(), 42)
```

</details>

#### hello bytes round-trip

- inp push
- inp push
- inp push
- inp push
- inp push
- assert true
- assert equal
- assert equal
- assert equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# 'h'=104 'e'=101 'l'=108 'l'=108 'o'=111
var inp: [u8] = []
inp.push(104u8)
inp.push(101u8)
inp.push(108u8)
inp.push(108u8)
inp.push(111u8)
val compressed = zstd_compress_raw(inp)
val res = zstd_decompress(compressed)
assert_true(res.ok)
assert_equal(res.data.len(), 5)
assert_equal(res.data[0].to_i64(), 104)
assert_equal(res.data[4].to_i64(), 111)
```

</details>

#### repeated bytes round-trip (200-byte buffer)

- inp push
- assert true
- assert equal
- assert equal
- assert equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var inp: [u8] = []
var fi = 0
while fi < 200:
    inp.push(0xABu8)
    fi = fi + 1
val compressed = zstd_compress_raw(inp)
val res = zstd_decompress(compressed)
assert_true(res.ok)
assert_equal(res.data.len(), 200)
assert_equal(res.data[0].to_i64(), 0xAB)
assert_equal(res.data[199].to_i64(), 0xAB)
```

</details>

#### compressed output starts with magic

- inp push
- inp push
- inp push
- assert equal
- assert equal
- assert equal
- assert equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var inp: [u8] = []
inp.push(1u8)
inp.push(2u8)
inp.push(3u8)
val compressed = zstd_compress_raw(inp)
assert_equal(compressed[0].to_i64(), 0x28)
assert_equal(compressed[1].to_i64(), 0xB5)
assert_equal(compressed[2].to_i64(), 0x2F)
assert_equal(compressed[3].to_i64(), 0xFD)
```

</details>

#### content bytes preserved exactly (first and last)

- inp push
- inp push
- inp push
- inp push
- assert true
- assert equal
- assert equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var inp: [u8] = []
inp.push(0x11u8)
inp.push(0x22u8)
inp.push(0x33u8)
inp.push(0x44u8)
val compressed = zstd_compress_raw(inp)
val res = zstd_decompress(compressed)
assert_true(res.ok)
assert_equal(res.data[0].to_i64(), 0x11)
assert_equal(res.data[3].to_i64(), 0x44)
```

</details>

#### decompress bad magic returns ok=false

- bad push
- bad push
- bad push
- bad push
- bad push
- bad push
- bad push
- bad push
- bad push
- bad push
- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var bad: [u8] = []
bad.push(0x00u8)
bad.push(0x00u8)
bad.push(0x00u8)
bad.push(0x00u8)
bad.push(0x20u8)
bad.push(0x01u8)
bad.push(0x01u8)
bad.push(0x00u8)
bad.push(0x00u8)
bad.push(0x41u8)
val res = zstd_decompress(bad)
assert_true(not res.ok)
```

</details>

### RLE block decode KAT

#### RLE block: value=A, size=3 expands to AAA

- frame push
- frame push
- frame push
- frame push
- frame push
- frame push
- frame push
- frame push
- frame push
- frame push
- assert true
- assert equal
- assert equal
- assert equal
- assert equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var frame: [u8] = []
# magic
frame.push(0x28u8)
frame.push(0xB5u8)
frame.push(0x2Fu8)
frame.push(0xFDu8)
# FHD: SS=1, FCS=1B, no checksum
frame.push(0x20u8)
# FCS: content_size = 3
frame.push(0x03u8)
# Block header: (3<<3)|(1<<1)|1 = 27 = 0x1B
frame.push(0x1Bu8)
frame.push(0x00u8)
frame.push(0x00u8)
# RLE byte: 'A' = 0x41
frame.push(0x41u8)

val res = zstd_decompress(frame)
assert_true(res.ok)
assert_equal(res.data.len(), 3)
assert_equal(res.data[0].to_i64(), 0x41)
assert_equal(res.data[1].to_i64(), 0x41)
assert_equal(res.data[2].to_i64(), 0x41)
```

</details>

#### RLE block: value=0x00, size=5 expands to 5 zeros

- frame push
- frame push
- frame push
- frame push
- frame push
- frame push
- frame push
- frame push
- frame push
- frame push
- assert true
- assert equal
- assert equal
- assert equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var frame: [u8] = []
frame.push(0x28u8)
frame.push(0xB5u8)
frame.push(0x2Fu8)
frame.push(0xFDu8)
frame.push(0x20u8)
frame.push(0x05u8)
# Block header: (5<<3)|(1<<1)|1 = 40|2|1 = 43 = 0x2B
frame.push(0x2Bu8)
frame.push(0x00u8)
frame.push(0x00u8)
frame.push(0x00u8)

val res = zstd_decompress(frame)
assert_true(res.ok)
assert_equal(res.data.len(), 5)
assert_equal(res.data[0].to_i64(), 0)
assert_equal(res.data[4].to_i64(), 0)
```

</details>

#### compressed block type returns ok=false with deferral message

- frame push
- frame push
- frame push
- frame push
- frame push
- frame push
- frame push
- frame push
- frame push
- frame push
- frame push
- frame push
- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var frame: [u8] = []
frame.push(0x28u8)
frame.push(0xB5u8)
frame.push(0x2Fu8)
frame.push(0xFDu8)
frame.push(0x20u8)
frame.push(0x03u8)
# Block header: type=2(compressed), size=3, last=true
# v = (3<<3)|(2<<1)|1 = 24|4|1 = 29 = 0x1D
frame.push(0x1Du8)
frame.push(0x00u8)
frame.push(0x00u8)
frame.push(0x41u8)
frame.push(0x42u8)
frame.push(0x43u8)

val res = zstd_decompress(frame)
assert_true(not res.ok)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/compress/typed/zstd_typed_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- FseTable scaffold
- Frame header interop KATs
- Block header encoding KATs
- Round-trip: raw compress/decompress
- RLE block decode KAT

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 33 |
| Active scenarios | 33 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
