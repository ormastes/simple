# Zstd Typed Specification

> Tests covering FseTable scaffold, Frame header interop KATs, Block header encoding KATs, Round-trip: raw compress/decompress, RLE block decode KAT.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 49 | 49 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Zstd Typed Specification

## Scenarios

### FseTable scaffold

#### symbol spread invariant: each symbol gets exactly counts[s] slots

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- symbol spread invariant: each symbol gets exactly counts[s] slots


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("symbol spread invariant: each symbol gets exactly counts[s] slots")
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

- total occupied slots == 1<<table_log


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("total occupied slots == 1<<table_log")
val counts_arr: [i64] = [4, 4, 4, 4]
val tbl = FseTable.from_normalized_counts(counts_arr, 4)
val total = tbl.slots_for_symbol(0) + tbl.slots_for_symbol(1) + tbl.slots_for_symbol(2) + tbl.slots_for_symbol(3)
assert_equal(total, 16)
```

</details>

#### table_size returns 1<<table_log

- table_size returns 1<<table_log


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("table_size returns 1<<table_log")
val counts_arr: [i64] = [2, 2]
val tbl = FseTable.from_normalized_counts(counts_arr, 2)
val sz = tbl.table_size()
assert_equal(sz, 4)
```

</details>

#### symbol distribution 2-sym: each gets exactly 2 slots in 4-slot table

- symbol distribution 2-sym: each gets exactly 2 slots in 4-slot table


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("symbol distribution 2-sym: each gets exactly 2 slots in 4-slot table")
val counts_arr: [i64] = [2, 2]
val tbl = FseTable.from_normalized_counts(counts_arr, 2)
val s0 = tbl.slots_for_symbol(0)
val s1 = tbl.slots_for_symbol(1)
assert_equal(s0, 2)
assert_equal(s1, 2)
```

</details>

#### decode_symbol_stub returns valid symbol for any state

- decode_symbol_stub returns valid symbol for any state


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("decode_symbol_stub returns valid symbol for any state")
val counts_arr: [i64] = [4, 4, 4, 4]
val tbl = FseTable.from_normalized_counts(counts_arr, 4)
val sym_at_0 = tbl.decode_symbol_stub(0)
# sym must be in 0..3 (a valid symbol index)
val ok = (sym_at_0 >= 0 and sym_at_0 <= 3)
assert_true(ok)
```

</details>

#### overfull normalized counts return empty table

- overfull normalized counts return empty table


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("overfull normalized counts return empty table")
val counts_arr: [i64] = [3, 3]
val tbl = FseTable.from_normalized_counts(counts_arr, 2)
assert_equal(tbl.table_size(), 1)
assert_equal(tbl.slots_for_symbol(0), 0)
assert_equal(tbl.decode_symbol_stub(0), -1)
```

</details>

#### negative normalized count below minus one returns empty table

- negative normalized count below minus one returns empty table


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("negative normalized count below minus one returns empty table")
val counts_arr: [i64] = [4, -2]
val tbl = FseTable.from_normalized_counts(counts_arr, 2)
assert_equal(tbl.table_size(), 1)
assert_equal(tbl.slots_for_symbol(0), 0)
assert_equal(tbl.decode_symbol_stub(0), -1)
```

</details>

### Frame header interop KATs

#### magic bytes are 28 B5 2F FD

- magic bytes are 28 B5 2F FD


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("magic bytes are 28 B5 2F FD")
assert_equal(ZSTD_MAGIC_B0, 0x28)
assert_equal(ZSTD_MAGIC_B1, 0xB5)
assert_equal(ZSTD_MAGIC_B2, 0x2F)
assert_equal(ZSTD_MAGIC_B3, 0xFD)
```

</details>

#### frame header for size=5 is exactly 6 bytes

- frame header for size=5 is exactly 6 bytes


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("frame header for size=5 is exactly 6 bytes")
val hdr = zstd_frame_header_bytes(5)
assert_equal(hdr.len(), 6)
```

</details>

#### frame header for size=5: magic b0 = 0x28

- frame header for size=5: magic b0 = 0x28


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("frame header for size=5: magic b0 = 0x28")
val hdr = zstd_frame_header_bytes(5)
assert_equal(hdr[0].to_i64(), 0x28)
```

</details>

#### frame header for size=5: magic b1 = 0xB5

- frame header for size=5: magic b1 = 0xB5


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("frame header for size=5: magic b1 = 0xB5")
val hdr = zstd_frame_header_bytes(5)
assert_equal(hdr[1].to_i64(), 0xB5)
```

</details>

#### frame header for size=5: magic b2 = 0x2F

- frame header for size=5: magic b2 = 0x2F


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("frame header for size=5: magic b2 = 0x2F")
val hdr = zstd_frame_header_bytes(5)
assert_equal(hdr[2].to_i64(), 0x2F)
```

</details>

#### frame header for size=5: magic b3 = 0xFD

- frame header for size=5: magic b3 = 0xFD


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("frame header for size=5: magic b3 = 0xFD")
val hdr = zstd_frame_header_bytes(5)
assert_equal(hdr[3].to_i64(), 0xFD)
```

</details>

#### frame header for size=5: FHD byte = 0x20 (SS=1, FCS=1B, no checksum)

- frame header for size=5: FHD byte = 0x20 (SS=1, FCS=1B, no checksum)


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("frame header for size=5: FHD byte = 0x20 (SS=1, FCS=1B, no checksum)")
val hdr = zstd_frame_header_bytes(5)
assert_equal(hdr[4].to_i64(), 0x20)
```

</details>

#### frame header for size=5: FCS byte = 5

- frame header for size=5: FCS byte = 5


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("frame header for size=5: FCS byte = 5")
val hdr = zstd_frame_header_bytes(5)
assert_equal(hdr[5].to_i64(), 5)
```

</details>

#### frame header for size=0 is exactly 6 bytes

- frame header for size=0 is exactly 6 bytes


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("frame header for size=0 is exactly 6 bytes")
val hdr = zstd_frame_header_bytes(0)
assert_equal(hdr.len(), 6)
```

</details>

#### frame header for size=0: FHD = 0x20

- frame header for size=0: FHD = 0x20


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("frame header for size=0: FHD = 0x20")
val hdr = zstd_frame_header_bytes(0)
assert_equal(hdr[4].to_i64(), 0x20)
```

</details>

#### frame header for size=0: FCS = 0

- frame header for size=0: FCS = 0


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("frame header for size=0: FCS = 0")
val hdr = zstd_frame_header_bytes(0)
assert_equal(hdr[5].to_i64(), 0)
```

</details>

#### frame header for size=255 has 1-byte FCS = 255

- frame header for size=255 has 1-byte FCS = 255


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("frame header for size=255 has 1-byte FCS = 255")
val hdr = zstd_frame_header_bytes(255)
assert_equal(hdr.len(), 6)
assert_equal(hdr[5].to_i64(), 255)
```

</details>

### Block header encoding KATs

#### raw block size=5 last: value=41, b0=0x29

- raw block size=5 last: value=41, b0=0x29


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("raw block size=5 last: value=41, b0=0x29")
val bh = zstd_block_header_bytes(5, ZSTD_BLOCK_RAW, true)
assert_equal(bh.len(), 3)
val v = (5 << 3) | (0 << 1) | 1
assert_equal(bh[0].to_i64(), v & 0xFF)
```

</details>

#### raw block size=5 last: b1=0, b2=0

- raw block size=5 last: b1=0, b2=0


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("raw block size=5 last: b1=0, b2=0")
val bh = zstd_block_header_bytes(5, ZSTD_BLOCK_RAW, true)
assert_equal(bh[1].to_i64(), 0)
assert_equal(bh[2].to_i64(), 0)
```

</details>

#### empty raw block last: v=1 -> [01 00 00]

- empty raw block last: v=1 -> [01 00 00]


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("empty raw block last: v=1 -> [01 00 00]")
val bh = zstd_block_header_bytes(0, ZSTD_BLOCK_RAW, true)
assert_equal(bh[0].to_i64(), 1)
assert_equal(bh[1].to_i64(), 0)
assert_equal(bh[2].to_i64(), 0)
```

</details>

#### not-last raw block: last_block bit = 0

- not-last raw block: last_block bit = 0


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("not-last raw block: last_block bit = 0")
val bh = zstd_block_header_bytes(10, ZSTD_BLOCK_RAW, false)
val v = (10 << 3) | 0
assert_equal(bh[0].to_i64(), v & 0xFF)
```

</details>

#### RLE block type=1 embedded in header

- RLE block type=1 embedded in header


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("RLE block type=1 embedded in header")
val bh = zstd_block_header_bytes(8, ZSTD_BLOCK_RLE, true)
val v = (8 << 3) | (1 << 1) | 1
assert_equal(bh[0].to_i64(), v & 0xFF)
```

</details>

#### large block size uses all 3 bytes

- large block size uses all 3 bytes


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("large block size uses all 3 bytes")
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

- empty input round-trips


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("empty input round-trips")
val empty: [u8] = []
val compressed = zstd_compress_raw(empty)
val res = zstd_decompress(compressed)
assert_true(res.ok)
assert_equal(res.data.len(), 0)
```

</details>

#### single byte round-trips

- single byte round-trips


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("single byte round-trips")
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

- hello bytes round-trip


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("hello bytes round-trip")
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

- repeated bytes round-trip (200-byte buffer)


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("repeated bytes round-trip (200-byte buffer)")
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

- compressed output starts with magic


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("compressed output starts with magic")
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

- content bytes preserved exactly (first and last)


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("content bytes preserved exactly (first and last)")
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

- decompress bad magic returns ok=false


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("decompress bad magic returns ok=false")
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

#### checksum flag without checksum bytes returns ok=false

- checksum flag without checksum bytes returns ok=false


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("checksum flag without checksum bytes returns ok=false")
var frame: [u8] = []
frame.push(0x28u8)
frame.push(0xB5u8)
frame.push(0x2Fu8)
frame.push(0xFDu8)
frame.push(0x24u8)
frame.push(0x01u8)
frame.push(0x09u8)
frame.push(0x00u8)
frame.push(0x00u8)
frame.push(0x41u8)
val res = zstd_decompress(frame)
assert_true(not res.ok)
```

</details>

#### checksum flag with checksum bytes returns ok=false

- checksum flag with checksum bytes returns ok=false


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("checksum flag with checksum bytes returns ok=false")
var inp: [u8] = []
inp.push(0x41u8)
var frame = zstd_compress_raw(inp)
frame[4] = 0x24u8
frame.push(0x00u8)
frame.push(0x00u8)
frame.push(0x00u8)
frame.push(0x00u8)
val res = zstd_decompress(frame)
assert_true(not res.ok)
```

</details>

#### content size mismatch returns ok=false

- content size mismatch returns ok=false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("content size mismatch returns ok=false")
var inp: [u8] = []
inp.push(0x41u8)
var frame = zstd_compress_raw(inp)
frame[5] = 0x02u8
val res = zstd_decompress(frame)
assert_true(not res.ok)
```

</details>

#### raw block larger than content size returns ok=false before copy

- raw block larger than content size returns ok=false before copy


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("raw block larger than content size returns ok=false before copy")
var frame: [u8] = []
frame.push(0x28u8)
frame.push(0xB5u8)
frame.push(0x2Fu8)
frame.push(0xFDu8)
frame.push(0x20u8)
frame.push(0x01u8)
frame.push(0x11u8)
frame.push(0x00u8)
frame.push(0x00u8)
frame.push(0x41u8)
frame.push(0x42u8)
val res = zstd_decompress(frame)
assert_true(not res.ok)
assert_equal(res.error, "block exceeds content size")
```

</details>

#### extra block after declared content size returns ok=false

- extra block after declared content size returns ok=false


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extra block after declared content size returns ok=false")
var frame: [u8] = []
frame.push(0x28u8)
frame.push(0xB5u8)
frame.push(0x2Fu8)
frame.push(0xFDu8)
frame.push(0x20u8)
frame.push(0x01u8)
# Non-final raw block: size=1, type=raw, last=false -> 0x08.
frame.push(0x08u8)
frame.push(0x00u8)
frame.push(0x00u8)
frame.push(0x41u8)
# Final raw block with zero bytes. This block is structurally extra.
frame.push(0x01u8)
frame.push(0x00u8)
frame.push(0x00u8)
val res = zstd_decompress(frame)
assert_true(not res.ok)
assert_equal(res.error, "extra block after content size")
```

</details>

#### 8-byte content size form returns ok=false

- 8-byte content size form returns ok=false


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("8-byte content size form returns ok=false")
var frame: [u8] = []
frame.push(0x28u8)
frame.push(0xB5u8)
frame.push(0x2Fu8)
frame.push(0xFDu8)
frame.push(0xE0u8)
var i = 0
while i < 8:
    frame.push(0x00u8)
    i = i + 1
val res = zstd_decompress(frame)
assert_true(not res.ok)
```

</details>

#### dictionary id flag returns ok=false

- dictionary id flag returns ok=false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("dictionary id flag returns ok=false")
var inp: [u8] = []
inp.push(0x41u8)
var frame = zstd_compress_raw(inp)
frame[4] = 0x21u8
val res = zstd_decompress(frame)
assert_true(not res.ok)
```

</details>

#### reserved frame header bit returns ok=false

- reserved frame header bit returns ok=false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reserved frame header bit returns ok=false")
var inp: [u8] = []
inp.push(0x41u8)
var frame = zstd_compress_raw(inp)
frame[4] = 0x28u8
val res = zstd_decompress(frame)
assert_true(not res.ok)
```

</details>

#### unused frame header bit returns ok=false

- unused frame header bit returns ok=false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("unused frame header bit returns ok=false")
var inp: [u8] = []
inp.push(0x41u8)
var frame = zstd_compress_raw(inp)
frame[4] = 0x30u8
val res = zstd_decompress(frame)
assert_true(not res.ok)
```

</details>

#### non-single-segment frame returns ok=false

- non-single-segment frame returns ok=false


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("non-single-segment frame returns ok=false")
var frame: [u8] = []
frame.push(0x28u8)
frame.push(0xB5u8)
frame.push(0x2Fu8)
frame.push(0xFDu8)
frame.push(0x00u8)
frame.push(0x00u8)
frame.push(0x01u8)
frame.push(0x09u8)
frame.push(0x00u8)
frame.push(0x00u8)
frame.push(0x41u8)
val res = zstd_decompress(frame)
assert_true(not res.ok)
```

</details>

#### trailing bytes after final block return ok=false

- trailing bytes after final block return ok=false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("trailing bytes after final block return ok=false")
var inp: [u8] = []
inp.push(0x41u8)
var frame = zstd_compress_raw(inp)
frame.push(0x00u8)
val res = zstd_decompress(frame)
assert_true(not res.ok)
```

</details>

#### oversized RLE block returns ok=false

- oversized RLE block returns ok=false


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("oversized RLE block returns ok=false")
var frame: [u8] = []
frame.push(0x28u8)
frame.push(0xB5u8)
frame.push(0x2Fu8)
frame.push(0xFDu8)
frame.push(0xA0u8)
frame.push(0x01u8)
frame.push(0x00u8)
frame.push(0x02u8)
frame.push(0x00u8)
# Block header: size=131073, type=RLE, last=true.
frame.push(0x0Bu8)
frame.push(0x00u8)
frame.push(0x10u8)
frame.push(0x41u8)
val res = zstd_decompress(frame)
assert_true(not res.ok)
```

</details>

### RLE block decode KAT

#### RLE block with zero regenerated size returns ok=false

- RLE block with zero regenerated size returns ok=false


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("RLE block with zero regenerated size returns ok=false")
var frame: [u8] = []
frame.push(0x28u8)
frame.push(0xB5u8)
frame.push(0x2Fu8)
frame.push(0xFDu8)
frame.push(0x20u8)
frame.push(0x00u8)
# Block header: size=0, type=RLE, last=true -> 0x03
frame.push(0x03u8)
frame.push(0x00u8)
frame.push(0x00u8)
frame.push(0x41u8)
val res = zstd_decompress(frame)
assert_true(not res.ok)
```

</details>

#### RLE block larger than content size returns ok=false before expansion

- RLE block larger than content size returns ok=false before expansion


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("RLE block larger than content size returns ok=false before expansion")
var frame: [u8] = []
frame.push(0x28u8)
frame.push(0xB5u8)
frame.push(0x2Fu8)
frame.push(0xFDu8)
frame.push(0x20u8)
frame.push(0x01u8)
# Block header: size=2, type=RLE, last=true -> 0x13
frame.push(0x13u8)
frame.push(0x00u8)
frame.push(0x00u8)
frame.push(0x41u8)
val res = zstd_decompress(frame)
assert_true(not res.ok)
assert_equal(res.error, "block exceeds content size")
```

</details>

#### RLE block: value=A, size=3 expands to AAA

- RLE block: value=A, size=3 expands to AAA


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("RLE block: value=A, size=3 expands to AAA")
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

- RLE block: value=0x00, size=5 expands to 5 zeros


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("RLE block: value=0x00, size=5 expands to 5 zeros")
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

- compressed block type returns ok=false with deferral message


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("compressed block type returns ok=false with deferral message")
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
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering FseTable scaffold, Frame header interop KATs, Block header encoding KATs, Round-trip: raw compress/decompress, RLE block decode KAT.
- FseTable scaffold
- Frame header interop KATs
- Block header encoding KATs
- Round-trip: raw compress/decompress
- RLE block decode KAT

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 49 |
| Active scenarios | 49 |
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

- Canonical SPipe generation for source `64b0e063a57f59c5561c8c067823072f62a27f1c409dd7947b5338444a416bc9`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `64b0e063a57f59c5561c8c067823072f62a27f1c409dd7947b5338444a416bc9`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `64b0e063a57f59c5561c8c067823072f62a27f1c409dd7947b5338444a416bc9`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/common/compress/typed/zstd_typed_spec.spl
mirror: doc/06_spec/01_unit/lib/common/compress/typed/zstd_typed_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/compress/typed/zstd_typed_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/compress/typed/zstd_typed_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/compress/typed/zstd_typed_spec.spl:52:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'symbol spread invariant: each symbol gets exactly counts[s] slots' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/compress/typed/zstd_typed_spec.spl:66:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'total occupied slots == 1<<table_log' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/compress/typed/zstd_typed_spec.spl:74:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'table_size returns 1<<table_log' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
