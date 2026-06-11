# Zstd Specification

> 1. fail

<!-- sdn-diagram:id=zstd_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=zstd_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

zstd_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=zstd_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 30 | 30 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Zstd Specification

## Scenarios

### ZstdBitReader forward read

#### reads 8 bits from a single byte

1. fail
   - Expected: res.unwrap().value equals `0xA3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# byte = 0xA3 = 0b10100011
val data = make_b1(0xA3)
val r = zstd_br_init(data)
val res = zstd_br_read(r, 8)
if res.is_err():
    fail("unexpected zstd parse or reader branch")
else:
    expect(res.unwrap().value).to_equal(0xA3)
```

</details>

#### reads 4 bits LSB-first from low nibble

1. fail
   - Expected: res.unwrap().value equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# byte = 0xA3; first 4 bits LSB-first = low nibble = 0x3
val data = make_b1(0xA3)
val r = zstd_br_init(data)
val res = zstd_br_read(r, 4)
if res.is_err():
    fail("unexpected zstd parse or reader branch")
else:
    expect(res.unwrap().value).to_equal(3)
```

</details>

#### reads two consecutive 4-bit chunks

1. fail
2. fail
   - Expected: lo equals `3`
   - Expected: hi equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# byte = 0xA3 = 0b10100011; low nibble=3, high nibble=10
val data = make_b1(0xA3)
val r = zstd_br_init(data)
val r1 = zstd_br_read(r, 4)
if r1.is_err():
    fail("unexpected zstd parse or reader branch")
else:
    val lo = r1.unwrap().value
    val r2 = zstd_br_read(r1.unwrap().reader, 4)
    if r2.is_err():
        fail("unexpected zstd parse or reader branch")
    else:
        val hi = r2.unwrap().value
        expect(lo).to_equal(3)
        expect(hi).to_equal(10)
```

</details>

#### reads across byte boundary (12 bits from 2 bytes)

1. fail
   - Expected: res.unwrap().value equals `0xBCD`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# bytes = [0xCD, 0xAB]
# First 8 bits = 0xCD; next 4 bits = low nibble of 0xAB = 0xB
# But reading 12 bits at once LSB-first = 0xCD | (0xAB << 8) = 0xABCD, masked to 12 bits = 0xBCD
val data = make_b2(0xCD, 0xAB)
val r = zstd_br_init(data)
val res = zstd_br_read(r, 12)
if res.is_err():
    fail("unexpected zstd parse or reader branch")
else:
    expect(res.unwrap().value).to_equal(0xBCD)
```

</details>

#### reads little-endian u16

1. fail
   - Expected: res.unwrap().value equals `0x1234`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# bytes = [0x34, 0x12] → LE u16 = 0x1234
val data = make_b2(0x34, 0x12)
val r = zstd_br_init(data)
val res = zstd_br_read_u16(r)
if res.is_err():
    fail("unexpected zstd parse or reader branch")
else:
    expect(res.unwrap().value).to_equal(0x1234)
```

</details>

#### reads little-endian u32

1. fail
   - Expected: res.unwrap().value equals `0x12345678`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# bytes = [0x78, 0x56, 0x34, 0x12] → LE u32 = 0x12345678
val data = make_b4(0x78, 0x56, 0x34, 0x12)
val r = zstd_br_init(data)
val res = zstd_br_read_u32(r)
if res.is_err():
    fail("unexpected zstd parse or reader branch")
else:
    expect(res.unwrap().value).to_equal(0x12345678)
```

</details>

#### returns error when reading past end of data

1. fail
   - Expected: r2.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data = make_b1(0xFF)
val r = zstd_br_init(data)
# Read 8 bits successfully
val r1 = zstd_br_read(r, 8)
if r1.is_err():
    fail("unexpected zstd parse or reader branch")
else:
    # Attempt to read 1 more bit from exhausted reader
    val r2 = zstd_br_read(r1.unwrap().reader, 1)
    expect(r2.is_err()).to_equal(true)
```

</details>

### ZstdBitReader byte alignment

#### align on already-aligned reader is a no-op

1. fail
   - Expected: res.unwrap().value equals `0xAB`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# No bits consumed yet → byte-aligned; align should succeed cleanly
val data = make_b2(0xAB, 0xCD)
val r = zstd_br_init(data)
val aligned = zstd_br_align(r)
# Read a byte after align — should get 0xAB
val res = zstd_br_read(aligned, 8)
if res.is_err():
    fail("unexpected zstd parse or reader branch")
else:
    expect(res.unwrap().value).to_equal(0xAB)
```

</details>

#### align discards sub-byte bits to reach next byte boundary

1. fail
2. fail
   - Expected: r2.unwrap().value equals `0xCD`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Read 3 bits from 0b00001001 (0x09) → value=1 (low 3 bits)
# Then align; next full byte read should be 0xCD
val data = make_b2(0x09, 0xCD)
val r = zstd_br_init(data)
val r1 = zstd_br_read(r, 3)
if r1.is_err():
    fail("unexpected zstd parse or reader branch")
else:
    val aligned = zstd_br_align(r1.unwrap().reader)
    val r2 = zstd_br_read(aligned, 8)
    if r2.is_err():
        fail("unexpected zstd parse or reader branch")
    else:
        expect(r2.unwrap().value).to_equal(0xCD)
```

</details>

### ZstdBitReader read_bytes

#### reads 3 bytes as a slice

1. fail
   - Expected: rb.bytes.len() equals `3`
   - Expected: rb.bytes[0].to_i64() equals `1`
   - Expected: rb.bytes[1].to_i64() equals `2`
   - Expected: rb.bytes[2].to_i64() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data = make_b4(0x01, 0x02, 0x03, 0x04)
val r = zstd_br_init(data)
val res = zstd_br_read_bytes(r, 3)
if res.is_err():
    fail("unexpected zstd parse or reader branch")
else:
    val rb = res.unwrap()
    expect(rb.bytes.len()).to_equal(3)
    expect(rb.bytes[0].to_i64()).to_equal(1)
    expect(rb.bytes[1].to_i64()).to_equal(2)
    expect(rb.bytes[2].to_i64()).to_equal(3)
```

</details>

#### reader advances past read bytes

1. fail
2. fail
   - Expected: r2.unwrap().value equals `0xCC`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data = make_b4(0xAA, 0xBB, 0xCC, 0xDD)
val r = zstd_br_init(data)
val res = zstd_br_read_bytes(r, 2)
if res.is_err():
    fail("unexpected zstd parse or reader branch")
else:
    val r2 = zstd_br_read(res.unwrap().reader, 8)
    if r2.is_err():
        fail("unexpected zstd parse or reader branch")
    else:
        expect(r2.unwrap().value).to_equal(0xCC)
```

</details>

### ZstdRevBitReader init

#### rejects empty slice

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var empty: [u8] = []
val r = zstd_rbr_init(empty)
expect(r.is_err()).to_equal(true)
```

</details>

#### rejects slice where last byte is 0 (no sentinel)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data = make_b1(0x00)
val r = zstd_rbr_init(data)
expect(r.is_err()).to_equal(true)
```

</details>

#### accepts single byte with sentinel at bit 7

1. fail
   - Expected: r.unwrap().bits_left equals `7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# 0x80 = 0b10000000: sentinel is bit7; bits_left = 7
val data = make_b1(0x80)
val r = zstd_rbr_init(data)
if r.is_err():
    fail("unexpected zstd parse or reader branch")
else:
    expect(r.unwrap().bits_left).to_equal(7)
```

</details>

#### accepts single byte with sentinel at bit 0

1. fail
   - Expected: r.unwrap().bits_left equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# 0x01 = 0b00000001: sentinel is bit0; bits_left = 0
val data = make_b1(0x01)
val r = zstd_rbr_init(data)
if r.is_err():
    fail("unexpected zstd parse or reader branch")
else:
    expect(r.unwrap().bits_left).to_equal(0)
```

</details>

#### two-byte stream: sentinel at MSB of last byte gives 15 bits

1. fail
   - Expected: r.unwrap().bits_left equals `15`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# last byte = 0x80 = 0b10000000; sentinel at bit7 → 7 data bits in last byte
# + 8 bits in first byte = 15 total
val data = make_b2(0xFF, 0x80)
val r = zstd_rbr_init(data)
if r.is_err():
    fail("unexpected zstd parse or reader branch")
else:
    expect(r.unwrap().bits_left).to_equal(15)
```

</details>

### ZstdRevBitReader read bits

#### reads known bits from single-byte sentinel stream

1. fail
2. fail
   - Expected: res.unwrap().value equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# 0b11000001: sentinel at bit0 → 0 data bits; reading 0 bits trivially works
# Use 0b10110001 (0xB1): sentinel at bit7; data bits = bits6-0 = 0b0110001 = 0x31
# bits_left = 7; reading 3 bits MSB-first = bits6,5,4 = 0,1,1 = 2
val data = make_b1(0xB1)
val r_r = zstd_rbr_init(data)
if r_r.is_err():
    fail("unexpected zstd parse or reader branch")
else:
    val r = r_r.unwrap()
    val res = zstd_rbr_read(r, 3)
    if res.is_err():
        fail("unexpected zstd parse or reader branch")
    else:
        # bits6=0, bits5=1, bits4=1 → MSB-first = 0b011 = 3
        expect(res.unwrap().value).to_equal(3)
```

</details>

#### bits_left decrements correctly after each read

1. fail
   - Expected: r.bits_left equals `15`
2. fail
   - Expected: res1.unwrap().reader.bits_left equals `10`
3. fail
   - Expected: res2.unwrap().reader.bits_left equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data = make_b2(0xFF, 0x81)
val r_r = zstd_rbr_init(data)
if r_r.is_err():
    fail("unexpected zstd parse or reader branch")
else:
    val r = r_r.unwrap()
    # sentinel at bit7 of 0x81; bits_left = 15
    expect(r.bits_left).to_equal(15)
    val res1 = zstd_rbr_read(r, 5)
    if res1.is_err():
        fail("unexpected zstd parse or reader branch")
    else:
        expect(res1.unwrap().reader.bits_left).to_equal(10)
        val res2 = zstd_rbr_read(res1.unwrap().reader, 6)
        if res2.is_err():
            fail("unexpected zstd parse or reader branch")
        else:
            expect(res2.unwrap().reader.bits_left).to_equal(4)
```

</details>

#### returns error when reading more bits than available

1. fail
   - Expected: res.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# 0x80: bits_left = 7; try to read 8 bits
val data = make_b1(0x80)
val r_r = zstd_rbr_init(data)
if r_r.is_err():
    fail("unexpected zstd parse or reader branch")
else:
    val r = r_r.unwrap()
    val res = zstd_rbr_read(r, 8)
    expect(res.is_err()).to_equal(true)
```

</details>

### zstd_parse_magic

#### accepts valid zstd magic 0xFD2FB528 (little-endian)

1. fail
   - Expected: mr.is_skippable is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# 0xFD2FB528 in LE: bytes [0x28, 0xB5, 0x2F, 0xFD]
val data = make_b4(0x28, 0xB5, 0x2F, 0xFD)
val r = zstd_br_init(data)
val res = zstd_parse_magic(r)
if res.is_err():
    fail("unexpected zstd parse or reader branch")
else:
    val mr = res.unwrap()
    expect(mr.is_skippable).to_equal(false)
```

</details>

#### rejects wrong magic bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data = make_b4(0x00, 0x00, 0x00, 0x00)
val r = zstd_br_init(data)
val res = zstd_parse_magic(r)
expect(res.is_err()).to_equal(true)
```

</details>

#### accepts skippable frame magic (0x184D2A50, low boundary) little-endian

1. fail
   - Expected: mr.is_skippable is true
   - Expected: mr.skip_size equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# 0x184D2A50 in LE: [0x50, 0x2A, 0x4D, 0x18] + 4 skip-size bytes
val data = make_b8(0x50, 0x2A, 0x4D, 0x18, 0x00, 0x00, 0x00, 0x00)
val r = zstd_br_init(data)
val res = zstd_parse_magic(r)
if res.is_err():
    fail("unexpected zstd parse or reader branch")
else:
    val mr = res.unwrap()
    expect(mr.is_skippable).to_equal(true)
    expect(mr.skip_size).to_equal(0)
```

</details>

#### reader advances past 4 magic bytes for regular frame

1. fail
2. fail
   - Expected: next.unwrap().value equals `0xAA`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data = make_b8(0x28, 0xB5, 0x2F, 0xFD, 0xAA, 0xBB, 0xCC, 0xDD)
val r = zstd_br_init(data)
val res = zstd_parse_magic(r)
if res.is_err():
    fail("unexpected zstd parse or reader branch")
else:
    # Next byte after magic should be 0xAA
    val next = zstd_br_read(res.unwrap().reader, 8)
    if next.is_err():
        fail("unexpected zstd parse or reader branch")
    else:
        expect(next.unwrap().value).to_equal(0xAA)
```

</details>

### zstd_parse_frame_header

#### parses minimal frame header: FHD=0x00 (single-segment, no dict, no checksum, no FCS)

1. fail
   - Expected: fh.dict_id equals `0`
   - Expected: fh.has_checksum is false
   - Expected: fh.content_size equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# FHD byte = 0x00:
#   bits [7:6] = Frame_Content_Size_Flag = 0 (size not present unless single-segment)
#   bit  [5]   = Single_Segment_Flag = 0 (window descriptor present)
#   bit  [2]   = Content_Checksum_Flag = 0
#   bits [1:0] = Dictionary_ID_Flag = 0 (no dict)
# Window_Descriptor byte required since Single_Segment=0:
#   0x08 = 0b00001000 → Exponent bits[7:3] = 00001 = 1, mantissa bits[2:0] = 0
#   window_size = (1 + 0/8) * 2^(10+1) = 2048 (well within any impl limit)
# content_size = -1 (unknown)
val data = make_b2(0x00, 0x08)
val r = zstd_br_init(data)
val res = zstd_parse_frame_header(r)
if res.is_err():
    fail("unexpected zstd parse or reader branch")
else:
    val fh = res.unwrap()
    expect(fh.dict_id).to_equal(0)
    expect(fh.has_checksum).to_equal(false)
    expect(fh.content_size).to_equal(-1)
```

</details>

#### parses single-segment frame header with 1-byte FCS

1. fail
   - Expected: fh.content_size equals `10`
   - Expected: fh.dict_id equals `0`
   - Expected: fh.has_checksum is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# FHD byte = 0x20:
#   bits [7:6] = FCS_Flag = 0 (but Single_Segment=1 implies FCS present as 1 byte)
#   bit  [5]   = Single_Segment_Flag = 1 (no Window_Descriptor, FCS_Flag=0 → 1-byte FCS)
#   bit  [2]   = Checksum = 0
#   bits [1:0] = DictID = 0
# FCS byte = 0x0A → content_size = 10
val data = make_b2(0x20, 0x0A)
val r = zstd_br_init(data)
val res = zstd_parse_frame_header(r)
if res.is_err():
    fail("unexpected zstd parse or reader branch")
else:
    val fh = res.unwrap()
    expect(fh.content_size).to_equal(10)
    expect(fh.dict_id).to_equal(0)
    expect(fh.has_checksum).to_equal(false)
```

</details>

#### parses frame header with checksum flag set

1. fail
   - Expected: fh.has_checksum is true
   - Expected: fh.content_size equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# FHD = 0x24: bit2=1 (checksum), Single_Segment=1, FCS_Flag=0 → 1-byte FCS, DictID=0
# FCS byte = 0x05 → content_size = 5
val data = make_b2(0x24, 0x05)
val r = zstd_br_init(data)
val res = zstd_parse_frame_header(r)
if res.is_err():
    fail("unexpected zstd parse or reader branch")
else:
    val fh = res.unwrap()
    expect(fh.has_checksum).to_equal(true)
    expect(fh.content_size).to_equal(5)
```

</details>

### zstd_parse_block_header

#### parses raw block header (last_block=1, type=RAW, size=4)

1. fail
   - Expected: bh.last_block is true
   - Expected: bh.block_type equals `ZSTD_BLOCK_RAW`
   - Expected: bh.block_size equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Block_Header = 3 bytes LE; layout: bit0=Last_Block, bits[2:1]=Block_Type, bits[23:3]=Block_Size
# last=1, type=RAW(0), size=4 → raw = 1 | (0<<1) | (4<<3) = 1 | 32 = 33 = 0x000021
# bytes: [0x21, 0x00, 0x00]
val data = make_b3(0x21, 0x00, 0x00)
val r = zstd_br_init(data)
val res = zstd_parse_block_header(r)
if res.is_err():
    fail("unexpected zstd parse or reader branch")
else:
    val bh = res.unwrap()
    expect(bh.last_block).to_equal(true)
    expect(bh.block_type).to_equal(ZSTD_BLOCK_RAW)
    expect(bh.block_size).to_equal(4)
```

</details>

#### parses RLE block header (last_block=0, type=RLE, size=10)

1. fail
   - Expected: bh.last_block is false
   - Expected: bh.block_type equals `ZSTD_BLOCK_RLE`
   - Expected: bh.block_size equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# last=0, type=RLE(1), size=10 → raw = 0 | (1<<1) | (10<<3) = 2 | 80 = 82 = 0x000052
# bytes: [0x52, 0x00, 0x00]
val data = make_b3(0x52, 0x00, 0x00)
val r = zstd_br_init(data)
val res = zstd_parse_block_header(r)
if res.is_err():
    fail("unexpected zstd parse or reader branch")
else:
    val bh = res.unwrap()
    expect(bh.last_block).to_equal(false)
    expect(bh.block_type).to_equal(ZSTD_BLOCK_RLE)
    expect(bh.block_size).to_equal(10)
```

</details>

#### parses compressed block header

1. fail
   - Expected: bh.last_block is true
   - Expected: bh.block_type equals `ZSTD_BLOCK_COMPRESSED`
   - Expected: bh.block_size equals `7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# last=1, type=COMPRESSED(2), size=7 → raw = 1 | (2<<1) | (7<<3) = 1|4|56 = 61 = 0x00003D
# bytes: [0x3D, 0x00, 0x00]
val data = make_b3(0x3D, 0x00, 0x00)
val r = zstd_br_init(data)
val res = zstd_parse_block_header(r)
if res.is_err():
    fail("unexpected zstd parse or reader branch")
else:
    val bh = res.unwrap()
    expect(bh.last_block).to_equal(true)
    expect(bh.block_type).to_equal(ZSTD_BLOCK_COMPRESSED)
    expect(bh.block_size).to_equal(7)
```

</details>

#### parses block header with large block size

1. fail
   - Expected: bh.last_block is false
   - Expected: bh.block_type equals `ZSTD_BLOCK_RAW`
   - Expected: bh.block_size equals `131071`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# last=0, type=RAW(0), size=131071 (0x1FFFF, max for 21-bit field)
# raw = 0 | (0<<1) | (131071<<3)
# 131071 * 8 = 1048568 = 0x0FFFF8
# bytes: [0xF8, 0xFF, 0x0F]
val data = make_b3(0xF8, 0xFF, 0x0F)
val r = zstd_br_init(data)
val res = zstd_parse_block_header(r)
if res.is_err():
    fail("unexpected zstd parse or reader branch")
else:
    val bh = res.unwrap()
    expect(bh.last_block).to_equal(false)
    expect(bh.block_type).to_equal(ZSTD_BLOCK_RAW)
    expect(bh.block_size).to_equal(131071)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_sync_mut/compression/zstd/zstd_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- ZstdBitReader forward read
- ZstdBitReader byte alignment
- ZstdBitReader read_bytes
- ZstdRevBitReader init
- ZstdRevBitReader read bits
- zstd_parse_magic
- zstd_parse_frame_header
- zstd_parse_block_header

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 30 |
| Active scenarios | 30 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
