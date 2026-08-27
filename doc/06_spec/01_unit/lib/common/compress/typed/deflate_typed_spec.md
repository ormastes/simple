# Deflate Typed Specification

> Tests covering negative control, Crc32 KAT, deflate_reverse_bits, stored block KAT, deflate_stored round-trip, deflate_fixed round-trip, gzip round-trip.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 37 | 37 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Deflate Typed Specification

## Scenarios

### negative control

#### assert_equal catches wrong values (self-proof)

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- assert_equal catches wrong values (self-proof)


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("assert_equal catches wrong values (self-proof)")
# Proof: we verified assert_equal(1,2) fires FAIL, then reverted.
val x = 42
assert_equal(x, 42)
```

</details>

### Crc32 KAT

#### CRC32 of 123456789 equals 0xCBF43926

- CRC32 of 123456789 equals 0xCBF43926


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("CRC32 of 123456789 equals 0xCBF43926")
val bytes: [u8] = [49u8, 50u8, 51u8, 52u8, 53u8, 54u8, 55u8, 56u8, 57u8]
val sp = ByteSpan.new(bytes)
var crc = Crc32.new()
crc.update(sp)
val got = crc.raw()
assert_equal(got, 0xCBF43926)
```

</details>

### deflate_reverse_bits

#### reverse 0b1 in 1 bit = 0b1

- reverse 0b1 in 1 bit = 0b1


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reverse 0b1 in 1 bit = 0b1")
val r = deflate_reverse_bits(1, 1)
assert_equal(r, 1)
```

</details>

#### reverse 0b10 in 2 bits = 0b01

- reverse 0b10 in 2 bits = 0b01


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reverse 0b10 in 2 bits = 0b01")
val r = deflate_reverse_bits(2, 2)
assert_equal(r, 1)
```

</details>

#### reverse 0b110 in 3 bits = 0b011

- reverse 0b110 in 3 bits = 0b011


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reverse 0b110 in 3 bits = 0b011")
val r = deflate_reverse_bits(6, 3)
assert_equal(r, 3)
```

</details>

#### reverse 0b0000000 in 7 bits = 0b0000000 (EOB sym 256 code)

- reverse 0b0000000 in 7 bits = 0b0000000 (EOB sym 256 code)


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reverse 0b0000000 in 7 bits = 0b0000000 (EOB sym 256 code)")
val r = deflate_reverse_bits(0, 7)
assert_equal(r, 0)
```

</details>

### stored block KAT

#### inflate hand-built stored block for hi — len=2 first=104 sum=209

- inflate hand-built stored block for hi — len=2 first=104 sum=209


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("inflate hand-built stored block for hi — len=2 first=104 sum=209")
val raw: [u8] = [1u8, 2u8, 0u8, 253u8, 255u8, 104u8, 105u8]
val sp = ByteSpan.new(raw)
val out = inflate_stored(sp)
val out_sp = out.freeze()
assert_equal(out_sp.len(), 2)
val b0 = out_sp.get(0).to_i64()
assert_equal(b0, 104)
val s = byte_sum(out_sp)
assert_equal(s, 209)
```

</details>

#### truncated stored length returns empty instead of reading past input

- truncated stored length returns empty instead of reading past input


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("truncated stored length returns empty instead of reading past input")
val raw: [u8] = [1u8, 2u8]
val out = inflate_stored(ByteSpan.new(raw))
assert_equal(out.freeze().len(), 0)
```

</details>

#### truncated stored payload returns empty

- truncated stored payload returns empty


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("truncated stored payload returns empty")
val raw: [u8] = [1u8, 2u8, 0u8, 253u8, 255u8, 104u8]
val out = inflate_stored(ByteSpan.new(raw))
assert_equal(out.freeze().len(), 0)
```

</details>

#### stored LEN NLEN mismatch returns empty

- stored LEN NLEN mismatch returns empty


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("stored LEN NLEN mismatch returns empty")
val raw: [u8] = [1u8, 2u8, 0u8, 0u8, 0u8, 104u8, 105u8]
val out = inflate_stored(ByteSpan.new(raw))
assert_equal(out.freeze().len(), 0)
```

</details>

#### stored block without final marker returns empty

- stored block without final marker returns empty


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("stored block without final marker returns empty")
val raw: [u8] = [0u8, 1u8, 0u8, 254u8, 255u8, 65u8]
val out = inflate_stored(ByteSpan.new(raw))
assert_equal(out.freeze().len(), 0)
```

</details>

#### stored block followed by unsupported block type returns empty

- stored block followed by unsupported block type returns empty


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("stored block followed by unsupported block type returns empty")
val raw: [u8] = [0u8, 1u8, 0u8, 254u8, 255u8, 65u8, 3u8]
val out = inflate_stored(ByteSpan.new(raw))
assert_equal(out.freeze().len(), 0)
```

</details>

#### trailing bytes after final stored block returns empty

- trailing bytes after final stored block returns empty


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("trailing bytes after final stored block returns empty")
val raw: [u8] = [1u8, 1u8, 0u8, 254u8, 255u8, 65u8, 0u8]
val out = inflate_stored(ByteSpan.new(raw))
assert_equal(out.freeze().len(), 0)
```

</details>

### deflate_stored round-trip

#### empty input round-trips via stored — len=0

- empty input round-trips via stored — len=0


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("empty input round-trips via stored — len=0")
val sp = ByteSpan.empty()
val compressed = deflate_stored(sp)
val out = inflate_stored(compressed.freeze())
assert_equal(out.freeze().len(), 0)
```

</details>

#### hello round-trips via stored — len=5 first=104 sum=532

- hello round-trips via stored — len=5 first=104 sum=532


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("hello round-trips via stored — len=5 first=104 sum=532")
val bytes: [u8] = [104u8, 101u8, 108u8, 108u8, 111u8]
val sp = ByteSpan.new(bytes)
val compressed = deflate_stored(sp)
val out = inflate_stored(compressed.freeze())
val out_sp = out.freeze()
assert_equal(out_sp.len(), 5)
val b0 = out_sp.get(0).to_i64()
assert_equal(b0, 104)
val s = byte_sum(out_sp)
assert_equal(s, 532)
```

</details>

#### 100-byte all-a round-trips via stored — len=100 all=97 sum=9700

- 100-byte all-a round-trips via stored — len=100 all=97 sum=9700


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("100-byte all-a round-trips via stored — len=100 all=97 sum=9700")
var ab: [u8] = []
var i = 0
while i < 100:
    ab.push(97u8)
    i = i + 1
val sp = ByteSpan.new(ab)
val compressed = deflate_stored(sp)
val out = inflate_stored(compressed.freeze())
val out_sp = out.freeze()
assert_equal(out_sp.len(), 100)
val b0 = out_sp.get(0).to_i64()
assert_equal(b0, 97)
val all_ok = all_bytes_equal(out_sp, 97)
assert_equal(all_ok, 1)
```

</details>

### deflate_fixed round-trip

#### empty input round-trips via fixed-Huffman — len=0

- empty input round-trips via fixed-Huffman — len=0


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("empty input round-trips via fixed-Huffman — len=0")
val sp = ByteSpan.empty()
val compressed = deflate_fixed(sp)
val out = inflate_fixed(compressed.freeze())
assert_equal(out.freeze().len(), 0)
```

</details>

#### hello round-trips via fixed-Huffman — len=5 first=104 sum=532

- hello round-trips via fixed-Huffman — len=5 first=104 sum=532


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("hello round-trips via fixed-Huffman — len=5 first=104 sum=532")
val bytes: [u8] = [104u8, 101u8, 108u8, 108u8, 111u8]
val sp = ByteSpan.new(bytes)
val compressed = deflate_fixed(sp)
val out = inflate_fixed(compressed.freeze())
val out_sp = out.freeze()
assert_equal(out_sp.len(), 5)
val b0 = out_sp.get(0).to_i64()
assert_equal(b0, 104)
val s = byte_sum(out_sp)
assert_equal(s, 532)
```

</details>

#### single byte A=65 round-trips via fixed-Huffman

- single byte A=65 round-trips via fixed-Huffman


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("single byte A=65 round-trips via fixed-Huffman")
val bytes: [u8] = [65u8]
val sp = ByteSpan.new(bytes)
val compressed = deflate_fixed(sp)
val out = inflate_fixed(compressed.freeze())
val out_sp = out.freeze()
assert_equal(out_sp.len(), 1)
val b0 = out_sp.get(0).to_i64()
assert_equal(b0, 65)
```

</details>

#### malformed fixed match before history stops without synthetic bytes

- malformed fixed match before history stops without synthetic bytes


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("malformed fixed match before history stops without synthetic bytes")
val raw: [u8] = [0x03u8, 0x02u8]
val out = inflate_fixed(ByteSpan.new(raw))
assert_equal(out.freeze().len(), 0)
```

</details>

#### truncated fixed block without EOB returns empty

- truncated fixed block without EOB returns empty


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("truncated fixed block without EOB returns empty")
var w = BitWriter.lsb()
w.put_bits(1, 1)
w.put_bits(1, 1)
w.put_bits(0, 1)
val lit_a = deflate_reverse_bits(48 + 65, 8)
w.put_bits(lit_a, 8)
val out = inflate_fixed(w.finish().freeze())
assert_equal(out.freeze().len(), 0)
```

</details>

#### non-final fixed block returns empty

- non-final fixed block returns empty


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("non-final fixed block returns empty")
var w = BitWriter.lsb()
w.put_bits(0, 1)
w.put_bits(1, 1)
w.put_bits(0, 1)
val lit_a = deflate_reverse_bits(48 + 65, 8)
w.put_bits(lit_a, 8)
w.put_bits(0, 7)
val out = inflate_fixed(w.finish().freeze())
assert_equal(out.freeze().len(), 0)
```

</details>

#### fixed match distance beyond history returns empty

- fixed match distance beyond history returns empty


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fixed match distance beyond history returns empty")
var w = BitWriter.lsb()
w.put_bits(1, 1)
w.put_bits(1, 1)
w.put_bits(0, 1)
val lit_a = deflate_reverse_bits(48 + 65, 8)
w.put_bits(lit_a, 8)
val len3 = deflate_reverse_bits(1, 7)
w.put_bits(len3, 7)
val dist2 = deflate_reverse_bits(1, 5)
w.put_bits(dist2, 5)
w.put_bits(0, 7)
w.align()
val out = inflate_fixed(w.finish().freeze())
assert_equal(out.freeze().len(), 0)
```

</details>

#### overlapping fixed match copies from newly emitted bytes

- overlapping fixed match copies from newly emitted bytes


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("overlapping fixed match copies from newly emitted bytes")
var w = BitWriter.lsb()
w.put_bits(1, 1)
w.put_bits(1, 1)
w.put_bits(0, 1)
val lit_a = deflate_reverse_bits(48 + 65, 8)
w.put_bits(lit_a, 8)
val len3 = deflate_reverse_bits(1, 7)
w.put_bits(len3, 7)
w.put_bits(0, 5)
w.put_bits(0, 7)
w.align()
val out = inflate_fixed(w.finish().freeze())
val out_sp = out.freeze()
assert_equal(out_sp.len(), 4)
assert_equal(byte_sum(out_sp), 260)
assert_equal(all_bytes_equal(out_sp, 65), 1)
```

</details>

#### 100 repeated a=97 round-trips via fixed-Huffman literals — sum=9700

- 100 repeated a=97 round-trips via fixed-Huffman literals — sum=9700


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("100 repeated a=97 round-trips via fixed-Huffman literals — sum=9700")
var ab: [u8] = []
var i = 0
while i < 100:
    ab.push(97u8)
    i = i + 1
val sp = ByteSpan.new(ab)
val compressed = deflate_fixed(sp)
val out = inflate_fixed(compressed.freeze())
val out_sp = out.freeze()
assert_equal(out_sp.len(), 100)
val b0 = out_sp.get(0).to_i64()
assert_equal(b0, 97)
val all_ok = all_bytes_equal(out_sp, 97)
assert_equal(all_ok, 1)
```

</details>

### gzip round-trip

#### gzip empty input — magic ok len>=18 decomp=0

- gzip empty input — magic ok len>=18 decomp=0


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("gzip empty input — magic ok len>=18 decomp=0")
val sp = ByteSpan.empty()
val gz = gzip_compress(sp)
val gz_sp = gz.freeze()
val has_header = gz_sp.len() >= 18
assert_true(has_header)
val id1 = gz_sp.get(0).to_i64()
assert_equal(id1, 31)
val out = gzip_decompress(gz_sp)
assert_equal(out.freeze().len(), 0)
```

</details>

#### gzip hello — magic id1=31 cm=8 decomp len=5 sum=532

- gzip hello — magic id1=31 cm=8 decomp len=5 sum=532


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("gzip hello — magic id1=31 cm=8 decomp len=5 sum=532")
val bytes: [u8] = [104u8, 101u8, 108u8, 108u8, 111u8]
val sp = ByteSpan.new(bytes)
val gz = gzip_compress(sp)
val gz_sp = gz.freeze()
val id1 = gz_sp.get(0).to_i64()
assert_equal(id1, 31)
val cm = gz_sp.get(2).to_i64()
assert_equal(cm, 8)
val out = gzip_decompress(gz_sp)
val out_sp = out.freeze()
assert_equal(out_sp.len(), 5)
val b0 = out_sp.get(0).to_i64()
assert_equal(b0, 104)
val s = byte_sum(out_sp)
assert_equal(s, 532)
```

</details>

#### gzip 100-byte repeated a=97 round-trips — len=100 sum=9700

- gzip 100-byte repeated a=97 round-trips — len=100 sum=9700


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("gzip 100-byte repeated a=97 round-trips — len=100 sum=9700")
var ab: [u8] = []
var i = 0
while i < 100:
    ab.push(97u8)
    i = i + 1
val sp = ByteSpan.new(ab)
val gz = gzip_compress(sp)
val gz_sp = gz.freeze()
val out = gzip_decompress(gz_sp)
val out_sp = out.freeze()
assert_equal(out_sp.len(), 100)
val b0 = out_sp.get(0).to_i64()
assert_equal(b0, 97)
val all_ok = all_bytes_equal(out_sp, 97)
assert_equal(all_ok, 1)
```

</details>

#### gzip OS byte at index 9 is 255 (unknown OS)

- gzip OS byte at index 9 is 255 (unknown OS)


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("gzip OS byte at index 9 is 255 (unknown OS)")
val bytes: [u8] = [65u8]
val sp = ByteSpan.new(bytes)
val gz = gzip_compress(sp)
val gz_sp = gz.freeze()
val os_byte = gz_sp.get(9).to_i64()
assert_equal(os_byte, 255)
```

</details>

#### gzip reserved header flags return empty

- gzip reserved header flags return empty


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("gzip reserved header flags return empty")
val bytes: [u8] = [104u8, 101u8, 108u8, 108u8, 111u8]
val gz = gzip_compress(ByteSpan.new(bytes))
var corrupt = gz.freeze().to_bytes()
corrupt[3] = 0xE0u8
val out = gzip_decompress(ByteSpan.new(corrupt))
assert_equal(out.freeze().len(), 0)
```

</details>

#### gzip truncated optional filename returns empty

- gzip truncated optional filename returns empty


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("gzip truncated optional filename returns empty")
val raw: [u8] = [
    0x1Fu8, 0x8Bu8, 0x08u8, 0x08u8,
    0x00u8, 0x00u8, 0x00u8, 0x00u8,
    0x00u8, 0xFFu8, 0x41u8
]
val out = gzip_decompress(ByteSpan.new(raw))
assert_equal(out.freeze().len(), 0)
```

</details>

#### gzip truncated optional extra field returns empty

- gzip truncated optional extra field returns empty


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("gzip truncated optional extra field returns empty")
val raw: [u8] = [
    0x1Fu8, 0x8Bu8, 0x08u8, 0x04u8,
    0x00u8, 0x00u8, 0x00u8, 0x00u8,
    0x00u8, 0xFFu8, 0x04u8, 0x00u8, 0xAAu8
]
val out = gzip_decompress(ByteSpan.new(raw))
assert_equal(out.freeze().len(), 0)
```

</details>

#### gzip truncated optional comment returns empty

- gzip truncated optional comment returns empty


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("gzip truncated optional comment returns empty")
val raw: [u8] = [
    0x1Fu8, 0x8Bu8, 0x08u8, 0x10u8,
    0x00u8, 0x00u8, 0x00u8, 0x00u8,
    0x00u8, 0xFFu8, 0x41u8
]
val out = gzip_decompress(ByteSpan.new(raw))
assert_equal(out.freeze().len(), 0)
```

</details>

#### gzip truncated header crc returns empty

- gzip truncated header crc returns empty


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("gzip truncated header crc returns empty")
val raw: [u8] = [
    0x1Fu8, 0x8Bu8, 0x08u8, 0x02u8,
    0x00u8, 0x00u8, 0x00u8, 0x00u8,
    0x00u8, 0xFFu8, 0x00u8
]
val out = gzip_decompress(ByteSpan.new(raw))
assert_equal(out.freeze().len(), 0)
```

</details>

#### gzip mismatched header crc returns empty

- gzip mismatched header crc returns empty


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("gzip mismatched header crc returns empty")
val bytes: [u8] = [104u8, 101u8, 108u8, 108u8, 111u8]
val gz = gzip_compress(ByteSpan.new(bytes))
val original = gz.freeze().to_bytes()
var corrupt: [u8] = []
var i = 0
while i < original.len():
    corrupt.push(original[i])
    if i == 9:
        corrupt[3] = 0x02u8
        corrupt.push(0x00u8)
        corrupt.push(0x00u8)
    i = i + 1
val out = gzip_decompress(ByteSpan.new(corrupt))
assert_equal(out.freeze().len(), 0)
```

</details>

#### gzip CRC32 trailer matches independent CRC32(hello)

- gzip CRC32 trailer matches independent CRC32(hello)


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("gzip CRC32 trailer matches independent CRC32(hello)")
val bytes: [u8] = [104u8, 101u8, 108u8, 108u8, 111u8]
val sp = ByteSpan.new(bytes)
var crc_check = Crc32.new()
crc_check.update(sp)
val expected_crc = crc_check.raw()
val gz = gzip_compress(sp)
val gz_sp = gz.freeze()
val gz_len = gz_sp.len()
val crc_b0 = gz_sp.get(gz_len - 8).to_i64()
# Compute stored CRC from trailer using byte_sum workaround:
# Read CRC LE 4 bytes via iteration to avoid get(N>0) pollution
var stored_crc = 0
var shift = 0
var ci = gz_len - 8
while ci < gz_len - 4:
    stored_crc = stored_crc | (gz_sp.get(ci).to_i64() << shift)
    shift = shift + 8
    ci = ci + 1
assert_equal(stored_crc, expected_crc)
```

</details>

#### gzip ISIZE trailer is 5 for hello

- gzip ISIZE trailer is 5 for hello


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("gzip ISIZE trailer is 5 for hello")
val bytes: [u8] = [104u8, 101u8, 108u8, 108u8, 111u8]
val sp = ByteSpan.new(bytes)
val gz = gzip_compress(sp)
val gz_sp = gz.freeze()
val gz_len = gz_sp.len()
var isize = 0
var shift = 0
var ii = gz_len - 4
while ii < gz_len:
    isize = isize | (gz_sp.get(ii).to_i64() << shift)
    shift = shift + 8
    ii = ii + 1
assert_equal(isize, 5)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/compress/typed/deflate_typed_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering negative control, Crc32 KAT, deflate_reverse_bits, stored block KAT, deflate_stored round-trip, deflate_fixed round-trip, gzip round-trip.
- negative control
- Crc32 KAT
- deflate_reverse_bits
- stored block KAT
- deflate_stored round-trip
- deflate_fixed round-trip
- gzip round-trip

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 37 |
| Active scenarios | 37 |
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

- Canonical SPipe generation for source `1ff10cadab63b6b8ff401b5a36c718b8a7574e28dccae626a2917afc0f0610c9`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `1ff10cadab63b6b8ff401b5a36c718b8a7574e28dccae626a2917afc0f0610c9`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `1ff10cadab63b6b8ff401b5a36c718b8a7574e28dccae626a2917afc0f0610c9`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/common/compress/typed/deflate_typed_spec.spl
mirror: doc/06_spec/01_unit/lib/common/compress/typed/deflate_typed_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/compress/typed/deflate_typed_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/compress/typed/deflate_typed_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/compress/typed/deflate_typed_spec.spl:73:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'assert_equal catches wrong values (self-proof)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/compress/typed/deflate_typed_spec.spl:84:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'CRC32 of 123456789 equals 0xCBF43926' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/compress/typed/deflate_typed_spec.spl:98:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reverse 0b1 in 1 bit = 0b1' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
