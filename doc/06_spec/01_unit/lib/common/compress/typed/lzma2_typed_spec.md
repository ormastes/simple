# Lzma2 Typed Specification

> Tests covering lzma2_typed codec.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 49 | 49 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Lzma2 Typed Specification

## Scenarios

### lzma2_typed codec

#### negative control

#### 1+1==2 proves runner fires assertions

- 1+1==2 proves runner fires assertions


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("1+1==2 proves runner fires assertions")
assert_equal(1 + 1, 2)
```

</details>

#### LZMA2 uncompressed round-trip: empty

#### empty input compresses to single end-marker byte

- empty input compresses to single end-marker byte


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("empty input compresses to single end-marker byte")
val input = ByteSpan.empty()
val compressed = lzma2_compress_uncompressed(input)
# Must be exactly [0x00]
assert_equal(compressed.len(), 1)
assert_equal(compressed.get(0).to_i64(), 0x00)
```

</details>

#### empty compress then decompress is empty

- empty compress then decompress is empty


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("empty compress then decompress is empty")
val input = ByteSpan.empty()
val compressed = lzma2_compress_uncompressed(input)
val recovered = lzma2_decompress(compressed)
assert_true(recovered.is_empty())
```

</details>

#### LZMA2 uncompressed round-trip: short ASCII

#### Hello compresses and decompresses correctly

- Hello compresses and decompresses correctly


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Hello compresses and decompresses correctly")
val input = span_from_text("Hello")
val compressed = lzma2_compress_uncompressed(input)
val recovered = lzma2_decompress(compressed)
val same = spans_equal(input, recovered)
assert_true(same)
```

</details>

#### Hello World round-trip

- Hello World round-trip


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Hello World round-trip")
val input = span_from_text("Hello, World!")
val compressed = lzma2_compress_uncompressed(input)
val recovered = lzma2_decompress(compressed)
val same = spans_equal(input, recovered)
assert_true(same)
```

</details>

#### LZMA2 uncompressed round-trip: binary data

#### all-zero 256 bytes round-trip

- all-zero 256 bytes round-trip


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("all-zero 256 bytes round-trip")
var raw: [u8] = []
var i = 0
while i < 256:
    raw.push(0x00u8)
    i = i + 1
val input = ByteSpan.new(raw)
val compressed = lzma2_compress_uncompressed(input)
val recovered = lzma2_decompress(compressed)
val same = spans_equal(input, recovered)
assert_true(same)
```

</details>

#### byte ramp 0..127 round-trip

- byte ramp 0..127 round-trip


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("byte ramp 0..127 round-trip")
var raw: [u8] = []
var i = 0
while i < 128:
    raw.push(i.to_u8())
    i = i + 1
val input = ByteSpan.new(raw)
val compressed = lzma2_compress_uncompressed(input)
val recovered = lzma2_decompress(compressed)
val same = spans_equal(input, recovered)
assert_true(same)
```

</details>

#### LZMA2 chunk layout interop

#### single-byte A: control=0x01, size_field=0x0000, payload=0x41

- single-byte A: control=0x01, size_field=0x0000, payload=0x41


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("single-byte A: control=0x01, size_field=0x0000, payload=0x41")
# 'A' = 0x41; chunk_sz=1, sz_field=0; big-endian: 0x00 0x00
# Expected bytes: [0x01, 0x00, 0x00, 0x41, 0x00]
#   ctrl=0x01 (first uncompressed), sz_hi=0x00, sz_lo=0x00, 'A', end=0x00
var raw: [u8] = [0x41u8]
val input = ByteSpan.new(raw)
val compressed = lzma2_compress_uncompressed(input)
assert_equal(compressed.len(), 5)
assert_equal(compressed.get(0).to_i64(), 0x01)
assert_equal(compressed.get(1).to_i64(), 0x00)
assert_equal(compressed.get(2).to_i64(), 0x00)
assert_equal(compressed.get(3).to_i64(), 0x41)
assert_equal(compressed.get(4).to_i64(), 0x00)
```

</details>

#### known LZMA2 uncompressed chunk sequence decodes correctly

- known LZMA2 uncompressed chunk sequence decodes correctly


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("known LZMA2 uncompressed chunk sequence decodes correctly")
# Manually constructed LZMA2 uncompressed chunk for bytes [0x48, 0x69] = "Hi"
# [0x01, 0x00, 0x01, 0x48, 0x69, 0x00]
#   ctrl=0x01, sz_hi=0x00, sz_lo=0x01 → chunk_sz=2, payload=Hi, end=0x00
var chunk: [u8] = [0x01u8, 0x00u8, 0x01u8, 0x48u8, 0x69u8, 0x00u8]
val input_span = ByteSpan.new(chunk)
val decoded = lzma2_decompress(input_span)
assert_equal(decoded.len(), 2)
assert_equal(decoded.get(0).to_i64(), 0x48)
assert_equal(decoded.get(1).to_i64(), 0x69)
```

</details>

#### two uncompressed chunks decode to concatenated payload

- two uncompressed chunks decode to concatenated payload


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("two uncompressed chunks decode to concatenated payload")
# Two chunks: [0x01, 0x00, 0x00, 0xAA] + [0x02, 0x00, 0x00, 0xBB] + [0x00]
var chunk: [u8] = [0x01u8, 0x00u8, 0x00u8, 0xAAu8,
                    0x02u8, 0x00u8, 0x00u8, 0xBBu8,
                    0x00u8]
val input_span = ByteSpan.new(chunk)
val decoded = lzma2_decompress(input_span)
assert_equal(decoded.len(), 2)
assert_equal(decoded.get(0).to_i64(), 0xAA)
assert_equal(decoded.get(1).to_i64(), 0xBB)
```

</details>

#### truncated uncompressed chunk decodes to empty

- truncated uncompressed chunk decodes to empty


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("truncated uncompressed chunk decodes to empty")
var chunk: [u8] = [0x01u8, 0x00u8, 0x02u8, 0x41u8]
val decoded = lzma2_decompress(ByteSpan.new(chunk))
assert_true(decoded.is_empty())
```

</details>

#### unknown control after payload decodes to empty

- unknown control after payload decodes to empty


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("unknown control after payload decodes to empty")
var chunk: [u8] = [0x01u8, 0x00u8, 0x00u8, 0x41u8, 0xFFu8]
val decoded = lzma2_decompress(ByteSpan.new(chunk))
assert_true(decoded.is_empty())
```

</details>

#### missing end marker decodes to empty

- missing end marker decodes to empty


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("missing end marker decodes to empty")
var chunk: [u8] = [0x01u8, 0x00u8, 0x00u8, 0x41u8]
val decoded = lzma2_decompress(ByteSpan.new(chunk))
assert_true(decoded.is_empty())
```

</details>

#### trailing bytes after end marker decode to empty

- trailing bytes after end marker decode to empty


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("trailing bytes after end marker decode to empty")
var chunk: [u8] = [0x00u8, 0x41u8]
val decoded = lzma2_decompress(ByteSpan.new(chunk))
assert_true(decoded.is_empty())
```

</details>

#### first chunk without dictionary reset decodes to empty

- first chunk without dictionary reset decodes to empty


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("first chunk without dictionary reset decodes to empty")
var chunk: [u8] = [0x02u8, 0x00u8, 0x00u8, 0x41u8, 0x00u8]
val decoded = lzma2_decompress(ByteSpan.new(chunk))
assert_true(decoded.is_empty())
```

</details>

#### XZ frame magic

#### xz_header_magic returns 6-byte FD377A585A00

- xz_header_magic returns 6-byte FD377A585A00


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("xz_header_magic returns 6-byte FD377A585A00")
val magic = xz_header_magic()
assert_equal(magic.len(), 6)
assert_equal(magic[0].to_i64(), 0xFD)
assert_equal(magic[1].to_i64(), 0x37)
assert_equal(magic[2].to_i64(), 0x7A)
assert_equal(magic[3].to_i64(), 0x58)
assert_equal(magic[4].to_i64(), 0x5A)
assert_equal(magic[5].to_i64(), 0x00)
```

</details>

#### xz_footer_magic returns 2-byte 595A

- xz_footer_magic returns 2-byte 595A


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("xz_footer_magic returns 2-byte 595A")
val magic = xz_footer_magic()
assert_equal(magic.len(), 2)
assert_equal(magic[0].to_i64(), 0x59)
assert_equal(magic[1].to_i64(), 0x5A)
```

</details>

#### xz_encode output starts with XZ header magic

- xz_encode output starts with XZ header magic


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("xz_encode output starts with XZ header magic")
val input = span_from_text("Hi")
val frame = xz_encode(input)
assert_true(frame.len() > 8)
assert_equal(frame.get(0).to_i64(), 0xFD)
assert_equal(frame.get(1).to_i64(), 0x37)
assert_equal(frame.get(2).to_i64(), 0x7A)
assert_equal(frame.get(3).to_i64(), 0x58)
assert_equal(frame.get(4).to_i64(), 0x5A)
assert_equal(frame.get(5).to_i64(), 0x00)
```

</details>

#### xz_encode output ends with XZ footer magic 595A

- xz_encode output ends with XZ footer magic 595A


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("xz_encode output ends with XZ footer magic 595A")
val input = span_from_text("Hi")
val frame = xz_encode(input)
val n = frame.len()
assert_equal(frame.get(n - 2).to_i64(), 0x59)
assert_equal(frame.get(n - 1).to_i64(), 0x5A)
```

</details>

#### xz_encode footer CRC covers backward size and stream flags

- xz_encode footer CRC covers backward size and stream flags


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("xz_encode footer CRC covers backward size and stream flags")
val input = span_from_text("Hi")
val frame = xz_encode(input)
val n = frame.len()
val footer_start = n - 12
val footer_content = frame.slice(footer_start + 4, 6)
var crc = Crc32.new()
crc.update(footer_content)
val raw = crc.raw()
assert_equal(frame.get(footer_start).to_i64(), raw & 0xFF)
assert_equal(frame.get(footer_start + 1).to_i64(), (raw >> 8) & 0xFF)
assert_equal(frame.get(footer_start + 2).to_i64(), (raw >> 16) & 0xFF)
assert_equal(frame.get(footer_start + 3).to_i64(), (raw >> 24) & 0xFF)
```

</details>

#### xz_decode_check_magic passes for xz_encode output

- xz_decode_check_magic passes for xz_encode output


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("xz_decode_check_magic passes for xz_encode output")
val input = span_from_text("Hello")
val frame = xz_encode(input)
val ok = xz_decode_check_magic(frame)
assert_true(ok)
```

</details>

#### xz_decode_check_magic fails for garbage

- xz_decode_check_magic fails for garbage


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("xz_decode_check_magic fails for garbage")
var bad: [u8] = [0x00u8, 0x01u8, 0x02u8, 0x03u8, 0x04u8, 0x05u8, 0x06u8, 0x07u8]
val bad_span = ByteSpan.new(bad)
val ok = xz_decode_check_magic(bad_span)
assert_equal(ok, false)
```

</details>

#### XZ encode/decode round-trip

#### empty input round-trip

- empty input round-trip


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("empty input round-trip")
val input = ByteSpan.empty()
val frame = xz_encode(input)
val recovered = xz_decode(frame)
assert_true(recovered.is_empty())
```

</details>

#### Hello round-trip

- Hello round-trip


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Hello round-trip")
val input = span_from_text("Hello")
val frame = xz_encode(input)
val recovered = xz_decode(frame)
val same = spans_equal(input, recovered)
assert_true(same)
```

</details>

#### Hello World round-trip

- Hello World round-trip


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Hello World round-trip")
val input = span_from_text("Hello, World!")
val frame = xz_encode(input)
val recovered = xz_decode(frame)
val same = spans_equal(input, recovered)
assert_true(same)
```

</details>

#### binary byte ramp 0..63 round-trip

- binary byte ramp 0..63 round-trip


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("binary byte ramp 0..63 round-trip")
var raw: [u8] = []
var i = 0
while i < 64:
    raw.push(i.to_u8())
    i = i + 1
val input = ByteSpan.new(raw)
val frame = xz_encode(input)
val recovered = xz_decode(frame)
val same = spans_equal(input, recovered)
assert_true(same)
```

</details>

#### non-none XZ stream flags decode to empty

- non-none XZ stream flags decode to empty


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("non-none XZ stream flags decode to empty")
val input = span_from_text("Hi")
val frame = xz_encode(input)
var bad = frame.to_bytes()
bad[7] = 0x01u8
val recovered = xz_decode(ByteSpan.new(bad))
assert_true(recovered.is_empty())
```

</details>

#### corrupt XZ stream flag CRC decodes to empty

- corrupt XZ stream flag CRC decodes to empty


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("corrupt XZ stream flag CRC decodes to empty")
val input = span_from_text("Hi")
val frame = xz_encode(input)
var bad = frame.to_bytes()
bad[8] = 0x00u8
val recovered = xz_decode(ByteSpan.new(bad))
assert_true(recovered.is_empty())
```

</details>

#### corrupt XZ block header CRC decodes to empty

- corrupt XZ block header CRC decodes to empty


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("corrupt XZ block header CRC decodes to empty")
val input = span_from_text("Hi")
val frame = xz_encode(input)
var bad = frame.to_bytes()
bad[20] = 0x00u8
val recovered = xz_decode(ByteSpan.new(bad))
assert_true(recovered.is_empty())
```

</details>

#### unsupported XZ block filter id decodes to empty

- unsupported XZ block filter id decodes to empty


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("unsupported XZ block filter id decodes to empty")
val input = span_from_text("Hi")
val frame = xz_encode(input)
var bad = frame.to_bytes()
bad[14] = 0x22u8
val bad_span = ByteSpan.new(bad)
val bh_content = bad_span.slice(12, 8)
var crc = Crc32.new()
crc.update(bh_content)
val raw = crc.raw()
bad[20] = (raw & 0xFF).to_u8()
bad[21] = ((raw >> 8) & 0xFF).to_u8()
bad[22] = ((raw >> 16) & 0xFF).to_u8()
bad[23] = ((raw >> 24) & 0xFF).to_u8()
val recovered = xz_decode(ByteSpan.new(bad))
assert_true(recovered.is_empty())
```

</details>

#### corrupt XZ index CRC decodes to empty

- corrupt XZ index CRC decodes to empty


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("corrupt XZ index CRC decodes to empty")
val input = span_from_text("Hi")
val frame = xz_encode(input)
var bad = frame.to_bytes()
val crc_byte = bad.len() - 16
bad[crc_byte] = 0x00u8
val recovered = xz_decode(ByteSpan.new(bad))
assert_true(recovered.is_empty())
```

</details>

#### corrupt XZ footer CRC decodes to empty

- corrupt XZ footer CRC decodes to empty


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("corrupt XZ footer CRC decodes to empty")
val input = span_from_text("Hi")
val frame = xz_encode(input)
var bad = frame.to_bytes()
val footer_start = bad.len() - 12
bad[footer_start] = (bad[footer_start].to_i64() ^ 0xFF).to_u8()
val recovered = xz_decode(ByteSpan.new(bad))
assert_true(recovered.is_empty())
```

</details>

#### corrupt XZ footer magic decodes to empty

- corrupt XZ footer magic decodes to empty


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("corrupt XZ footer magic decodes to empty")
val input = span_from_text("Hi")
val frame = xz_encode(input)
var bad = frame.to_bytes()
bad[bad.len() - 1] = 0x00u8
val recovered = xz_decode(ByteSpan.new(bad))
assert_true(recovered.is_empty())
```

</details>

#### unsupported XZ index indicator decodes to empty

- unsupported XZ index indicator decodes to empty


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("unsupported XZ index indicator decodes to empty")
val input = span_from_text("Hi")
val frame = xz_encode(input)
var bad = frame.to_bytes()
val footer_start = bad.len() - 12
val bw0 = bad[footer_start + 4].to_i64()
val bw1 = bad[footer_start + 5].to_i64()
val bw2 = bad[footer_start + 6].to_i64()
val bw3 = bad[footer_start + 7].to_i64()
val backward_sz = bw0 | (bw1 << 8) | (bw2 << 16) | (bw3 << 24)
val index_total = (backward_sz + 1) * 4
val index_start = footer_start - index_total
val index_content_len = index_total - 4
bad[index_start] = 0x01u8
val bad_span = ByteSpan.new(bad)
val index_content = bad_span.slice(index_start, index_content_len)
var crc = Crc32.new()
crc.update(index_content)
val raw = crc.raw()
val crc_start = index_start + index_content_len
bad[crc_start] = (raw & 0xFF).to_u8()
bad[crc_start + 1] = ((raw >> 8) & 0xFF).to_u8()
bad[crc_start + 2] = ((raw >> 16) & 0xFF).to_u8()
bad[crc_start + 3] = ((raw >> 24) & 0xFF).to_u8()
val recovered = xz_decode(ByteSpan.new(bad))
assert_true(recovered.is_empty())
```

</details>

#### mismatched XZ index uncompressed size decodes to empty

- mismatched XZ index uncompressed size decodes to empty


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("mismatched XZ index uncompressed size decodes to empty")
val input = span_from_text("Hi")
val frame = xz_encode(input)
var bad = frame.to_bytes()
val footer_start = bad.len() - 12
val bw0 = bad[footer_start + 4].to_i64()
val bw1 = bad[footer_start + 5].to_i64()
val bw2 = bad[footer_start + 6].to_i64()
val bw3 = bad[footer_start + 7].to_i64()
val backward_sz = bw0 | (bw1 << 8) | (bw2 << 16) | (bw3 << 24)
val index_total = (backward_sz + 1) * 4
val index_start = footer_start - index_total
val index_content_len = index_total - 4
bad[index_start + 3] = 0x03u8
val bad_span = ByteSpan.new(bad)
val index_content = bad_span.slice(index_start, index_content_len)
var crc = Crc32.new()
crc.update(index_content)
val raw = crc.raw()
val crc_start = index_start + index_content_len
bad[crc_start] = (raw & 0xFF).to_u8()
bad[crc_start + 1] = ((raw >> 8) & 0xFF).to_u8()
bad[crc_start + 2] = ((raw >> 16) & 0xFF).to_u8()
bad[crc_start + 3] = ((raw >> 24) & 0xFF).to_u8()
val recovered = xz_decode(ByteSpan.new(bad))
assert_true(recovered.is_empty())
```

</details>

#### RangeCoder probability update

#### rc_prob_update bit=0 increases probability (toward 2048)

- rc_prob_update bit=0 increases probability (toward 2048)


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rc_prob_update bit=0 increases probability (toward 2048)")
val p = rc_prob_init()
val p2 = rc_prob_update(p, 0)
val increased = p2 > p
assert_true(increased)
```

</details>

#### rc_prob_update bit=1 decreases probability (toward 0)

- rc_prob_update bit=1 decreases probability (toward 0)


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rc_prob_update bit=1 decreases probability (toward 0)")
val p = rc_prob_init()
val p2 = rc_prob_update(p, 1)
val decreased = p2 < p
assert_true(decreased)
```

</details>

#### rc_prob_update converges toward 2048 for all-zero bits

- rc_prob_update converges toward 2048 for all-zero bits


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rc_prob_update converges toward 2048 for all-zero bits")
var p = rc_prob_init()
var i = 0
while i < 10:
    p = rc_prob_update(p, 0)
    i = i + 1
val gt_init = p > rc_prob_init()
assert_true(gt_init)
```

</details>

#### rc_prob_update converges toward 0 for all-one bits

- rc_prob_update converges toward 0 for all-one bits


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rc_prob_update converges toward 0 for all-one bits")
var p = rc_prob_init()
var i = 0
while i < 10:
    p = rc_prob_update(p, 1)
    i = i + 1
val lt_init = p < rc_prob_init()
assert_true(lt_init)
```

</details>

#### RangeCoder bit round-trip

#### single bit 0 round-trip

- single bit 0 round-trip


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("single bit 0 round-trip")
var bits: [i64] = [0]
val encoded = rc_encode_bits(bits, rc_prob_init())
val decoded = rc_decode_bits(encoded, 1, rc_prob_init())
assert_equal(decoded.len(), 1)
assert_equal(decoded[0], 0)
```

</details>

#### single bit 1 round-trip

- single bit 1 round-trip


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("single bit 1 round-trip")
var bits: [i64] = [1]
val encoded = rc_encode_bits(bits, rc_prob_init())
val decoded = rc_decode_bits(encoded, 1, rc_prob_init())
assert_equal(decoded.len(), 1)
assert_equal(decoded[0], 1)
```

</details>

#### alternating bits 0,1,0,1,0,1 round-trip

- alternating bits 0,1,0,1,0,1 round-trip


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("alternating bits 0,1,0,1,0,1 round-trip")
var bits: [i64] = [0, 1, 0, 1, 0, 1]
val encoded = rc_encode_bits(bits, rc_prob_init())
val decoded = rc_decode_bits(encoded, 6, rc_prob_init())
val same = ints_equal(decoded, bits)
assert_true(same)
```

</details>

#### all-zero 8 bits round-trip

- all-zero 8 bits round-trip


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("all-zero 8 bits round-trip")
var bits: [i64] = [0, 0, 0, 0, 0, 0, 0, 0]
val encoded = rc_encode_bits(bits, rc_prob_init())
val decoded = rc_decode_bits(encoded, 8, rc_prob_init())
val same = ints_equal(decoded, bits)
assert_true(same)
```

</details>

#### all-one 8 bits round-trip

- all-one 8 bits round-trip


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("all-one 8 bits round-trip")
var bits: [i64] = [1, 1, 1, 1, 1, 1, 1, 1]
val encoded = rc_encode_bits(bits, rc_prob_init())
val decoded = rc_decode_bits(encoded, 8, rc_prob_init())
val same = ints_equal(decoded, bits)
assert_true(same)
```

</details>

#### mixed 8-bit sequence round-trip

- mixed 8-bit sequence round-trip


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("mixed 8-bit sequence round-trip")
# NOTE: The simplified range coder (no carry-propagation cache) is
# correct for sequences up to 8 bits with evolving probability.
# Longer sequences require full LZMA carry propagation — deferred to
# doc/08_tracking/bug/lzma_full_range_model_deferred_2026-06-15.md
var bits: [i64] = [1, 0, 1, 1, 0, 0, 1, 0]
val encoded = rc_encode_bits(bits, rc_prob_init())
val decoded = rc_decode_bits(encoded, 8, rc_prob_init())
val same = ints_equal(decoded, bits)
assert_true(same)
```

</details>

#### invalid initial probability fails closed before encoding

- invalid initial probability fails closed before encoding


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("invalid initial probability fails closed before encoding")
var bits: [i64] = [0]
val encoded = rc_encode_bits(bits, 2048)
assert_true(encoded.is_empty())
```

</details>

#### invalid bit value fails closed before encoding

- invalid bit value fails closed before encoding


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("invalid bit value fails closed before encoding")
var bits: [i64] = [2]
val encoded = rc_encode_bits(bits, rc_prob_init())
assert_true(encoded.is_empty())
```

</details>

#### invalid initial probability fails closed before decoding

- invalid initial probability fails closed before decoding


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("invalid initial probability fails closed before decoding")
var raw: [u8] = [0x00u8, 0x00u8, 0x00u8, 0x00u8]
val decoded = rc_decode_bits(ByteSpan.new(raw), 1, 2048)
assert_equal(decoded.len(), 0)
```

</details>

#### negative decode count fails closed

- negative decode count fails closed


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("negative decode count fails closed")
var raw: [u8] = [0x00u8, 0x00u8, 0x00u8, 0x00u8]
val decoded = rc_decode_bits(ByteSpan.new(raw), -1, rc_prob_init())
assert_equal(decoded.len(), 0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/compress/typed/lzma2_typed_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering lzma2_typed codec.
- lzma2_typed codec

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

- Canonical SPipe generation for source `92757255abe3ac624c13ccd8e1da84f0a37c3588692ea9c194274bf56a199526`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `92757255abe3ac624c13ccd8e1da84f0a37c3588692ea9c194274bf56a199526`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `92757255abe3ac624c13ccd8e1da84f0a37c3588692ea9c194274bf56a199526`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/common/compress/typed/lzma2_typed_spec.spl
mirror: doc/06_spec/01_unit/lib/common/compress/typed/lzma2_typed_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/compress/typed/lzma2_typed_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/compress/typed/lzma2_typed_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/compress/typed/lzma2_typed_spec.spl:78:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario '1+1==2 proves runner fires assertions' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/compress/typed/lzma2_typed_spec.spl:88:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'empty input compresses to single end-marker byte' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/compress/typed/lzma2_typed_spec.spl:97:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'empty compress then decompress is empty' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
