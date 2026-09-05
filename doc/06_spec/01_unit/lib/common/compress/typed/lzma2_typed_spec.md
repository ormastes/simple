# Lzma2 Typed Specification

> <details>

<!-- sdn-diagram:id=lzma2_typed_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=lzma2_typed_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

lzma2_typed_spec -> std
lzma2_typed_spec -> lib
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=lzma2_typed_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 30 | 30 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Lzma2 Typed Specification

## Scenarios

### lzma2_typed codec

#### negative control

#### 1+1==2 proves runner fires assertions

- assert equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
assert_equal(1 + 1, 2)
```

</details>

#### LZMA2 uncompressed round-trip: empty

#### empty input compresses to single end-marker byte

- assert equal
- assert equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val input = ByteSpan.empty()
val compressed = lzma2_compress_uncompressed(input)
# Must be exactly [0x00]
assert_equal(compressed.len(), 1)
assert_equal(compressed.get(0).to_i64(), 0x00)
```

</details>

#### empty compress then decompress is empty

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val input = ByteSpan.empty()
val compressed = lzma2_compress_uncompressed(input)
val recovered = lzma2_decompress(compressed)
assert_true(recovered.is_empty())
```

</details>

#### LZMA2 uncompressed round-trip: short ASCII

#### Hello compresses and decompresses correctly

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val input = span_from_text("Hello")
val compressed = lzma2_compress_uncompressed(input)
val recovered = lzma2_decompress(compressed)
val same = spans_equal(input, recovered)
assert_true(same)
```

</details>

#### Hello World round-trip

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val input = span_from_text("Hello, World!")
val compressed = lzma2_compress_uncompressed(input)
val recovered = lzma2_decompress(compressed)
val same = spans_equal(input, recovered)
assert_true(same)
```

</details>

#### LZMA2 uncompressed round-trip: binary data

#### all-zero 256 bytes round-trip

- raw push
- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

- raw push
- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

- assert equal
- assert equal
- assert equal
- assert equal
- assert equal
- assert equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

- assert equal
- assert equal
- assert equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

- assert equal
- assert equal
- assert equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

#### XZ frame magic

#### xz_header_magic returns 6-byte FD377A585A00

- assert equal
- assert equal
- assert equal
- assert equal
- assert equal
- assert equal
- assert equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

- assert equal
- assert equal
- assert equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val magic = xz_footer_magic()
assert_equal(magic.len(), 2)
assert_equal(magic[0].to_i64(), 0x59)
assert_equal(magic[1].to_i64(), 0x5A)
```

</details>

#### xz_encode output starts with XZ header magic

- assert true
- assert equal
- assert equal
- assert equal
- assert equal
- assert equal
- assert equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

- assert equal
- assert equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val input = span_from_text("Hi")
val frame = xz_encode(input)
val n = frame.len()
assert_equal(frame.get(n - 2).to_i64(), 0x59)
assert_equal(frame.get(n - 1).to_i64(), 0x5A)
```

</details>

#### xz_decode_check_magic passes for xz_encode output

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val input = span_from_text("Hello")
val frame = xz_encode(input)
val ok = xz_decode_check_magic(frame)
assert_true(ok)
```

</details>

#### xz_decode_check_magic fails for garbage

- assert equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var bad: [u8] = [0x00u8, 0x01u8, 0x02u8, 0x03u8, 0x04u8, 0x05u8, 0x06u8, 0x07u8]
val bad_span = ByteSpan.new(bad)
val ok = xz_decode_check_magic(bad_span)
assert_equal(ok, false)
```

</details>

#### XZ encode/decode round-trip

#### empty input round-trip

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val input = ByteSpan.empty()
val frame = xz_encode(input)
val recovered = xz_decode(frame)
assert_true(recovered.is_empty())
```

</details>

#### Hello round-trip

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val input = span_from_text("Hello")
val frame = xz_encode(input)
val recovered = xz_decode(frame)
val same = spans_equal(input, recovered)
assert_true(same)
```

</details>

#### Hello World round-trip

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val input = span_from_text("Hello, World!")
val frame = xz_encode(input)
val recovered = xz_decode(frame)
val same = spans_equal(input, recovered)
assert_true(same)
```

</details>

#### binary byte ramp 0..63 round-trip

- raw push
- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

#### RangeCoder probability update

#### rc_prob_update bit=0 increases probability (toward 2048)

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = rc_prob_init()
val p2 = rc_prob_update(p, 0)
val increased = p2 > p
assert_true(increased)
```

</details>

#### rc_prob_update bit=1 decreases probability (toward 0)

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = rc_prob_init()
val p2 = rc_prob_update(p, 1)
val decreased = p2 < p
assert_true(decreased)
```

</details>

#### rc_prob_update converges toward 2048 for all-zero bits

- var p = rc prob init
- p = rc prob update
- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

- var p = rc prob init
- p = rc prob update
- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

- assert equal
- assert equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var bits: [i64] = [0]
val encoded = rc_encode_bits(bits, rc_prob_init())
val decoded = rc_decode_bits(encoded, 1, rc_prob_init())
assert_equal(decoded.len(), 1)
assert_equal(decoded[0], 0)
```

</details>

#### single bit 1 round-trip

- assert equal
- assert equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var bits: [i64] = [1]
val encoded = rc_encode_bits(bits, rc_prob_init())
val decoded = rc_decode_bits(encoded, 1, rc_prob_init())
assert_equal(decoded.len(), 1)
assert_equal(decoded[0], 1)
```

</details>

#### alternating bits 0,1,0,1,0,1 round-trip

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var bits: [i64] = [0, 1, 0, 1, 0, 1]
val encoded = rc_encode_bits(bits, rc_prob_init())
val decoded = rc_decode_bits(encoded, 6, rc_prob_init())
val same = ints_equal(decoded, bits)
assert_true(same)
```

</details>

#### all-zero 8 bits round-trip

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var bits: [i64] = [0, 0, 0, 0, 0, 0, 0, 0]
val encoded = rc_encode_bits(bits, rc_prob_init())
val decoded = rc_decode_bits(encoded, 8, rc_prob_init())
val same = ints_equal(decoded, bits)
assert_true(same)
```

</details>

#### all-one 8 bits round-trip

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var bits: [i64] = [1, 1, 1, 1, 1, 1, 1, 1]
val encoded = rc_encode_bits(bits, rc_prob_init())
val decoded = rc_decode_bits(encoded, 8, rc_prob_init())
val same = ints_equal(decoded, bits)
assert_true(same)
```

</details>

#### mixed 8-bit sequence round-trip

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/compress/typed/lzma2_typed_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- lzma2_typed codec

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 30 |
| Active scenarios | 30 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
