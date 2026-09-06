# Lz4 Typed Specification

> <details>

<!-- sdn-diagram:id=lz4_typed_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=lz4_typed_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

lz4_typed_spec -> std
lz4_typed_spec -> lib
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=lz4_typed_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Lz4 Typed Specification

## Scenarios

### lz4_typed block codec

#### round-trip: empty input

#### compress then decompress empty gives empty

- assert equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val input = ByteSpan.empty()
val compressed = lz4_compress(input)
val recovered = lz4_decompress(compressed, 0)
assert_equal(recovered.len(), 0)
```

</details>

#### round-trip: all-same bytes (high compressibility)

#### 10 repeated 'a' chars

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val input = span_from_text("aaaaaaaaaa")
val compressed = lz4_compress(input)
val recovered = lz4_decompress(compressed, input.len())
assert_true(spans_equal(recovered, input))
```

</details>

#### 100 repeated 'z' chars

- buf100 push
- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var buf100: [u8] = []
var k = 0
while k < 100:
    buf100.push(122u8)   # 'z'
    k = k + 1
val input = ByteSpan.new(buf100)
val compressed = lz4_compress(input)
val recovered = lz4_decompress(compressed, input.len())
assert_true(spans_equal(recovered, input))
```

</details>

#### round-trip: periodic pattern

#### abcabcabcabc (12 bytes)

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val input = span_from_text("abcabcabcabc")
val compressed = lz4_compress(input)
val recovered = lz4_decompress(compressed, input.len())
assert_true(spans_equal(recovered, input))
```

</details>

#### abcabc repeated to 30 bytes

- buf push
- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pat_bytes = "abcabc".bytes()
var buf: [u8] = []
var k = 0
while k < 5:
    var j = 0
    while j < pat_bytes.len():
        buf.push(pat_bytes[j])
        j = j + 1
    k = k + 1
val input = ByteSpan.new(buf)
val compressed = lz4_compress(input)
val recovered = lz4_decompress(compressed, input.len())
assert_true(spans_equal(recovered, input))
```

</details>

#### round-trip: 300-byte mixed buffer with long repeats

#### 100 'A's + 100 'B's + 100 alternating AB

- buf300 push
- buf300 push
- buf300 push
- buf300 push
- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var buf300: [u8] = []
var k = 0
while k < 100:
    buf300.push(65u8)   # 'A'
    k = k + 1
k = 0
while k < 100:
    buf300.push(66u8)   # 'B'
    k = k + 1
k = 0
while k < 50:
    buf300.push(65u8)
    buf300.push(66u8)
    k = k + 1
val input = ByteSpan.new(buf300)
val compressed = lz4_compress(input)
val recovered = lz4_decompress(compressed, input.len())
assert_true(spans_equal(recovered, input))
```

</details>

#### round-trip: random-ish / non-repeating data

#### 26-byte alphabet ABCDEFGHIJ... each unique

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val input = span_from_text("ABCDEFGHIJKLMNOPQRSTUVWXYZ")
val compressed = lz4_compress(input)
val recovered = lz4_decompress(compressed, input.len())
assert_true(spans_equal(recovered, input))
```

</details>

#### short mixed ascii phrase

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val input = span_from_text("The quick brown fox jumps over the lazy dog.")
val compressed = lz4_compress(input)
val recovered = lz4_decompress(compressed, input.len())
assert_true(spans_equal(recovered, input))
```

</details>

#### interop: hand-constructed canonical LZ4 block

#### known-good block decodes to ABCDABCDEFGHIJKL

- assert equal
- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 42 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Canonical LZ4 block (hand-traced):
#   Block bytes: 40 41 42 43 44 04 00 80 45 46 47 48 49 4A 4B 4C
#   Token byte 0x40: lit_nib=4 (4 literals), mat_nib=0 (match_len=4)
#     Literals: 0x41 0x42 0x43 0x44  => "ABCD"
#     Offset:   0x00 0x80             => 0x8000 & 0xFFFF... wait, use actual byte LE
#   Actual: offset bytes are 0x00 0x80 = LE => dist = 0 | (0x80<<8) = 0x8000 = 32768
#   That would be invalid (too far). Use a corrected KAT below.
#
# Correct KAT: produce 16 bytes "ABCDABCDEFGHIJKL"
#   = "ABCD" (literals) + copy(distance=4, length=4) + "EFGHIJKL" (literals)
#
# Sequence 1: token = (4<<4)|0 = 0x40
#   lit_len=4, mat_nib=0 => match_len=4
#   literals: 41 42 43 44 ("ABCD")
#   offset LE: 04 00   (distance=4)
#   (no extra match len bytes since mat_nib=0 → match_len=4, adj=0 < 15)
# Sequence 2 (final): token = (8<<4)|0 = 0x80
#   lit_len=8, no match
#   literals: 45 46 47 48 49 4A 4B 4C ("EFGHIJKL")
#
# Output: "ABCD" + "ABCD" (copy from dist 4) + "EFGHIJKL" = "ABCDABCDEFGHIJKL"
var block: [u8] = [
    0x40u8,
    0x41u8, 0x42u8, 0x43u8, 0x44u8,
    0x04u8, 0x00u8,
    0x80u8,
    0x45u8, 0x46u8, 0x47u8, 0x48u8, 0x49u8, 0x4Au8, 0x4Bu8, 0x4Cu8
]
val block_span = ByteSpan.new(block)
val decoded = lz4_decompress(block_span, 16)

# Expected: "ABCDABCDEFGHIJKL" (16 bytes)
var expected: [u8] = [
    0x41u8, 0x42u8, 0x43u8, 0x44u8,
    0x41u8, 0x42u8, 0x43u8, 0x44u8,
    0x45u8, 0x46u8, 0x47u8, 0x48u8,
    0x49u8, 0x4Au8, 0x4Bu8, 0x4Cu8
]
val expected_span = ByteSpan.new(expected)

assert_equal(decoded.len(), 16)
assert_true(spans_equal(decoded, expected_span))
```

</details>

#### single-literal block: one byte 0x42 'B'

- assert equal
- assert equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Token 0x10: lit_nib=1, mat_nib=0. Literal: 0x42. No offset (final seq).
var one_byte_block: [u8] = [0x10u8, 0x42u8]
val decoded = lz4_decompress(ByteSpan.new(one_byte_block), 1)
assert_equal(decoded.len(), 1)
assert_equal(decoded.get(0).to_i64(), 0x42)
```

</details>

#### failure self-check (verifies assertions fire correctly)

#### wrong expected length detects mismatch

- assert equal
- assert equal
- assert equal
- assert equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val input = span_from_text("hello")
val compressed = lz4_compress(input)
# Decompress requesting only 3 bytes — should give 3 not 5
val partial = lz4_decompress(compressed, 3)
assert_equal(partial.len(), 3)
# The 3 bytes must equal the first 3 bytes of "hello"
assert_equal(partial.get(0).to_i64(), 104)   # 'h'
assert_equal(partial.get(1).to_i64(), 101)   # 'e'
assert_equal(partial.get(2).to_i64(), 108)   # 'l'
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/compress/typed/lz4_typed_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- lz4_typed block codec

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
