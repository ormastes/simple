# Bytes Foundation Specification

> <details>

<!-- sdn-diagram:id=bytes_foundation_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=bytes_foundation_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

bytes_foundation_spec -> std
bytes_foundation_spec -> lib
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=bytes_foundation_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Bytes Foundation Specification

## Scenarios

### AC-3: ByteBuffer.freeze() <-> ByteSpan byte-exact round-trip

#### buffer built from a span freezes back to an equal span

- var buf = ByteBuffer new
- buf push span
   - Expected: frozen.equals(src) is true
   - Expected: frozen.get(0).to_i64() equals `0xDE`
   - Expected: frozen.get(5).to_i64() equals `0xFF`
   - Expected: frozen.len() equals `6`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val original: [u8] = [0xDEu8, 0xADu8, 0xBEu8, 0xEFu8, 0x00u8, 0xFFu8]
val src = ByteSpan.new(original)
var buf = ByteBuffer.new()
buf.push_span(src)
val frozen = buf.freeze()
expect(frozen.equals(src)).to_equal(true)
# absolute oracle: explicit bytes
expect(frozen.get(0).to_i64()).to_equal(0xDE)
expect(frozen.get(5).to_i64()).to_equal(0xFF)
expect(frozen.len()).to_equal(6)
```

</details>

#### mixed push_u8 + push_span assembles the expected exact bytes

- var buf = ByteBuffer new
- buf push u8
- buf push span
   - Expected: frozen.equals(ByteSpan.new(expected)) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var buf = ByteBuffer.new()
buf.push_u8(0x01u8)
val tail: [u8] = [0x02u8, 0x03u8]
buf.push_span(ByteSpan.new(tail))
val frozen = buf.freeze()
val expected: [u8] = [0x01u8, 0x02u8, 0x03u8]
expect(frozen.equals(ByteSpan.new(expected))).to_equal(true)
```

</details>

### AC-4: BitWriter -> BitReader bit-exact across orderings

#### LSB-first packs and unpacks an exact known bit pattern

- var w = BitWriter lsb
- w put bits
- w put bits
- w put bits
   - Expected: bytes[0].to_i64() equals `0xA7`
- var r = BitReader lsb
   - Expected: r.read_bits(1) equals `1`
   - Expected: r.read_bits(3) equals `3`
   - Expected: r.read_bits(4) equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var w = BitWriter.lsb()
w.put_bits(0b1, 1)
w.put_bits(0b011, 3)
w.put_bits(0b1010, 4)
val bytes = w.finish().to_bytes()
# LSB-first: byte = bit0=1, bits1..3=011, bits4..7=1010 -> 0b10100111 = 0xA7
expect(bytes[0].to_i64()).to_equal(0xA7)
var r = BitReader.lsb(bytes)
expect(r.read_bits(1)).to_equal(1)
expect(r.read_bits(3)).to_equal(3)
expect(r.read_bits(4)).to_equal(10)
```

</details>

#### MSB-first packs and unpacks an exact known bit pattern

- var w = BitWriter msb
- w put bits
- w put bits
- w put bits
   - Expected: bytes[0].to_i64() equals `0xBA`
- var r = BitReader msb
   - Expected: r.read_bits(1) equals `1`
   - Expected: r.read_bits(3) equals `3`
   - Expected: r.read_bits(4) equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var w = BitWriter.msb()
w.put_bits(0b1, 1)
w.put_bits(0b011, 3)
w.put_bits(0b1010, 4)
val bytes = w.finish().to_bytes()
# MSB-first: byte = 1 011 1010 = 0b10111010 = 0xBA
expect(bytes[0].to_i64()).to_equal(0xBA)
var r = BitReader.msb(bytes)
expect(r.read_bits(1)).to_equal(1)
expect(r.read_bits(3)).to_equal(3)
expect(r.read_bits(4)).to_equal(10)
```

</details>

### Cross-module: encode integers, then checksum the frozen span

#### U32be + U32le serialized into a buffer CRC matches a recomputed CRC

- var buf = ByteBuffer new
- U32be of
- U32le of
   - Expected: span.len() equals `8`
   - Expected: span.get(0).to_i64() equals `0x12`
   - Expected: span.get(3).to_i64() equals `0x78`
   - Expected: span.get(4).to_i64() equals `0xF0`
   - Expected: span.get(7).to_i64() equals `0x9A`
- var c1 = Crc32 new
- c1 update
- var c2 = Crc32 new
- c2 update
   - Expected: c1.raw() equals `c2.raw()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var buf = ByteBuffer.new()
U32be.of(0x12345678).store(buf)
U32le.of(0x9ABCDEF0).store(buf)
val span = buf.freeze()
expect(span.len()).to_equal(8)
# byte layout oracle: BE first (12 34 56 78), then LE (F0 DE BC 9A)
expect(span.get(0).to_i64()).to_equal(0x12)
expect(span.get(3).to_i64()).to_equal(0x78)
expect(span.get(4).to_i64()).to_equal(0xF0)
expect(span.get(7).to_i64()).to_equal(0x9A)
# checksum the assembled span; recompute and compare (absolute equality)
var c1 = Crc32.new()
c1.update(span)
var c2 = Crc32.new()
c2.update(ByteSpan.new(span.to_bytes()))
expect(c1.raw()).to_equal(c2.raw())
```

</details>

### AC-1: package facade (__init__.spl) re-exports load

#### RingWindow is reachable via std.common.bytes facade

- var w = RingWindow new
- w push
   - Expected: w.at_distance(1).to_i64() equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var w = RingWindow.new(4)
w.push(42u8)
expect(w.at_distance(1).to_i64()).to_equal(42)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/bytes/bytes_foundation_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- AC-3: ByteBuffer.freeze() <-> ByteSpan byte-exact round-trip
- AC-4: BitWriter -> BitReader bit-exact across orderings
- Cross-module: encode integers, then checksum the frozen span
- AC-1: package facade (__init__.spl) re-exports load

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
