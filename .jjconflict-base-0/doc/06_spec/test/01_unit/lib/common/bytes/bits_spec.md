# Bits Specification

> <details>

<!-- sdn-diagram:id=bits_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=bits_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

bits_spec -> std
bits_spec -> lib
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=bits_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Bits Specification

## Scenarios

### LSB-first bit ordering

#### packs 0b101 (n=3) into the low bits of a byte = 0x05

- var w = BitWriter lsb
- w put bits
   - Expected: out.len() equals `1`
   - Expected: out[0].to_i64() equals `0x05`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var w = BitWriter.lsb()
w.put_bits(5, 3)
val out = w.finish().to_bytes()
expect(out.len()).to_equal(1)
expect(out[0].to_i64()).to_equal(0x05)
```

</details>

#### packs two fields LSB-first: 0b11 then 0b10 -> byte 0b1011 = 0x0B

- var w = BitWriter lsb
- w put bits
- w put bits
   - Expected: out[0].to_i64() equals `0x0B`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var w = BitWriter.lsb()
w.put_bits(3, 2)
w.put_bits(2, 2)
val out = w.finish().to_bytes()
expect(out[0].to_i64()).to_equal(0x0B)
```

</details>

#### reads back the same fields in order

- var w = BitWriter lsb
- w put bits
- w put bits
- var r = BitReader lsb
   - Expected: r.read_bits(2) equals `3`
   - Expected: r.read_bits(2) equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var w = BitWriter.lsb()
w.put_bits(3, 2)
w.put_bits(2, 2)
val bytes = w.finish().to_bytes()
var r = BitReader.lsb(bytes)
expect(r.read_bits(2)).to_equal(3)
expect(r.read_bits(2)).to_equal(2)
```

</details>

### MSB-first bit ordering

#### packs 0b101 (n=3) into the high bits of a byte = 0xA0

- var w = BitWriter msb
- w put bits
   - Expected: out[0].to_i64() equals `0xA0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var w = BitWriter.msb()
w.put_bits(5, 3)
val out = w.finish().to_bytes()
expect(out[0].to_i64()).to_equal(0xA0)
```

</details>

#### reads back MSB-first fields in order

- var w = BitWriter msb
- w put bits
- w put bits
- var r = BitReader msb
   - Expected: r.read_bits(3) equals `5`
   - Expected: r.read_bits(1) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var w = BitWriter.msb()
w.put_bits(5, 3)
w.put_bits(1, 1)
val bytes = w.finish().to_bytes()
var r = BitReader.msb(bytes)
expect(r.read_bits(3)).to_equal(5)
expect(r.read_bits(1)).to_equal(1)
```

</details>

### Round-trip across non-byte-aligned widths

#### LSB round-trips a sequence of varied widths exactly

- var w = BitWriter lsb
- w put bits
- w put bits
- w put bits
- w put bits
- var r = BitReader lsb
   - Expected: r.read_bits(1) equals `1`
   - Expected: r.read_bits(5) equals `13`
   - Expected: r.read_bits(11) equals `700`
   - Expected: r.read_bits(8) equals `255`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var w = BitWriter.lsb()
w.put_bits(1, 1)
w.put_bits(13, 5)
w.put_bits(700, 11)
w.put_bits(255, 8)
val bytes = w.finish().to_bytes()
var r = BitReader.lsb(bytes)
expect(r.read_bits(1)).to_equal(1)
expect(r.read_bits(5)).to_equal(13)
expect(r.read_bits(11)).to_equal(700)
expect(r.read_bits(8)).to_equal(255)
```

</details>

#### MSB round-trips a sequence of varied widths exactly

- var w = BitWriter msb
- w put bits
- w put bits
- w put bits
- w put bits
- var r = BitReader msb
   - Expected: r.read_bits(1) equals `1`
   - Expected: r.read_bits(5) equals `13`
   - Expected: r.read_bits(11) equals `700`
   - Expected: r.read_bits(8) equals `255`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var w = BitWriter.msb()
w.put_bits(1, 1)
w.put_bits(13, 5)
w.put_bits(700, 11)
w.put_bits(255, 8)
val bytes = w.finish().to_bytes()
var r = BitReader.msb(bytes)
expect(r.read_bits(1)).to_equal(1)
expect(r.read_bits(5)).to_equal(13)
expect(r.read_bits(11)).to_equal(700)
expect(r.read_bits(8)).to_equal(255)
```

</details>

#### LSB round-trips a wide 33-bit value

- var w = BitWriter lsb
- w put bits
- var r = BitReader lsb
   - Expected: r.read_bits(33) equals `big`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var w = BitWriter.lsb()
val big = 0x1FEEDBEEF
w.put_bits(big, 33)
val bytes = w.finish().to_bytes()
var r = BitReader.lsb(bytes)
expect(r.read_bits(33)).to_equal(big)
```

</details>

#### LSB round-trips a 48-bit value

- var w = BitWriter lsb
- w put bits
- var r = BitReader lsb
   - Expected: r.read_bits(48) equals `v`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var w = BitWriter.lsb()
val v = 0xABCDEF012345
w.put_bits(v, 48)
var r = BitReader.lsb(w.finish().to_bytes())
expect(r.read_bits(48)).to_equal(v)
```

</details>

#### MSB round-trips a full 64-bit value (AC-4 upper bound)

- var w = BitWriter msb
- w put bits
- var r = BitReader msb
   - Expected: r.read_bits(64) equals `v`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var w = BitWriter.msb()
val v = 0x0123456789ABCDEF
w.put_bits(v, 64)
var r = BitReader.msb(w.finish().to_bytes())
expect(r.read_bits(64)).to_equal(v)
```

</details>

#### LSB round-trips a full 64-bit value (AC-4 upper bound)

- var w = BitWriter lsb
- w put bits
- var r = BitReader lsb
   - Expected: r.read_bits(64) equals `v`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var w = BitWriter.lsb()
val v = 0x0123456789ABCDEF
w.put_bits(v, 64)
var r = BitReader.lsb(w.finish().to_bytes())
expect(r.read_bits(64)).to_equal(v)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/bytes/bits_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- LSB-first bit ordering
- MSB-first bit ordering
- Round-trip across non-byte-aligned widths

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
