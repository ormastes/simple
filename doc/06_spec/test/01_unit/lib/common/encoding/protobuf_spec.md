# Protobuf Specification

> <details>

<!-- sdn-diagram:id=protobuf_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=protobuf_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

protobuf_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=protobuf_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 45 | 45 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Protobuf Specification

## Scenarios

### pb_encode_varint

#### 1-byte cases

#### encodes 1 as single byte 0x01

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val enc = _varint_1()
expect(enc.len()).to_equal(1)
expect(enc[0].to_i64()).to_equal(1)
```

</details>

#### encodes 127 as single byte 0x7F

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val enc = _varint_127()
expect(enc.len()).to_equal(1)
expect(enc[0].to_i64()).to_equal(127)
```

</details>

#### 2-byte cases

#### encodes 128 as two bytes 0x80 0x01

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val enc = _varint_128()
expect(enc.len()).to_equal(2)
expect(enc[0].to_i64()).to_equal(0x80)
expect(enc[1].to_i64()).to_equal(0x01)
```

</details>

#### encodes 150 as two bytes 0x96 0x01

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val enc = _varint_150()
expect(enc.len()).to_equal(2)
expect(enc[0].to_i64()).to_equal(0x96)
expect(enc[1].to_i64()).to_equal(0x01)
```

</details>

#### encodes 300 as two bytes 0xAC 0x02

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val enc = _varint_300()
expect(enc.len()).to_equal(2)
expect(enc[0].to_i64()).to_equal(0xAC)
expect(enc[1].to_i64()).to_equal(0x02)
```

</details>

#### 5-byte case

#### encodes 2147483647 (i32 max) in 5 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val enc = _varint_2147483647()
expect(enc.len()).to_equal(5)
```

</details>

### pb_decode_varint

#### 1-byte decode

#### decodes 1 back to 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = _decode_varint_1()
expect(r[0]).to_equal(1)
```

</details>

#### returns new_pos = 1 for 1-byte varint

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = _decode_varint_1()
expect(r[1]).to_equal(1)
```

</details>

#### 2-byte decode

#### decodes 128 back to 128

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = _decode_varint_128()
expect(r[0]).to_equal(128)
```

</details>

#### returns new_pos = 2 for 2-byte varint

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = _decode_varint_128()
expect(r[1]).to_equal(2)
```

</details>

#### decodes 300 back to 300

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = _decode_varint_300()
expect(r[0]).to_equal(300)
```

</details>

#### 5-byte decode

#### decodes i32 max (2147483647) back correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = _decode_varint_2147483647()
expect(r[0]).to_equal(2147483647)
```

</details>

#### returns new_pos = 5 for 5-byte varint

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = _decode_varint_2147483647()
expect(r[1]).to_equal(5)
```

</details>

### pb_encode_zigzag

#### encodes 0 to 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_zigzag_0()).to_equal(0)
```

</details>

#### encodes -1 to 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_zigzag_neg1()).to_equal(1)
```

</details>

#### encodes 1 to 2

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_zigzag_1()).to_equal(2)
```

</details>

#### encodes -2 to 3

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_zigzag_neg2()).to_equal(3)
```

</details>

#### encodes large positive to even number

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_zigzag_2147483647()).to_equal(4294967294)
```

</details>

### pb_decode_zigzag

#### decodes 0 to 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_decode_zigzag_0()).to_equal(0)
```

</details>

#### decodes 1 to -1

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_decode_zigzag_1()).to_equal(-1)
```

</details>

#### decodes 2 to 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_decode_zigzag_2()).to_equal(1)
```

</details>

#### decodes 3 to -2

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_decode_zigzag_3()).to_equal(-2)
```

</details>

### pb_encode_zigzag / pb_decode_zigzag round-trip

#### round-trips 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(pb_decode_zigzag(pb_encode_zigzag(0))).to_equal(0)
```

</details>

#### round-trips -1

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(pb_decode_zigzag(pb_encode_zigzag(-1))).to_equal(-1)
```

</details>

#### round-trips 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(pb_decode_zigzag(pb_encode_zigzag(1))).to_equal(1)
```

</details>

#### round-trips large negative

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(pb_decode_zigzag(pb_encode_zigzag(-100000))).to_equal(-100000)
```

</details>

### pb_encode_tag

#### encodes field 1, wire_type 0 (varint) as single byte 0x08

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val enc = _tag_field1_varint()
expect(enc.len()).to_equal(1)
expect(enc[0].to_i64()).to_equal(0x08)
```

</details>

#### encodes field 2, wire_type 2 (length-delimited) as single byte 0x12

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val enc = _tag_field2_len()
expect(enc.len()).to_equal(1)
expect(enc[0].to_i64()).to_equal(0x12)
```

</details>

### pb_encode_fixed32

#### encodes 300 as 4 little-endian bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val enc = _fixed32_300()
expect(enc.len()).to_equal(4)
expect(enc[0].to_i64()).to_equal(44)
expect(enc[1].to_i64()).to_equal(1)
expect(enc[2].to_i64()).to_equal(0)
expect(enc[3].to_i64()).to_equal(0)
```

</details>

### pb_encode_fixed64

#### encodes 1000000000000 as 8 little-endian bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val enc = _fixed64_as_field()
# Just verify the tag+value field is 9 bytes (1 tag byte + 8 data bytes)
expect(enc.len()).to_equal(9)
```

</details>

### protobuf message round-trip

#### field1 = varint 150

#### decodes field_num = 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = pb_decode_field(_roundtrip_message(), 0)
expect(r[0]).to_equal(1)
```

</details>

#### decodes wire_type = 0 (varint)

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_roundtrip_field1_wire_type()).to_equal(0)
```

</details>

#### decodes value = 150

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_roundtrip_field1_value()).to_equal(150)
```

</details>

#### field2 = string testing

#### decodes field_num = 2

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_roundtrip_field2_field_num()).to_equal(2)
```

</details>

#### decodes wire_type = 2 (length-delimited)

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_roundtrip_field2_wire_type()).to_equal(2)
```

</details>

#### decodes 7 bytes for 'testing'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_roundtrip_field2_bytes_len()).to_equal(7)
```

</details>

#### first decoded byte = ord('t') = 116

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_roundtrip_field2_first_byte()).to_equal(116)
```

</details>

### pb_decode_field fixed32

#### decodes field_num = 3

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = pb_decode_field(_fixed32_300_as_field(), 0)
expect(r[0]).to_equal(3)
```

</details>

#### decodes wire_type = 5

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = pb_decode_field(_fixed32_300_as_field(), 0)
expect(r[1]).to_equal(5)
```

</details>

#### decodes value = 300

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = pb_decode_field(_fixed32_300_as_field(), 0)
expect(r[2]).to_equal(300)
```

</details>

#### advances pos by 5 (1 tag + 4 data)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = pb_decode_field(_fixed32_300_as_field(), 0)
expect(r[3]).to_equal(5)
```

</details>

### pb_decode_field fixed64

#### decodes field_num = 4

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = pb_decode_field(_fixed64_as_field(), 0)
expect(r[0]).to_equal(4)
```

</details>

#### decodes wire_type = 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = pb_decode_field(_fixed64_as_field(), 0)
expect(r[1]).to_equal(1)
```

</details>

#### decodes value = 1000000000000

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = pb_decode_field(_fixed64_as_field(), 0)
expect(r[2]).to_equal(1000000000000)
```

</details>

#### advances pos by 9 (1 tag + 8 data)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = pb_decode_field(_fixed64_as_field(), 0)
expect(r[3]).to_equal(9)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/encoding/protobuf_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- pb_encode_varint
- pb_decode_varint
- pb_encode_zigzag
- pb_decode_zigzag
- pb_encode_zigzag / pb_decode_zigzag round-trip
- pb_encode_tag
- pb_encode_fixed32
- pb_encode_fixed64
- protobuf message round-trip
- pb_decode_field fixed32
- pb_decode_field fixed64

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 45 |
| Active scenarios | 45 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
