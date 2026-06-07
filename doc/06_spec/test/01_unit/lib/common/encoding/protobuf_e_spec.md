# Protobuf E Specification

> <details>

<!-- sdn-diagram:id=protobuf_e_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=protobuf_e_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

protobuf_e_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=protobuf_e_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Protobuf E Specification

## Scenarios

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
expect(enc[0].to_i64()).to_equal(44)   # 300 & 0xFF = 0x2C = 44
expect(enc[1].to_i64()).to_equal(1)    # (300>>8)&0xFF = 1
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

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/encoding/protobuf_e_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- pb_encode_tag
- pb_encode_fixed32
- pb_encode_fixed64
- protobuf message round-trip

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
