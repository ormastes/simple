# Binary Io Specification

> <details>

<!-- sdn-diagram:id=binary_io_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=binary_io_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

binary_io_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=binary_io_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Binary Io Specification

## Scenarios

### BinaryWriter integer byte masks

#### writes and reads little-endian values with nonzero high bytes

- var writer = BinaryWriter new
- writer write u16
- writer write u32
- writer write i64
   - Expected: bytes[0] equals `77`
   - Expected: bytes[1] equals `1`
   - Expected: bytes[2] equals `1`
   - Expected: bytes[3] equals `2`
   - Expected: bytes[4] equals `3`
   - Expected: bytes[5] equals `4`
   - Expected: bytes[6] equals `77`
   - Expected: bytes[7] equals `1`
- var reader = BinaryReader new
   - Expected: reader.read_u16(ByteOrder.LittleEndian) ?? 0 equals `333`
   - Expected: reader.read_u32(ByteOrder.LittleEndian) ?? 0 equals `0x04030201`
   - Expected: reader.read_i64(ByteOrder.LittleEndian) ?? 0 equals `333`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var writer = BinaryWriter.new()
writer.write_u16(333, ByteOrder.LittleEndian)
writer.write_u32(0x04030201, ByteOrder.LittleEndian)
writer.write_i64(333, ByteOrder.LittleEndian)

val bytes = writer.to_bytes()
expect(bytes[0]).to_equal(77)
expect(bytes[1]).to_equal(1)
expect(bytes[2]).to_equal(1)
expect(bytes[3]).to_equal(2)
expect(bytes[4]).to_equal(3)
expect(bytes[5]).to_equal(4)
expect(bytes[6]).to_equal(77)
expect(bytes[7]).to_equal(1)

var reader = BinaryReader.new(bytes)
expect(reader.read_u16(ByteOrder.LittleEndian) ?? 0).to_equal(333)
expect(reader.read_u32(ByteOrder.LittleEndian) ?? 0).to_equal(0x04030201)
expect(reader.read_i64(ByteOrder.LittleEndian) ?? 0).to_equal(333)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/io/binary_io_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- BinaryWriter integer byte masks

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
