# Byte Cursor Specification

> <details>

<!-- sdn-diagram:id=byte_cursor_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=byte_cursor_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

byte_cursor_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=byte_cursor_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Byte Cursor Specification

## Scenarios

### ByteReader/ByteWriter big-endian wire codec

#### round-trips 0xDEADBEEF through write_u32/read_u32 with exact bytes

- var w = ByteWriter new
- w write u32
   - Expected: bytes.len() equals `4`
   - Expected: bytes[0] equals `0xDEu8`
   - Expected: bytes[1] equals `0xADu8`
   - Expected: bytes[2] equals `0xBEu8`
   - Expected: bytes[3] equals `0xEFu8`
- var r = ByteReader new


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var w = ByteWriter.new()
w.write_u32(0xDEADBEEFu32)
val bytes = w.to_bytes()
expect(bytes.len()).to_equal(4)
expect(bytes[0]).to_equal(0xDEu8)
expect(bytes[1]).to_equal(0xADu8)
expect(bytes[2]).to_equal(0xBEu8)
expect(bytes[3]).to_equal(0xEFu8)
var r = ByteReader.new(bytes)
match r.read_u32():
    case Ok(v): expect(v).to_equal(0xDEADBEEFu32)
    case Err(_): assert_true(false)
```

</details>

#### read_u8 past end yields a clean Err, never a panic

- var r = ByteReader new


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var r = ByteReader.new([])
match r.read_u8():
    case Ok(_): assert_true(false)
    case Err(msg): expect(msg).to_contain("past end")
```

</details>

#### read_bytes past end yields a clean Err

- var r = ByteReader new


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data: [u8] = [1u8, 2u8]
var r = ByteReader.new(data)
match r.read_bytes(5):
    case Ok(_): assert_true(false)
    case Err(msg): expect(msg).to_contain("past end")
```

</details>

#### boundary read at exact remaining length succeeds and drains the cursor

- var r = ByteReader new
   - Expected: r.remaining() equals `0u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data: [u8] = [0xAAu8, 0xBBu8]
var r = ByteReader.new(data)
match r.read_u16():
    case Ok(v): expect(v).to_equal(0xAABBu16)
    case Err(_): assert_true(false)
expect(r.remaining()).to_equal(0u64)
```

</details>

#### interleaves u8/u16/u24/u32/u48/u64 writes and reads in order

- var w = ByteWriter new
- w write u8
- w write u16
- w write u24
- w write u32
- w write u48
- w write u64
   - Expected: bytes.len() equals `24`
- var r = ByteReader new
   - Expected: r.remaining() equals `0u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var w = ByteWriter.new()
w.write_u8(1u8)
w.write_u16(2u16)
w.write_u24(3u32)
w.write_u32(4u32)
w.write_u48(5u64)
w.write_u64(6u64)
val bytes = w.to_bytes()
expect(bytes.len()).to_equal(24)
var r = ByteReader.new(bytes)
match r.read_u8():
    case Ok(v): expect(v).to_equal(1u8)
    case Err(_): assert_true(false)
match r.read_u16():
    case Ok(v): expect(v).to_equal(2u16)
    case Err(_): assert_true(false)
match r.read_u24():
    case Ok(v): expect(v).to_equal(3u32)
    case Err(_): assert_true(false)
match r.read_u32():
    case Ok(v): expect(v).to_equal(4u32)
    case Err(_): assert_true(false)
match r.read_u48():
    case Ok(v): expect(v).to_equal(5u64)
    case Err(_): assert_true(false)
match r.read_u64():
    case Ok(v): expect(v).to_equal(6u64)
    case Err(_): assert_true(false)
expect(r.remaining()).to_equal(0u64)
```

</details>

#### write_bytes/read_bytes round-trips an arbitrary payload

- var w = ByteWriter new
- w write bytes
- var r = ByteReader new
   - Expected: v[0] equals `0x10u8`
   - Expected: v[1] equals `0x20u8`
   - Expected: v[2] equals `0x30u8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val payload: [u8] = [0x10u8, 0x20u8, 0x30u8]
var w = ByteWriter.new()
w.write_bytes(payload)
val bytes = w.to_bytes()
var r = ByteReader.new(bytes)
match r.read_bytes(3):
    case Ok(v):
        expect(v[0]).to_equal(0x10u8)
        expect(v[1]).to_equal(0x20u8)
        expect(v[2]).to_equal(0x30u8)
    case Err(_): assert_true(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/net/byte_cursor_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- ByteReader/ByteWriter big-endian wire codec

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
