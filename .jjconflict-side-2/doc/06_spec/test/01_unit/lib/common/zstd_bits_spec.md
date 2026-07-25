# Zstd Bits Specification

> <details>

<!-- sdn-diagram:id=zstd_bits_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=zstd_bits_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

zstd_bits_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=zstd_bits_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Zstd Bits Specification

## Scenarios

### zstd backward bit helpers

#### reads little-endian integers with bounded truncation checks

-  expect compression error


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data = [
    0x78u8, 0x56u8, 0x34u8, 0x12u8,
    0x08u8, 0x07u8, 0x06u8, 0x05u8,
    0x04u8, 0x03u8, 0x02u8, 0x01u8
]
val word = zstd_read_u32_le(data, 0)
expect(word.is_err()).to_equal(false)
expect(word.unwrap()).to_equal(0x12345678u32)
val long = zstd_read_u64_le(data, 4)
expect(long.is_err()).to_equal(false)
expect(long.unwrap()).to_equal(0x0102030405060708u64)
val truncated = zstd_read_u32_le(data, 9)
expect(truncated.is_err()).to_equal(true)
_expect_compression_error(truncated.unwrap_err(), "TruncatedInput", "4 bytes")
```

</details>

#### peeks and consumes a reverse reservoir across the tail sentinel

<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data = [0xABu8, 0xCDu8, 0x17u8]
val init = zstd_bits_init(data, 0, data.len())
expect(init.is_err()).to_equal(false)
val reader = init.unwrap()
expect(zstd_bits_remaining(reader)).to_equal(20)
val low = zstd_bits_peek(reader, 4)
expect(low.is_err()).to_equal(false)
expect(low.unwrap()).to_equal(0x07u32)
val after_low = zstd_bits_consume(reader, 4)
expect(after_low.is_err()).to_equal(false)
val middle = zstd_bits_read(after_low.unwrap(), 8)
expect(middle.is_err()).to_equal(false)
val (middle_byte, after_middle) = middle.unwrap()
expect(middle_byte).to_equal(0xCDu32)
val high = zstd_bits_peek(after_middle, 8)
expect(high.is_err()).to_equal(false)
expect(high.unwrap()).to_equal(0xABu32)
expect(zstd_bits_remaining(after_middle)).to_equal(8)
```

</details>

#### fails closed on a missing tail mark

-  expect compression error


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val init = zstd_bits_init([0xAAu8, 0x00u8], 0, 2)
expect(init.is_err()).to_equal(true)
_expect_compression_error(init.unwrap_err(), "CorruptStream", "end mark")
```

</details>

#### fails closed when the caller asks for more bits than remain

-  expect compression error


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val init = zstd_bits_init([0x55u8, 0x01u8], 0, 2)
expect(init.is_err()).to_equal(false)
val reader = init.unwrap()
val full = zstd_bits_read(reader, 8)
expect(full.is_err()).to_equal(false)
val (_byte, empty) = full.unwrap()
val truncated = zstd_bits_peek(empty, 1)
expect(truncated.is_err()).to_equal(true)
_expect_compression_error(truncated.unwrap_err(), "TruncatedInput", "bitstream bits")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/zstd_bits_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- zstd backward bit helpers

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
