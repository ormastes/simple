# Zstd Sequence Rle Specification

> <details>

<!-- sdn-diagram:id=zstd_sequence_rle_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=zstd_sequence_rle_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

zstd_sequence_rle_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=zstd_sequence_rle_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Zstd Sequence Rle Specification

## Scenarios

### zstd rle sequence execution

#### decodes a one-sequence block with a normal offset

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val frame = _zstd_frame(6, _compressed_block(true, [
    0x18u8,
    0x61u8, 0x62u8, 0x63u8,
    0x01u8,
    0x54u8,
    0x03u8, 0x02u8, 0x00u8,
    0x06u8
]))
val decoded = decompress_bytes(frame, Some(CompressionCodec.zstd))
expect(decoded.is_err()).to_equal(false)
expect(decoded.unwrap()).to_equal([0x61u8, 0x62u8, 0x63u8, 0x61u8, 0x62u8, 0x63u8])
```

</details>

#### supports overlap-safe matches for offset one

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val frame = _zstd_frame(6, _compressed_block(true, [
    0x08u8,
    0x61u8,
    0x01u8,
    0x54u8,
    0x01u8, 0x02u8, 0x02u8,
    0x04u8
]))
val decoded = decompress_bytes(frame, Some(CompressionCodec.zstd))
expect(decoded.is_err()).to_equal(false)
expect(decoded.unwrap()).to_equal([0x61u8, 0x61u8, 0x61u8, 0x61u8, 0x61u8, 0x61u8])
```

</details>

#### supports rep1 offsets during rle sequence execution

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val frame = _zstd_frame(4, _compressed_block(true, [
    0x08u8,
    0x61u8,
    0x01u8,
    0x54u8,
    0x01u8, 0x00u8, 0x00u8,
    0x01u8
]))
val decoded = decompress_bytes(frame, Some(CompressionCodec.zstd))
expect(decoded.is_err()).to_equal(false)
expect(decoded.unwrap()).to_equal([0x61u8, 0x61u8, 0x61u8, 0x61u8])
```

</details>

#### supports zero-literal shifted repeat offsets

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val frame = _zstd_frame(7, _raw_block(false, [0x61u8, 0x62u8, 0x63u8, 0x64u8]) + _compressed_block(true, [
    0x00u8,
    0x01u8,
    0x54u8,
    0x00u8, 0x00u8, 0x00u8,
    0x01u8
]))
val decoded = decompress_bytes(frame, Some(CompressionCodec.zstd))
expect(decoded.is_err()).to_equal(false)
expect(decoded.unwrap()).to_equal([0x61u8, 0x62u8, 0x63u8, 0x64u8, 0x61u8, 0x62u8, 0x63u8])
```

</details>

#### carries repeat-offset history across compressed blocks

- ]) +  compressed block
   - Expected: decoded.is_err() is false
   - Expected: decoded.unwrap() equals `[0x61u8, 0x62u8, 0x63u8, 0x61u8, 0x62u8, 0x63u8, 0x63u8, 0x63u8, 0x63u8]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val frame = _zstd_frame(9, _compressed_block(false, [
    0x18u8,
    0x61u8, 0x62u8, 0x63u8,
    0x01u8,
    0x54u8,
    0x03u8, 0x02u8, 0x00u8,
    0x06u8
]) + _compressed_block(true, [
    0x00u8,
    0x01u8,
    0x54u8,
    0x00u8, 0x00u8, 0x00u8,
    0x01u8
]))
val decoded = decompress_bytes(frame, Some(CompressionCodec.zstd))
expect(decoded.is_err()).to_equal(false)
expect(decoded.unwrap()).to_equal([0x61u8, 0x62u8, 0x63u8, 0x61u8, 0x62u8, 0x63u8, 0x63u8, 0x63u8, 0x63u8])
```

</details>

#### rejects invalid match offsets after literals are copied

-  expect compression error


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val frame = _zstd_frame(6, _compressed_block(true, [
    0x18u8,
    0x61u8, 0x62u8, 0x63u8,
    0x01u8,
    0x54u8,
    0x03u8, 0x03u8, 0x00u8,
    0x0Eu8
]))
val decoded = decompress_bytes(frame, Some(CompressionCodec.zstd))
expect(decoded.is_err()).to_equal(true)
_expect_compression_error(decoded.unwrap_err(), "CorruptStream", "invalid match offset")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/zstd_sequence_rle_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- zstd rle sequence execution

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
