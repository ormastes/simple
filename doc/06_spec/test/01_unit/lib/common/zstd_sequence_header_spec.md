# Zstd Sequence Header Specification

> 1.  expect compression error

<!-- sdn-diagram:id=zstd_sequence_header_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=zstd_sequence_header_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

zstd_sequence_header_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=zstd_sequence_header_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Zstd Sequence Header Specification

## Scenarios

### zstd sequence header gates

#### rejects repeated fse tables explicitly after parsing the modes byte

1.  expect compression error


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val frame = _zstd_frame(3, _compressed_block(_raw_literals_prefix() + [0x01u8, 0xC0u8]))
val decoded = decompress_bytes(frame, Some(CompressionCodec.zstd))
expect(decoded.is_err()).to_equal(true)
_expect_compression_error(decoded.unwrap_err(), "UnsupportedFeature", "repeated fse tables")
```

</details>

#### rejects sequence decoding tables after parsing predefined modes

1.  expect compression error


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val frame = _zstd_frame(3, _compressed_block(_raw_literals_prefix() + [0x01u8, 0x00u8]))
val decoded = decompress_bytes(frame, Some(CompressionCodec.zstd))
expect(decoded.is_err()).to_equal(true)
_expect_compression_error(decoded.unwrap_err(), "UnsupportedFeature", "sequence decoding tables")
```

</details>

#### validates reserved bits in the sequence modes byte

1.  expect compression error


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val frame = _zstd_frame(3, _compressed_block(_raw_literals_prefix() + [0x01u8, 0x01u8]))
val decoded = decompress_bytes(frame, Some(CompressionCodec.zstd))
expect(decoded.is_err()).to_equal(true)
_expect_compression_error(decoded.unwrap_err(), "CorruptStream", "reserved bits")
```

</details>

#### parses the two-byte sequence count encoding before gating

1.  expect compression error


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val frame = _zstd_frame(3, _compressed_block(_raw_literals_prefix() + [0x80u8, 0x82u8, 0x00u8]))
val decoded = decompress_bytes(frame, Some(CompressionCodec.zstd))
expect(decoded.is_err()).to_equal(true)
_expect_compression_error(decoded.unwrap_err(), "UnsupportedFeature", "sequence decoding tables")
```

</details>

#### parses the three-byte sequence count encoding before gating

1.  expect compression error


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val frame = _zstd_frame(3, _compressed_block(_raw_literals_prefix() + [0xFFu8, 0x01u8, 0x00u8, 0x00u8]))
val decoded = decompress_bytes(frame, Some(CompressionCodec.zstd))
expect(decoded.is_err()).to_equal(true)
_expect_compression_error(decoded.unwrap_err(), "UnsupportedFeature", "sequence decoding tables")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/zstd_sequence_header_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- zstd sequence header gates

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
