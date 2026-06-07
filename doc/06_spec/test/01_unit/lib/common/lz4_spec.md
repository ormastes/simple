# Lz4 Specification

> <details>

<!-- sdn-diagram:id=lz4_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=lz4_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

lz4_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=lz4_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 20 | 20 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Lz4 Specification

## Scenarios

### lz4 pure-Simple block and frame

#### round-trips overlap-heavy raw blocks

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val input = _repetitive_bytes(8192)
val encoded = lz4_compress_block(input)
val decoded = lz4_decompress_block(encoded)
expect(decoded.is_err()).to_equal(false)
expect(decoded.unwrap()).to_equal(input)
```

</details>

#### round-trips repetitive data through the baseline raw-block encoder

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val input = _repetitive_bytes(8192)
val encoded = lz4_compress_block(input)
val decoded = lz4_decompress_block(encoded)
expect(decoded.is_err()).to_equal(false)
expect(decoded.unwrap()).to_equal(input)
```

</details>

#### emits framed bytes with declared content size

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val input = _repetitive_bytes(4096)
val options = _frame_options(false, input.len(), 1)
val encoded = lz4_compress_frame(input, options)
expect(encoded[4] & 0x20u8 != 0u8).to_equal(true)
expect(encoded[4] & 0x08u8 != 0u8).to_equal(true)
expect(encoded[5]).to_equal(0x40u8)
val decoded = lz4_decompress_frame(encoded)
expect(decoded.is_err()).to_equal(false)
expect(decoded.unwrap()).to_equal(input)
val public_decoded = decompress_bytes(encoded, nil)
expect(public_decoded.is_err()).to_equal(false)
expect(public_decoded.unwrap()).to_equal(input)
```

</details>

#### keeps public block mode round-tripping through explicit lz4 hint

<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val base = default_compression_options(CompressionCodec.lz4)
val options = CompressionOptions(
    codec: base.codec,
    level: base.level,
    checksum: false,
    block_mode: "block",
    dictionary_bytes: nil,
    dictionary_id: nil,
    content_size: nil
)
val input = _repetitive_bytes(4096)
val encoded = compress_bytes(input, options)
val decoded = decompress_bytes(encoded, Some(CompressionCodec.lz4))
expect(decoded.is_err()).to_equal(false)
expect(decoded.unwrap()).to_equal(input)
```

</details>

#### keeps framed output and decode parity across scalar avx2 and neon tiers

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val input = _repetitive_bytes(4096)
val options = _frame_options(false, input.len(), 1)
val scalar = lz4_compress_frame_for_tier(input, options, CompressionSimdTier.scalar)
val avx2 = lz4_compress_frame_for_tier(input, options, CompressionSimdTier.avx2)
val neon = lz4_compress_frame_for_tier(input, options, CompressionSimdTier.neon)
expect(avx2).to_equal(scalar)
expect(neon).to_equal(scalar)
expect(lz4_compress_frame(input, options)).to_equal(scalar)
expect(lz4_decompress_frame_for_tier(scalar, CompressionSimdTier.scalar).unwrap()).to_equal(input)
expect(lz4_decompress_frame_for_tier(scalar, CompressionSimdTier.avx2).unwrap()).to_equal(input)
expect(lz4_decompress_frame_for_tier(scalar, CompressionSimdTier.neon).unwrap()).to_equal(input)
```

</details>

#### stores compressed frame blocks for repetitive data on the baseline path

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val input = _repetitive_bytes(8192)
val encoded = lz4_compress_frame(input, _frame_options(false, input.len(), 1))
val size_word = _frame_first_block_size_word(encoded)
expect((size_word & 0x80000000u32) == 0u32).to_equal(true)
expect((size_word & 0x7FFFFFFFu32).to_i64() < input.len()).to_equal(true)
val decoded = lz4_decompress_frame(encoded)
expect(decoded.is_err()).to_equal(false)
expect(decoded.unwrap()).to_equal(input)
```

</details>

#### stores incompressible frame blocks as raw literals

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val input = _unique_bytes(251, 17)
val encoded = lz4_compress_frame(input, _frame_options(false, input.len(), 1))
val size_word = _frame_first_block_size_word(encoded)
expect((size_word & 0x80000000u32) != 0u32).to_equal(true)
expect((size_word & 0x7FFFFFFFu32).to_i64()).to_equal(input.len())
val decoded = lz4_decompress_frame(encoded)
expect(decoded.is_err()).to_equal(false)
expect(decoded.unwrap()).to_equal(input)
```

</details>

#### emits exact raw single-block frames with host-compatible wire bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val input = [0x00u8, 0x01u8, 0x02u8, 0x03u8]
val expected = _manual_raw_frame(input, false, true)
val encoded = lz4_compress_frame(input, _frame_options(false, input.len(), 1))
expect(encoded).to_equal(expected)
val decoded = lz4_decompress_frame(expected)
expect(decoded.is_err()).to_equal(false)
expect(decoded.unwrap()).to_equal(input)
```

</details>

#### decodes multi-block raw frames with content-size framing

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val first = _unique_bytes(251, 23)
val second = _repetitive_bytes(64)
val input = _concat_bytes(first, second)
val encoded = _manual_raw_two_block_frame(first, second, false, true)
expect(encoded[4]).to_equal(0x68u8)
expect(_count_frame_blocks(encoded)).to_equal(2)
val decoded = lz4_decompress_frame(encoded)
expect(decoded.is_err()).to_equal(false)
expect(decoded.unwrap()).to_equal(input)
```

</details>

#### fails closed on a corrupt frame header checksum

1.  expect compression error


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val input = _repetitive_bytes(2048)
val encoded = lz4_compress_frame(input, _frame_options(false, input.len(), 1))
var corrupt = encoded
val hc_offset = _frame_header_checksum_offset(corrupt)
corrupt[hc_offset] = corrupt[hc_offset] ^ 0x01u8
val decoded = lz4_decompress_frame(corrupt)
expect(decoded.is_err()).to_equal(true)
_expect_compression_error(decoded.unwrap_err(), "ChecksumMismatch", "header checksum")
```

</details>

#### fails closed on a corrupt block checksum

1.  expect compression error


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val input = _repetitive_bytes(4096)
val encoded = lz4_compress_frame(input, _frame_options(true, input.len(), 1))
var corrupt = encoded
val payload_offset = _frame_first_block_payload_offset(corrupt)
corrupt[payload_offset] = corrupt[payload_offset] ^ 0x01u8
val decoded = lz4_decompress_frame(corrupt)
expect(decoded.is_err()).to_equal(true)
_expect_compression_error(decoded.unwrap_err(), "ChecksumMismatch", "block checksum")
```

</details>

#### fails closed on a corrupt content checksum

1.  expect compression error


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val input = _repetitive_bytes(4096)
val encoded = lz4_compress_frame(input, _frame_options(true, input.len(), 1))
var corrupt = encoded
val checksum_offset = _frame_content_checksum_offset(corrupt)
corrupt[checksum_offset] = corrupt[checksum_offset] ^ 0x01u8
val decoded = lz4_decompress_frame(corrupt)
expect(decoded.is_err()).to_equal(true)
_expect_compression_error(decoded.unwrap_err(), "ChecksumMismatch", "content checksum")
```

</details>

#### fails closed on truncated block payload bytes

1.  expect compression error


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val input = _unique_bytes(251, 91)
val encoded = lz4_compress_frame(input, _frame_options(false, input.len(), 1))
val truncated = encoded.slice(0, encoded.len() - 2)
val decoded = lz4_decompress_frame(truncated)
expect(decoded.is_err()).to_equal(true)
_expect_compression_error(decoded.unwrap_err(), "TruncatedInput", "lz4 block")
```

</details>

#### fails closed on truncated block checksum bytes

1.  expect compression error


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val input = _unique_bytes(251, 101)
val encoded = lz4_compress_frame(input, _frame_options(true, input.len(), 1))
val truncated = encoded.slice(0, encoded.len() - 6)
val decoded = lz4_decompress_frame(truncated)
expect(decoded.is_err()).to_equal(true)
_expect_compression_error(decoded.unwrap_err(), "TruncatedInput", "block checksum")
```

</details>

#### fails closed on truncated content checksum bytes

1.  expect compression error


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val input = _unique_bytes(251, 111)
val encoded = lz4_compress_frame(input, _frame_options(true, input.len(), 1))
val truncated = encoded.slice(0, encoded.len() - 2)
val decoded = lz4_decompress_frame(truncated)
expect(decoded.is_err()).to_equal(true)
_expect_compression_error(decoded.unwrap_err(), "TruncatedInput", "content checksum")
```

</details>

#### validates declared content size against decoded bytes

1. corrupt =  set header checksum
   - Expected: decoded.is_err() is true
2.  expect compression error


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val input = _repetitive_bytes(2048)
val encoded = lz4_compress_frame(input, _frame_options(false, input.len(), 1))
var corrupt = encoded
corrupt[6] = corrupt[6] + 1u8
corrupt = _set_header_checksum(corrupt)
val decoded = lz4_decompress_frame(corrupt)
expect(decoded.is_err()).to_equal(true)
_expect_compression_error(decoded.unwrap_err(), "CorruptStream", "content size mismatch")
```

</details>

#### rejects dependent-block frames explicitly

1. corrupt =  set header checksum
   - Expected: decoded.is_err() is true
2.  expect compression error


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val input = _repetitive_bytes(2048)
val encoded = lz4_compress_frame(input, _frame_options(false, nil, 1))
var corrupt = encoded
corrupt[4] = corrupt[4] & 0xDFu8
corrupt = _set_header_checksum(corrupt)
val decoded = lz4_decompress_frame(corrupt)
expect(decoded.is_err()).to_equal(true)
_expect_compression_error(decoded.unwrap_err(), "UnsupportedFeature", "dependent blocks")
```

</details>

#### rejects trailing bytes after a valid frame

1. var encoded = lz4 compress frame
2. encoded push
   - Expected: decoded.is_err() is true
3.  expect compression error


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val input = _repetitive_bytes(2048)
var encoded = lz4_compress_frame(input, _frame_options(false, input.len(), 1))
encoded.push(0xAAu8)
val decoded = lz4_decompress_frame(encoded)
expect(decoded.is_err()).to_equal(true)
_expect_compression_error(decoded.unwrap_err(), "CorruptStream", "trailing bytes")
```

</details>

#### rejects empty non-terminal data blocks

1. var frame =  manual raw frame
   - Expected: decoded.is_err() is true
2.  expect compression error


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var frame = _manual_raw_frame([0x41u8], false, true)
val size_offset = _frame_header_checksum_offset(frame) + 1
frame[size_offset] = 0u8
frame[size_offset + 1] = 0u8
frame[size_offset + 2] = 0u8
frame[size_offset + 3] = 0x80u8
val decoded = lz4_decompress_frame(frame)
expect(decoded.is_err()).to_equal(true)
_expect_compression_error(decoded.unwrap_err(), "CorruptStream", "empty data block")
```

</details>

#### rejects impossible raw block back-references

1.  expect compression error


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val decoded = lz4_decompress_block([0x00u8, 0x00u8, 0x00u8])
expect(decoded.is_err()).to_equal(true)
_expect_compression_error(decoded.unwrap_err(), "CorruptStream", "invalid match offset")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/lz4_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- lz4 pure-Simple block and frame

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 20 |
| Active scenarios | 20 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
