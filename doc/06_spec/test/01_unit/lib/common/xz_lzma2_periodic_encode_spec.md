# Xz Lzma2 Periodic Encode Specification

> 1.  ensure tmp root

<!-- sdn-diagram:id=xz_lzma2_periodic_encode_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=xz_lzma2_periodic_encode_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

xz_lzma2_periodic_encode_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=xz_lzma2_periodic_encode_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Xz Lzma2 Periodic Encode Specification

## Scenarios

### xz lzma2 periodic encode

#### compresses alternating-byte runs into a real lzma2 chunk that host xz can decode

1.  ensure tmp root
   - Expected: encoded[_first_block_data_start(encoded)] equals `0xE0u8`
   - Expected: _first_block_declared_compressed_size(encoded) < input.len() is true
   - Expected: lzma2_decompress_xz(encoded).unwrap() equals `input`
2.  assert host xz roundtrip


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
_ensure_tmp_root()
val input = _repeat_pattern([65u8, 66u8], 96)
val options = default_compression_options(CompressionCodec.lzma2)
val encoded = lzma2_compress_xz(input, options)
expect(encoded[_first_block_data_start(encoded)]).to_equal(0xE0u8)
expect(_first_block_declared_compressed_size(encoded) < input.len()).to_equal(true)
expect(lzma2_decompress_xz(encoded).unwrap()).to_equal(input)
_assert_host_xz_roundtrip("alternating", input, encoded)
```

</details>

#### compresses odd-length alternating-byte tails into a real lzma2 chunk that host xz can decode

1.  ensure tmp root
   - Expected: encoded[_first_block_data_start(encoded)] equals `0xE0u8`
   - Expected: _first_block_declared_compressed_size(encoded) < input.len() is true
   - Expected: lzma2_decompress_xz(encoded).unwrap() equals `input`
2.  assert host xz roundtrip


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
_ensure_tmp_root()
val input = _repeat_pattern([65u8, 66u8], 35)
val options = default_compression_options(CompressionCodec.lzma2)
val encoded = lzma2_compress_xz(input, options)
expect(encoded[_first_block_data_start(encoded)]).to_equal(0xE0u8)
expect(_first_block_declared_compressed_size(encoded) < input.len()).to_equal(true)
expect(lzma2_decompress_xz(encoded).unwrap()).to_equal(input)
_assert_host_xz_roundtrip("alternating-odd-tail", input, encoded)
```

</details>

#### compresses three-byte periodic runs into a real lzma2 chunk that host xz can decode

1.  ensure tmp root
   - Expected: encoded[_first_block_data_start(encoded)] equals `0xE0u8`
   - Expected: _first_block_declared_compressed_size(encoded) < input.len() is true
   - Expected: lzma2_decompress_xz(encoded).unwrap() equals `input`
2.  assert host xz roundtrip


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
_ensure_tmp_root()
val input = _repeat_pattern([65u8, 66u8, 67u8], 96)
val options = default_compression_options(CompressionCodec.lzma2)
val encoded = lzma2_compress_xz(input, options)
expect(encoded[_first_block_data_start(encoded)]).to_equal(0xE0u8)
expect(_first_block_declared_compressed_size(encoded) < input.len()).to_equal(true)
expect(lzma2_decompress_xz(encoded).unwrap()).to_equal(input)
_assert_host_xz_roundtrip("triple-period", input, encoded)
```

</details>

#### compresses three-byte periodic runs across the max-match boundary into a real lzma2 chunk that host xz can decode

1.  ensure tmp root
   - Expected: encoded[_first_block_data_start(encoded)] equals `0xE0u8`
   - Expected: _first_block_declared_compressed_size(encoded) < input.len() is true
   - Expected: lzma2_decompress_xz(encoded).unwrap() equals `input`
2.  assert host xz roundtrip


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
_ensure_tmp_root()
val input = _repeat_pattern([65u8, 66u8, 67u8], 277)
val options = default_compression_options(CompressionCodec.lzma2)
val encoded = lzma2_compress_xz(input, options)
expect(encoded[_first_block_data_start(encoded)]).to_equal(0xE0u8)
expect(_first_block_declared_compressed_size(encoded) < input.len()).to_equal(true)
expect(lzma2_decompress_xz(encoded).unwrap()).to_equal(input)
_assert_host_xz_roundtrip("triple-period-max-match", input, encoded)
```

</details>

#### falls back cleanly for four-byte periodic input outside the verified lane

1.  assert host xz roundtrip


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val input = _repeat_pattern([65u8, 66u8, 67u8, 68u8], 96)
val options = default_compression_options(CompressionCodec.lzma2)
val encoded = lzma2_compress_xz(input, options)
expect(encoded[_first_block_data_start(encoded)]).to_equal(0x01u8)
expect(lzma2_decompress_xz(encoded).unwrap()).to_equal(input)
_assert_host_xz_roundtrip("period-four-fallback", input, encoded)
```

</details>

#### falls back cleanly for five-byte periodic input outside the bounded encode lane

1.  assert host xz roundtrip


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val input = _repeat_pattern([65u8, 66u8, 67u8, 68u8, 69u8], 125)
val options = default_compression_options(CompressionCodec.lzma2)
val encoded = lzma2_compress_xz(input, options)
expect(encoded[_first_block_data_start(encoded)]).to_equal(0x01u8)
expect(lzma2_decompress_xz(encoded).unwrap()).to_equal(input)
_assert_host_xz_roundtrip("period-five-fallback", input, encoded)
```

</details>

#### falls back cleanly for mixed periodic data that breaks the bounded encode shape

1.  assert host xz roundtrip


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val input = _repeat_pattern([65u8, 66u8], 48) + [90u8, 91u8, 92u8] + _repeat_pattern([65u8, 66u8], 45)
val options = default_compression_options(CompressionCodec.lzma2)
val encoded = lzma2_compress_xz(input, options)
expect(encoded[_first_block_data_start(encoded)]).to_equal(0x01u8)
expect(lzma2_decompress_xz(encoded).unwrap()).to_equal(input)
_assert_host_xz_roundtrip("mixed-periodic-fallback", input, encoded)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/xz_lzma2_periodic_encode_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- xz lzma2 periodic encode

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
