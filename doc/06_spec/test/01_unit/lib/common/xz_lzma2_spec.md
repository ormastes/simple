# Xz Lzma2 Specification

> 1.  ensure tmp root

<!-- sdn-diagram:id=xz_lzma2_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=xz_lzma2_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

xz_lzma2_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=xz_lzma2_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 20 | 20 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Xz Lzma2 Specification

## Scenarios

### xz lzma2 codec

#### round-trips and host-xz decodes a framed stream

1.  ensure tmp root
   - Expected: decoded.is_err() is false
   - Expected: decoded.unwrap() equals `input`
2.  write bytes via hex shell
3.  write bytes via hex shell
4. print
5. print
   - Expected: run.exit_code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
_ensure_tmp_root()
val input = _payload(8192)
val options = default_compression_options(CompressionCodec.lzma2)
val encoded = lzma2_compress_xz(input, options)
val decoded = lzma2_decompress_xz(encoded)
expect(decoded.is_err()).to_equal(false)
expect(decoded.unwrap()).to_equal(input)

val compressed_path = TMP_ROOT + "/multiblock.xz"
val input_path = TMP_ROOT + "/multiblock.input"
val output_path = TMP_ROOT + "/multiblock.out"
_write_bytes_via_hex_shell(compressed_path, encoded)
_write_bytes_via_hex_shell(input_path, input)
val run = shell(
    "sh -c \"xz -q -d -f -c '" + compressed_path + "' > '" + output_path + "' && cmp -s '" + input_path + "' '" + output_path + "'\""
)
if run.exit_code != 0:
    print(run.stdout)
    print(run.stderr)
expect(run.exit_code).to_equal(0)
```

</details>

#### keeps xz framing and decode parity across scalar avx2 and neon tiers

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val input = _payload(2048)
val options = default_compression_options(CompressionCodec.lzma2)
val scalar = lzma2_compress_xz_for_tier(input, options, CompressionSimdTier.scalar)
val avx2 = lzma2_compress_xz_for_tier(input, options, CompressionSimdTier.avx2)
val neon = lzma2_compress_xz_for_tier(input, options, CompressionSimdTier.neon)
expect(avx2).to_equal(scalar)
expect(neon).to_equal(scalar)
expect(lzma2_compress_xz(input, options)).to_equal(scalar)
expect(lzma2_decompress_xz_for_tier(scalar, CompressionSimdTier.scalar).unwrap()).to_equal(input)
expect(lzma2_decompress_xz_for_tier(scalar, CompressionSimdTier.avx2).unwrap()).to_equal(input)
expect(lzma2_decompress_xz_for_tier(scalar, CompressionSimdTier.neon).unwrap()).to_equal(input)
```

</details>

#### emits a real compressed lzma2 chunk for repeated-byte runs when that beats the raw chunk

1.  ensure tmp root
   - Expected: encoded[_first_block_data_start(encoded)] equals `0xE0u8`
   - Expected: _first_block_declared_compressed_size(encoded) < input.len() is true
   - Expected: decoded.is_err() is false
   - Expected: decoded.unwrap() equals `input`
2.  write bytes via hex shell
3.  write bytes via hex shell
4. print
5. print
   - Expected: run.exit_code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
_ensure_tmp_root()
val input = _repeat_byte(65u8, 275)
val options = default_compression_options(CompressionCodec.lzma2)
val encoded = lzma2_compress_xz(input, options)
expect(encoded[_first_block_data_start(encoded)]).to_equal(0xE0u8)
expect(_first_block_declared_compressed_size(encoded) < input.len()).to_equal(true)
val decoded = lzma2_decompress_xz(encoded)
expect(decoded.is_err()).to_equal(false)
expect(decoded.unwrap()).to_equal(input)

val compressed_path = TMP_ROOT + "/repeat-byte-run.xz"
val input_path = TMP_ROOT + "/repeat-byte-run.input"
val output_path = TMP_ROOT + "/repeat-byte-run.out"
_write_bytes_via_hex_shell(compressed_path, encoded)
_write_bytes_via_hex_shell(input_path, input)
val run = shell(
    "sh -c \"xz -q -d -f -c '" + compressed_path + "' > '" + output_path + "' && cmp -s '" + input_path + "' '" + output_path + "'\""
)
if run.exit_code != 0:
    print(run.stdout)
    print(run.stderr)
expect(run.exit_code).to_equal(0)
```

</details>

#### rejects misaligned xz stream padding

1.  expect compression error


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val options = default_compression_options(CompressionCodec.lzma2)
val left = lzma2_compress_xz(_payload(64), options)
val right = lzma2_compress_xz(_payload(96), options)
val combined = left + [0x00u8] + right
val decoded = lzma2_decompress_xz(combined)
expect(decoded.is_err()).to_equal(true)
_expect_compression_error(decoded.unwrap_err(), "CorruptStream", "stream padding")
```

</details>

#### decodes concatenated xz streams with aligned stream padding

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val options = default_compression_options(CompressionCodec.lzma2)
val left_payload = _payload(128)
val right_payload = _payload(192)
val left = lzma2_compress_xz(left_payload, options)
val right = lzma2_compress_xz(right_payload, options)
val combined = left + [0x00u8, 0x00u8, 0x00u8, 0x00u8] + right
val decoded = lzma2_decompress_xz(combined)
expect(decoded.is_err()).to_equal(false)
expect(decoded.unwrap()).to_equal(left_payload + right_payload)
```

</details>

#### rejects unsupported non-lzma2 filter chains with a typed error

1. var encoded = lzma2 compress xz
2. encoded =  repair first block header crc
   - Expected: decoded.is_err() is true
3.  expect compression error


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val options = default_compression_options(CompressionCodec.lzma2)
var encoded = lzma2_compress_xz(_payload(128), options)
val filter_id_pos = _first_filter_id_pos(encoded)
encoded[filter_id_pos] = 0x22u8
encoded = _repair_first_block_header_crc(encoded)
val decoded = lzma2_decompress_xz(encoded)
expect(decoded.is_err()).to_equal(true)
_expect_compression_error(decoded.unwrap_err(), "UnsupportedFeature", "filter chains")
```

</details>

#### rejects compressed lzma2 chunk controls explicitly

1. var encoded = lzma2 compress xz
2. encoded[ first block data start
   - Expected: decoded.is_err() is true
3.  expect compression error


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val options = default_compression_options(CompressionCodec.lzma2)
var encoded = lzma2_compress_xz(_payload(128), options)
encoded[_first_block_data_start(encoded)] = 0x80u8
val decoded = lzma2_decompress_xz(encoded)
expect(decoded.is_err()).to_equal(true)
_expect_compression_error(decoded.unwrap_err(), "CorruptStream", "dictionary reset")
```

</details>

#### rejects invalid non-terminal lzma2 control bytes explicitly

1. var encoded = lzma2 compress xz
2. encoded[ first block data start
   - Expected: decoded.is_err() is true
3.  expect compression error


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val options = default_compression_options(CompressionCodec.lzma2)
var encoded = lzma2_compress_xz(_payload(128), options)
encoded[_first_block_data_start(encoded)] = 0x03u8
val decoded = lzma2_decompress_xz(encoded)
expect(decoded.is_err()).to_equal(true)
_expect_compression_error(decoded.unwrap_err(), "CorruptStream", "control")
```

</details>

#### rejects compressed lzma2 chunks without required new properties in the first chunk

1. lzma2 compress xz
   - Expected: decoded.is_err() is true
2.  expect compression error


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val options = default_compression_options(CompressionCodec.lzma2)
val encoded = _replace_first_chunk_prefix(
    lzma2_compress_xz(_payload(128), options),
    [0xA0u8, 0x00u8, 0x00u8, 0x00u8, 0x04u8]
)
val decoded = lzma2_decompress_xz(encoded)
expect(decoded.is_err()).to_equal(true)
_expect_compression_error(decoded.unwrap_err(), "CorruptStream", "properties")
```

</details>

#### rejects too-short compressed lzma2 payloads after parsing their headers

1. lzma2 compress xz
   - Expected: decoded.is_err() is true
2.  expect compression error


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val options = default_compression_options(CompressionCodec.lzma2)
val encoded = _replace_first_chunk_prefix(
    lzma2_compress_xz(_payload(128), options),
    [0xE0u8, 0x00u8, 0x00u8, 0x00u8, 0x03u8, 0x00u8]
)
val decoded = lzma2_decompress_xz(encoded)
expect(decoded.is_err()).to_equal(true)
_expect_compression_error(decoded.unwrap_err(), "CorruptStream", "compressed chunk size")
```

</details>

#### rejects invalid compressed lzma2 property bytes

1. lzma2 compress xz
   - Expected: decoded.is_err() is true
2.  expect compression error


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val options = default_compression_options(CompressionCodec.lzma2)
val encoded = _replace_first_chunk_prefix(
    lzma2_compress_xz(_payload(128), options),
    [0xE0u8, 0x00u8, 0x00u8, 0x00u8, 0x04u8, 0x29u8]
)
val decoded = lzma2_decompress_xz(encoded)
expect(decoded.is_err()).to_equal(true)
_expect_compression_error(decoded.unwrap_err(), "CorruptStream", "properties")
```

</details>

#### rejects malformed compressed lzma2 range-decoder init bytes before unsupported-feature fallback

1. lzma2 compress xz
   - Expected: decoded.is_err() is true
2.  expect compression error


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val options = default_compression_options(CompressionCodec.lzma2)
val encoded = _replace_first_chunk_prefix(
    lzma2_compress_xz(_payload(128), options),
    [0xE0u8, 0x00u8, 0x00u8, 0x00u8, 0x04u8, 0x00u8, 0x01u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8]
)
val decoded = lzma2_decompress_xz(encoded)
expect(decoded.is_err()).to_equal(true)
_expect_compression_error(decoded.unwrap_err(), "CorruptStream", "range decoder init")
```

</details>

#### parses compressed lzma2 chunk headers before falling back on body decode

1. lzma2 compress xz
   - Expected: decoded.is_err() is true
2.  expect compression error


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# The fabricated chunk uses an unsupported props byte (0x00 -> LCLPPB
# 0/0/0) that the new range decoder rejects with the explicit
# LCLPPB-other-than-3/0/2 error string per the partial-LANDED scope.
val options = default_compression_options(CompressionCodec.lzma2)
val encoded = _replace_first_chunk_prefix(
    lzma2_compress_xz(_payload(128), options),
    [0xE0u8, 0x00u8, 0x00u8, 0x00u8, 0x04u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8]
)
val decoded = lzma2_decompress_xz(encoded)
expect(decoded.is_err()).to_equal(true)
_expect_compression_error(decoded.unwrap_err(), "UnsupportedFeature", "LZMA2 LCLPPB other than 3/0/2")
```

</details>

#### reports footer crc corruption as a checksum mismatch

1. var encoded = lzma2 compress xz
2. encoded[encoded len
   - Expected: decoded.is_err() is true
3.  expect compression error


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val options = default_compression_options(CompressionCodec.lzma2)
var encoded = lzma2_compress_xz(_payload(128), options)
encoded[encoded.len() - 12] = encoded[encoded.len() - 12] ^ 0x01u8
val decoded = lzma2_decompress_xz(encoded)
expect(decoded.is_err()).to_equal(true)
_expect_compression_error(decoded.unwrap_err(), "ChecksumMismatch", "footer crc32")
```

</details>

#### reports header crc corruption as a checksum mismatch

1. var encoded = lzma2 compress xz
   - Expected: decoded.is_err() is true
2.  expect compression error


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val options = default_compression_options(CompressionCodec.lzma2)
var encoded = lzma2_compress_xz(_payload(128), options)
encoded[8] = encoded[8] ^ 0x01u8
val decoded = lzma2_decompress_xz(encoded)
expect(decoded.is_err()).to_equal(true)
_expect_compression_error(decoded.unwrap_err(), "ChecksumMismatch", "xz header crc32")
```

</details>

#### reports block crc corruption as a checksum mismatch

1. var encoded = lzma2 compress xz
   - Expected: decoded.is_err() is true
2.  expect compression error


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val options = default_compression_options(CompressionCodec.lzma2)
var encoded = lzma2_compress_xz(_payload(128), options)
val check_pos = _first_block_check_pos(encoded)
encoded[check_pos] = encoded[check_pos] ^ 0x01u8
val decoded = lzma2_decompress_xz(encoded)
expect(decoded.is_err()).to_equal(true)
_expect_compression_error(decoded.unwrap_err(), "ChecksumMismatch", "xz block crc32")
```

</details>

#### reports host-default crc64 block corruption as a checksum mismatch

1.  ensure tmp root
2.  write bytes
3. print
4. print
   - Expected: run.exit_code equals `0`
5. var encoded =  read bytes
   - Expected: decoded.is_err() is true
6.  expect compression error


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
_ensure_tmp_root()
val input = _payload(256)
val input_path = TMP_ROOT + "/crc64-check-input.bin"
val compressed_path = TMP_ROOT + "/crc64-check.xz"
_write_bytes(input_path, input)
val run = shell("xz -q -z -f -c '" + input_path + "' > '" + compressed_path + "'")
if run.exit_code != 0:
    print(run.stdout)
    print(run.stderr)
expect(run.exit_code).to_equal(0)
var encoded = _read_bytes(compressed_path)
val check_pos = _single_stream_crc64_check_pos(encoded)
encoded[check_pos] = encoded[check_pos] ^ 0x01u8
val decoded = lzma2_decompress_xz(encoded)
expect(decoded.is_err()).to_equal(true)
_expect_compression_error(decoded.unwrap_err(), "ChecksumMismatch", "xz block crc64")
```

</details>

#### reports index crc corruption as a checksum mismatch

1. var encoded = lzma2 compress xz
   - Expected: decoded.is_err() is true
2.  expect compression error


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val options = default_compression_options(CompressionCodec.lzma2)
var encoded = lzma2_compress_xz(_payload(128), options)
val footer_start = encoded.len() - 12
encoded[footer_start - 1] = encoded[footer_start - 1] ^ 0x01u8
val decoded = lzma2_decompress_xz(encoded)
expect(decoded.is_err()).to_equal(true)
_expect_compression_error(decoded.unwrap_err(), "ChecksumMismatch", "xz index crc32")
```

</details>

#### reports truncated block checks before unsupported compressed-chunk fallback

1. lzma2 compress xz
2. encoded = encoded slice
   - Expected: decoded.is_err() is true
3.  expect compression error


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val options = default_compression_options(CompressionCodec.lzma2)
var encoded = _replace_first_chunk_prefix(
    lzma2_compress_xz(_payload(128), options),
    [0xE0u8, 0x00u8, 0x00u8, 0x00u8, 0x04u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8]
)
encoded = encoded.slice(0, _first_block_check_pos(encoded) + 2)
val decoded = lzma2_decompress_xz(encoded)
expect(decoded.is_err()).to_equal(true)
_expect_compression_error(decoded.unwrap_err(), "TruncatedInput", "xz block check")
```

</details>

#### decodes host-generated compressed xz streams via the pure-Simple range decoder

1.  ensure tmp root
2.  write bytes
3. print
4. print
   - Expected: run.exit_code equals `0`
   - Expected: decoded.is_err() is false
   - Expected: decoded.unwrap() equals `input`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
_ensure_tmp_root()
val input = _payload(256)
val input_path = TMP_ROOT + "/host-generated-input.bin"
val compressed_path = TMP_ROOT + "/host-generated.xz"
_write_bytes(input_path, input)
val run = shell("xz -q -z -f -c '" + input_path + "' > '" + compressed_path + "'")
if run.exit_code != 0:
    print(run.stdout)
    print(run.stderr)
expect(run.exit_code).to_equal(0)
val encoded = _read_bytes(compressed_path)
val decoded = lzma2_decompress_xz(encoded)
expect(decoded.is_err()).to_equal(false)
expect(decoded.unwrap()).to_equal(input)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/xz_lzma2_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- xz lzma2 codec

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 20 |
| Active scenarios | 20 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
