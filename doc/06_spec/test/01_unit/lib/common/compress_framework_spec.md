# Compress Framework Specification

> 1. Err

<!-- sdn-diagram:id=compress_framework_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=compress_framework_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

compress_framework_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=compress_framework_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 24 | 24 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Compress Framework Specification

## Scenarios

### common compression framework

#### REQ-009: lz4 block round-trips with explicit hint

1. Err


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val options = default_compression_options(CompressionCodec.lz4)
val block_options = CompressionOptions(
    codec: options.codec,
    level: options.level,
    checksum: options.checksum,
    block_mode: "block",
    dictionary_bytes: options.dictionary_bytes,
    dictionary_id: options.dictionary_id,
    content_size: options.content_size
)
val input = _fixture_bytes()
val encoded = compress_bytes(input, block_options)
val decoded = decompress_bytes(encoded, Some(CompressionCodec.lz4))
match decoded:
    Ok(bytes): expect(bytes).to_equal(input)
    Err(_): fail("lz4 block should round-trip")
```

</details>

#### REQ-009: lz4 frame auto-detect round-trips

1. Err


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val options = default_compression_options(CompressionCodec.lz4)
val input = _fixture_bytes()
val encoded = compress_bytes(input, options)
val decoded = decompress_bytes(encoded, nil)
match decoded:
    Ok(bytes): expect(bytes).to_equal(input)
    Err(_): fail("lz4 frame should auto-detect and round-trip")
```

</details>

#### REQ-010: zstd frame round-trips through shared api

1. Err
2. print
3. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val options = default_compression_options(CompressionCodec.zstd)
val input = _fixture_bytes()
val encoded = compress_bytes(input, options)
val decoded = decompress_bytes(encoded, nil)
match decoded:
    Ok(bytes): expect(bytes).to_equal(input)
    Err(err):
        print(err)
        fail("zstd frame should round-trip")
```

</details>

#### REQ-011: xz lzma2 frame round-trips through shared api

1. Err


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val options = default_compression_options(CompressionCodec.lzma2)
expect(options.checksum).to_equal(true)
val input = _fixture_bytes()
val encoded = compress_bytes(input, options)
val decoded = decompress_bytes(encoded, nil)
match decoded:
    Ok(bytes): expect(bytes).to_equal(input)
    Err(_): fail("xz lzma2 frame should round-trip")
```

</details>

#### REQ-008: streaming encoder/decoder produces the original bytes

1. var encoder = new encoder state
2. encoder = encoder write
3. encoder = encoder write
4. var decoder = new decoder state
5. decoder = decoder write
6. Err
7. print
8. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val options = default_compression_options(CompressionCodec.zstd)
var encoder = new_encoder_state(options)
encoder = encoder_write(encoder, [0x61u8, 0x61u8, 0x61u8])
encoder = encoder_write(encoder, [0x62u8, 0x62u8, 0x62u8])
val encoded = encoder_finish(encoder)

var decoder = new_decoder_state(nil)
decoder = decoder_write(decoder, encoded)
val decoded_res = decoder_finish(decoder)
match decoded_res:
    Ok(bytes): expect(bytes).to_equal([0x61u8, 0x61u8, 0x61u8, 0x62u8, 0x62u8, 0x62u8])
    Err(err):
        print(err)
        fail("streaming zstd decoder should return original bytes")
```

</details>

#### REQ-012: checked api accepts zstd checksum requests and round-trips

<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val base = default_compression_options(CompressionCodec.zstd)
val options = CompressionOptions(
    codec: base.codec,
    level: base.level,
    checksum: true,
    block_mode: base.block_mode,
    dictionary_bytes: base.dictionary_bytes,
    dictionary_id: base.dictionary_id,
    content_size: base.content_size
)
val encoded_res = try_compress_bytes(_fixture_bytes(), options)
expect(encoded_res.is_err()).to_equal(false)
val decoded = decompress_bytes(encoded_res.unwrap(), Some(CompressionCodec.zstd))
expect(decoded.is_err()).to_equal(false)
expect(decoded.unwrap()).to_equal(_fixture_bytes())
```

</details>

#### REQ-012: checked api rejects unsupported dictionary metadata

1.  expect unsupported feature


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val base = default_compression_options(CompressionCodec.lz4)
val options = CompressionOptions(
    codec: base.codec,
    level: base.level,
    checksum: base.checksum,
    block_mode: "frame",
    dictionary_bytes: [0x61u8],
    dictionary_id: 7,
    content_size: base.content_size
)
_expect_unsupported_feature(try_compress_bytes(_fixture_bytes(), options), "dictionaries")
```

</details>

#### REQ-012: checked api rejects dictionary id without bytes

1.  expect unsupported feature


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val base = default_compression_options(CompressionCodec.zstd)
val options = CompressionOptions(
    codec: base.codec,
    level: base.level,
    checksum: base.checksum,
    block_mode: base.block_mode,
    dictionary_bytes: nil,
    dictionary_id: 99,
    content_size: base.content_size
)
_expect_unsupported_feature(try_compress_bytes(_fixture_bytes(), options), "dictionary_id requires dictionary_bytes")
```

</details>

#### REQ-012: checked api rejects negative dictionary ids before codec dispatch

1.  expect unsupported feature


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val base = default_compression_options(CompressionCodec.zstd)
val options = CompressionOptions(
    codec: base.codec,
    level: base.level,
    checksum: base.checksum,
    block_mode: base.block_mode,
    dictionary_bytes: [0x01u8],
    dictionary_id: -1,
    content_size: base.content_size
)
_expect_unsupported_feature(try_compress_bytes(_fixture_bytes(), options), "dictionary_id must be >= 0")
```

</details>

#### REQ-012: checked encoder finish preserves zstd checksum success

1. var encoder = new encoder state
2. encoder = encoder write
   - Expected: encoded.is_err() is false
   - Expected: decoded.is_err() is false
   - Expected: decoded.unwrap() equals `_fixture_bytes()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val base = default_compression_options(CompressionCodec.zstd)
val options = CompressionOptions(
    codec: base.codec,
    level: base.level,
    checksum: true,
    block_mode: base.block_mode,
    dictionary_bytes: base.dictionary_bytes,
    dictionary_id: base.dictionary_id,
    content_size: base.content_size
)
var encoder = new_encoder_state(options)
encoder = encoder_write(encoder, _fixture_bytes())
val encoded = encoder_finish_checked(encoder)
expect(encoded.is_err()).to_equal(false)
val decoded = decompress_bytes(encoded.unwrap(), Some(CompressionCodec.zstd))
expect(decoded.is_err()).to_equal(false)
expect(decoded.unwrap()).to_equal(_fixture_bytes())
```

</details>

#### REQ-012: checked encoder finish matches direct checked encode on success

1. var encoder = new encoder state
2. encoder = encoder write
3. encoder = encoder write
4. Ok
5. Err
6. Err


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val options = default_compression_options(CompressionCodec.zstd)
val input = _fixture_bytes()
var encoder = new_encoder_state(options)
encoder = encoder_write(encoder, input.slice(0, 10))
encoder = encoder_write(encoder, input.slice(10, input.len()))
val direct = try_compress_bytes(input, options)
val streamed = encoder_finish_checked(encoder)
match direct:
    Ok(direct_bytes):
        match streamed:
            Ok(streamed_bytes): expect(streamed_bytes).to_equal(direct_bytes)
            Err(_): fail("checked streaming encode should match direct encode")
    Err(_): fail("direct checked encode should succeed")
```

</details>

#### REQ-012: checked api rejects mismatched declared content size

1. content size:  fixture bytes
2.  expect unsupported feature


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val base = default_compression_options(CompressionCodec.lzma2)
val options = CompressionOptions(
    codec: base.codec,
    level: base.level,
    checksum: base.checksum,
    block_mode: base.block_mode,
    dictionary_bytes: base.dictionary_bytes,
    dictionary_id: base.dictionary_id,
    content_size: _fixture_bytes().len() + 1
)
_expect_unsupported_feature(try_compress_bytes(_fixture_bytes(), options), "content_size")
```

</details>

#### REQ-012: checked api rejects negative content size

1.  expect unsupported feature


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val base = default_compression_options(CompressionCodec.zstd)
val options = CompressionOptions(
    codec: base.codec,
    level: base.level,
    checksum: base.checksum,
    block_mode: base.block_mode,
    dictionary_bytes: base.dictionary_bytes,
    dictionary_id: base.dictionary_id,
    content_size: -1
)
_expect_unsupported_feature(try_compress_bytes(_fixture_bytes(), options), "content_size must be >= 0")
```

</details>

#### REQ-012: checked api rejects lz4 block checksum normalization

1.  expect unsupported feature


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val base = default_compression_options(CompressionCodec.lz4)
val options = CompressionOptions(
    codec: base.codec,
    level: base.level,
    checksum: true,
    block_mode: "block",
    dictionary_bytes: base.dictionary_bytes,
    dictionary_id: base.dictionary_id,
    content_size: base.content_size
)
_expect_unsupported_feature(try_compress_bytes(_fixture_bytes(), options), "block mode does not support checksum")
```

</details>

#### REQ-012: checked api rejects lz4 block content size normalization

1. content size:  fixture bytes
2.  expect unsupported feature


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val base = default_compression_options(CompressionCodec.lz4)
val options = CompressionOptions(
    codec: base.codec,
    level: base.level,
    checksum: base.checksum,
    block_mode: "block",
    dictionary_bytes: base.dictionary_bytes,
    dictionary_id: base.dictionary_id,
    content_size: _fixture_bytes().len()
)
_expect_unsupported_feature(try_compress_bytes(_fixture_bytes(), options), "block mode does not support content_size")
```

</details>

#### REQ-012: checked api rejects lz4 non-baseline levels

1. level: CompressionLevel
2.  expect unsupported feature


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val base = default_compression_options(CompressionCodec.lz4)
val options = CompressionOptions(
    codec: base.codec,
    level: CompressionLevel(value: 2),
    checksum: base.checksum,
    block_mode: base.block_mode,
    dictionary_bytes: base.dictionary_bytes,
    dictionary_id: base.dictionary_id,
    content_size: base.content_size
)
_expect_unsupported_feature(try_compress_bytes(_fixture_bytes(), options), "levels other than 1")
```

</details>

#### REQ-012: checked api keeps the supported lz4 baseline level round-tripping

1. level: CompressionLevel
   - Expected: encoded.is_err() is false
   - Expected: decoded.is_err() is false
   - Expected: decoded.unwrap() equals `_fixture_bytes()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val base = default_compression_options(CompressionCodec.lz4)
val options = CompressionOptions(
    codec: base.codec,
    level: CompressionLevel(value: 1),
    checksum: base.checksum,
    block_mode: base.block_mode,
    dictionary_bytes: base.dictionary_bytes,
    dictionary_id: base.dictionary_id,
    content_size: base.content_size
)
val encoded = try_compress_bytes(_fixture_bytes(), options)
expect(encoded.is_err()).to_equal(false)
val decoded = decompress_bytes(encoded.unwrap(), Some(CompressionCodec.lz4))
expect(decoded.is_err()).to_equal(false)
expect(decoded.unwrap()).to_equal(_fixture_bytes())
```

</details>

#### REQ-012: checked api rejects xz checksum disable requests

1.  expect unsupported feature


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val base = default_compression_options(CompressionCodec.lzma2)
val options = CompressionOptions(
    codec: base.codec,
    level: base.level,
    checksum: false,
    block_mode: base.block_mode,
    dictionary_bytes: base.dictionary_bytes,
    dictionary_id: base.dictionary_id,
    content_size: base.content_size
)
_expect_unsupported_feature(try_compress_bytes(_fixture_bytes(), options), "checksum=true")
```

</details>

#### REQ-012: checked api preserves supported non-default lzma2 levels

1. level: CompressionLevel
   - Expected: encoded.is_err() is false
   - Expected: decoded.is_err() is false
   - Expected: decoded.unwrap() equals `_fixture_bytes()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val base = default_compression_options(CompressionCodec.lzma2)
val options = CompressionOptions(
    codec: base.codec,
    level: CompressionLevel(value: 9),
    checksum: base.checksum,
    block_mode: base.block_mode,
    dictionary_bytes: base.dictionary_bytes,
    dictionary_id: base.dictionary_id,
    content_size: base.content_size
)
val encoded = try_compress_bytes(_fixture_bytes(), options)
expect(encoded.is_err()).to_equal(false)
val decoded = decompress_bytes(encoded.unwrap(), Some(CompressionCodec.lzma2))
expect(decoded.is_err()).to_equal(false)
expect(decoded.unwrap()).to_equal(_fixture_bytes())
```

</details>

#### REQ-012: checked encoder finish mirrors direct block-mode rejection

1. var encoder = new encoder state
2. encoder = encoder write
3.  expect same unsupported feature


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val base = default_compression_options(CompressionCodec.zstd)
val options = CompressionOptions(
    codec: base.codec,
    level: base.level,
    checksum: base.checksum,
    block_mode: "block",
    dictionary_bytes: base.dictionary_bytes,
    dictionary_id: base.dictionary_id,
    content_size: base.content_size
)
var encoder = new_encoder_state(options)
encoder = encoder_write(encoder, _fixture_bytes())
val direct = try_compress_bytes(_fixture_bytes(), options)
val streamed = encoder_finish_checked(encoder)
_expect_same_unsupported_feature(direct, streamed, "block_mode must be frame")
```

</details>

#### REQ-012: checked encoder finish mirrors direct dictionary rejection

1. var encoder = new encoder state
2. encoder = encoder write
3.  expect same unsupported feature


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val base = default_compression_options(CompressionCodec.lz4)
val options = CompressionOptions(
    codec: base.codec,
    level: base.level,
    checksum: base.checksum,
    block_mode: "frame",
    dictionary_bytes: [0xCAu8, 0xFEu8],
    dictionary_id: 12,
    content_size: base.content_size
)
var encoder = new_encoder_state(options)
encoder = encoder_write(encoder, _fixture_bytes())
val direct = try_compress_bytes(_fixture_bytes(), options)
val streamed = encoder_finish_checked(encoder)
_expect_same_unsupported_feature(direct, streamed, "dictionaries")
```

</details>

#### REQ-012: truncated lz4 frame fails closed

1. Ok
2. Err
3.  : fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val options = default_compression_options(CompressionCodec.lz4)
val input = _fixture_bytes()
val encoded = compress_bytes(input, options)
val truncated = encoded.slice(0, 6)
val result = decompress_bytes(truncated, nil)
match result:
    Ok(_): fail("truncated lz4 frame should fail closed")
    Err(err):
        match err:
            CompressionError.TruncatedInput(message): expect(message).to_contain("lz4 frame")
            CompressionError.InvalidHeader(message): expect(message).to_contain("lz4")
            _: fail("truncated lz4 frame should report truncation or invalid header")
```

</details>

#### REQ-010: shared zstd decoder accepts the emitted frame

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val input = _fixture_bytes()
val options = default_compression_options(CompressionCodec.zstd)
val encoded = compress_bytes(input, options)
val decoded = decompress_bytes(encoded, Some(CompressionCodec.zstd))
expect(decoded.is_err()).to_equal(false)
expect(decoded.unwrap()).to_equal(input)
```

</details>

#### REQ-011: shared xz decoder accepts the emitted stream

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val input = _fixture_bytes()
val options = default_compression_options(CompressionCodec.lzma2)
val encoded = compress_bytes(input, options)
val decoded = decompress_bytes(encoded, Some(CompressionCodec.lzma2))
expect(decoded.is_err()).to_equal(false)
expect(decoded.unwrap()).to_equal(input)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/compress_framework_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- common compression framework

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 24 |
| Active scenarios | 24 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
