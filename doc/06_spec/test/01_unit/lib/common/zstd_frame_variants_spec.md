# Zstd Frame Variants Specification

> <details>

<!-- sdn-diagram:id=zstd_frame_variants_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=zstd_frame_variants_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

zstd_frame_variants_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=zstd_frame_variants_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 19 | 19 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Zstd Frame Variants Specification

## Scenarios

### zstd frame header variants

#### keeps the current pure-Simple framed subset in parity across scalar avx2 and neon tiers

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val payload = [0x61u8, 0x62u8, 0x63u8, 0x64u8, 0x65u8, 0x66u8]
val options = default_compression_options(CompressionCodec.zstd)
val scalar = zstd_compress_frame_for_tier(payload, options, CompressionSimdTier.scalar)
val avx2 = zstd_compress_frame_for_tier(payload, options, CompressionSimdTier.avx2)
val neon = zstd_compress_frame_for_tier(payload, options, CompressionSimdTier.neon)
expect(avx2).to_equal(scalar)
expect(neon).to_equal(scalar)
expect(zstd_compress_frame(payload, options)).to_equal(scalar)
expect(zstd_decompress_frame_for_tier(scalar, CompressionSimdTier.scalar).unwrap()).to_equal(payload)
expect(zstd_decompress_frame_for_tier(scalar, CompressionSimdTier.avx2).unwrap()).to_equal(payload)
expect(zstd_decompress_frame_for_tier(scalar, CompressionSimdTier.neon).unwrap()).to_equal(payload)
expect(zstd_decompress_frame(scalar).unwrap()).to_equal(payload)
```

</details>

#### emits frame-level content checksums for the current encoder path

<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
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
val payload = [0x41u8, 0x42u8, 0x43u8, 0x44u8, 0x45u8]
val encoded = zstd_compress_frame(payload, options)
expect((encoded[4] & 0x04u8) != 0u8).to_equal(true)
val decoded = zstd_decompress_frame(encoded)
expect(decoded.is_err()).to_equal(false)
expect(decoded.unwrap()).to_equal(payload)
```

</details>

#### emits the checksum trailer even for empty payloads

<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
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
val encoded = zstd_compress_frame([], options)
expect((encoded[4] & 0x04u8) != 0u8).to_equal(true)
expect(encoded.len()).to_equal(13)
val decoded = zstd_decompress_frame(encoded)
expect(decoded.is_err()).to_equal(false)
expect(decoded.unwrap()).to_equal([])
```

</details>

#### emits the compact 1-byte single-segment size form for small payloads

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val payload = [0x61u8, 0x62u8, 0x63u8]
val encoded = zstd_compress_frame(payload, default_compression_options(CompressionCodec.zstd))
expect(encoded[4]).to_equal(0x20u8)
expect(encoded[5]).to_equal(payload.len().to_u8())
expect(zstd_decompress_frame(encoded).unwrap()).to_equal(payload)
```

</details>

#### emits the compact 2-byte single-segment size form once the payload reaches 256 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val payload = _repeated_bytes(0x5Au8, 300)
val encoded = zstd_compress_frame(payload, default_compression_options(CompressionCodec.zstd))
expect(encoded[4]).to_equal(0x60u8)
expect(encoded[5]).to_equal((payload.len() - 256).to_u8())
expect(encoded[6]).to_equal(0u8)
expect(zstd_decompress_frame(encoded).unwrap()).to_equal(payload)
```

</details>

#### keeps the 4-byte single-segment size form for larger payloads

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val payload = rt_bytes_alloc(65792)
val encoded = zstd_compress_frame(payload, default_compression_options(CompressionCodec.zstd))
expect(encoded[4]).to_equal(0xA0u8)
expect(encoded[5]).to_equal((payload.len() & 0xFF).to_u8())
expect(encoded[6]).to_equal(((payload.len() >> 8) & 0xFF).to_u8())
expect(encoded[7]).to_equal(((payload.len() >> 16) & 0xFF).to_u8())
expect(encoded[8]).to_equal(((payload.len() >> 24) & 0xFF).to_u8())
expect((encoded[9] & 0x07u8)).to_equal(0x03u8)
expect(encoded[12]).to_equal(0u8)
```

</details>

#### decodes the repeated-tail raw-block fallback

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val payload = _repeated_tail_payload()
val encoded = zstd_compress_frame(payload, default_compression_options(CompressionCodec.zstd))
expect((encoded[6] & 0x07u8)).to_equal(0x01u8)
expect(zstd_decompress_frame(encoded).unwrap()).to_equal(payload)
```

</details>

#### decodes single-segment frames with 1-byte content size

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val payload = [0x61u8, 0x62u8, 0x63u8]
val frame = _frame(0x20u8, [payload.len().to_u8()], payload, false)
val decoded = decompress_bytes(frame, Some(CompressionCodec.zstd))
expect(decoded.is_err()).to_equal(false)
expect(decoded.unwrap()).to_equal(payload)
```

</details>

#### decodes single-segment frames with 8-byte content size

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val payload = [0x21u8, 0x22u8, 0x23u8, 0x24u8, 0x25u8]
val frame = _frame(0xE0u8, _write_u64_le(payload.len().to_u64()), payload, false)
val decoded = decompress_bytes(frame, Some(CompressionCodec.zstd))
expect(decoded.is_err()).to_equal(false)
expect(decoded.unwrap()).to_equal(payload)
```

</details>

#### decodes single-segment frames with 2-byte content size

1.
2.
   - Expected: decoded.is_err() is false
   - Expected: decoded.unwrap() equals `payload`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val payload = _repeated_bytes(0x5Au8, 300)
val encoded_size = payload.len() - 256
val frame = _frame(
    0x60u8,
    [
        (encoded_size & 0xFF).to_u8(),
        ((encoded_size >> 8) & 0xFF).to_u8()
    ],
    payload,
    false
)
val decoded = decompress_bytes(frame, Some(CompressionCodec.zstd))
expect(decoded.is_err()).to_equal(false)
expect(decoded.unwrap()).to_equal(payload)
```

</details>

#### decodes non-single-segment frames with a window descriptor

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val payload = [0x41u8, 0x42u8, 0x43u8, 0x44u8]
val frame = _frame(0x00u8, [0x00u8], payload, false)
val decoded = decompress_bytes(frame, Some(CompressionCodec.zstd))
expect(decoded.is_err()).to_equal(false)
expect(decoded.unwrap()).to_equal(payload)
```

</details>

#### verifies frame-level content checksums

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val payload = [0x31u8, 0x32u8, 0x33u8, 0x34u8]
val frame = _frame(0x24u8, [payload.len().to_u8()], payload, true)
val decoded = decompress_bytes(frame, Some(CompressionCodec.zstd))
expect(decoded.is_err()).to_equal(false)
expect(decoded.unwrap()).to_equal(payload)
```

</details>

#### rejects dictionary-backed frames explicitly

1.  expect error contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val payload = [0x51u8, 0x52u8]
val frame = _frame(0x21u8, [0x09u8, payload.len().to_u8()], payload, false)
_expect_error_contains(decompress_bytes(frame, Some(CompressionCodec.zstd)), "UnsupportedFeature", "dictionary")
```

</details>

#### decodes dictionary-backed frames when the matching external dictionary is supplied directly

<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val frame = ZSTD_MAGIC_BYTES + [
    0xA3u8,
    0x78u8, 0x56u8, 0x34u8, 0x12u8,
    0x0Cu8, 0x00u8, 0x00u8, 0x00u8,
    0x61u8, 0x00u8, 0x00u8,
    0x48u8, 0x45u8, 0x4Cu8, 0x4Cu8,
    0x4Fu8, 0x5Fu8, 0x44u8, 0x49u8,
    0x43u8, 0x54u8, 0x21u8, 0x21u8
]
val decoded = zstd_decompress_frame_with_dictionary(frame, DICT_OK, DICT_OK_ID)
expect(decoded.is_err()).to_equal(false)
expect(decoded.unwrap()).to_equal([
    0x48u8, 0x45u8, 0x4Cu8, 0x4Cu8,
    0x4Fu8, 0x5Fu8, 0x44u8, 0x49u8,
    0x43u8, 0x54u8, 0x21u8, 0x21u8
])
```

</details>

#### fails closed when a dictionary-backed frame is decoded with the wrong dictionary id

1.  expect error contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val frame = ZSTD_MAGIC_BYTES + [
    0x21u8,
    0x09u8,
    0x03u8,
    0x23u8, 0x00u8, 0x00u8,
    0x00u8,
    0x01u8,
    0x14u8,
    0x02u8, 0x00u8,
    0x01u8
]
_expect_error_contains(zstd_decompress_frame_with_dictionary(frame, DICT_OK, 8), "CorruptStream", "dictionary id mismatch")
```

</details>

#### accepts frames that carry an explicit zero dictionary id

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val payload = [0x71u8, 0x72u8]
val frame = _frame(0x21u8, [0x00u8, payload.len().to_u8()], payload, false)
val decoded = decompress_bytes(frame, Some(CompressionCodec.zstd))
expect(decoded.is_err()).to_equal(false)
expect(decoded.unwrap()).to_equal(payload)
```

</details>

#### decodes concatenated frames in one buffer

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val left = _frame(0x20u8, [2u8], [0x61u8, 0x62u8], false)
val right = _frame(0x20u8, [3u8], [0x63u8, 0x64u8, 0x65u8], false)
val decoded = decompress_bytes(left + right, Some(CompressionCodec.zstd))
expect(decoded.is_err()).to_equal(false)
expect(decoded.unwrap()).to_equal([0x61u8, 0x62u8, 0x63u8, 0x64u8, 0x65u8])
```

</details>

#### fails closed on a corrupt content checksum

1. var frame =  frame
2. frame[frame len
3.  expect error contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val payload = [0x90u8, 0x91u8, 0x92u8]
var frame = _frame(0x24u8, [payload.len().to_u8()], payload, true)
frame[frame.len() - 1] = frame[frame.len() - 1] ^ 0x01u8
_expect_error_contains(decompress_bytes(frame, Some(CompressionCodec.zstd)), "ChecksumMismatch", "checksum")
```

</details>

#### decodes a host-generated frame for a mixed payload

1.  ensure tmp root
2. payload push
3. payload push
4. payload push
5. payload push
6.  write bytes
7. print
8. print
   - Expected: run.exit_code equals `0`
   - Expected: decoded.is_err() is false
   - Expected: decoded.unwrap() equals `payload`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
_ensure_tmp_root()
var payload: [u8] = []
var i = 0
while i < 4096:
    payload.push(((i * 17 + (i / 7)) % 251).to_u8())
    payload.push(0x61u8 + (i % 5).to_u8())
    payload.push(0x61u8 + (i % 5).to_u8())
    payload.push(0x20u8)
    i = i + 1
val input_path = TMP_ROOT + "/mixed.bin"
val compressed_path = TMP_ROOT + "/mixed.zst"
_write_bytes(input_path, payload)
val run = shell("zstd -q --no-check -19 -f '" + input_path + "' -o '" + compressed_path + "'")
if run.exit_code != 0:
    print(run.stdout)
    print(run.stderr)
expect(run.exit_code).to_equal(0)
val decoded = decompress_bytes(_read_bytes(compressed_path), Some(CompressionCodec.zstd))
expect(decoded.is_err()).to_equal(false)
expect(decoded.unwrap()).to_equal(payload)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/zstd_frame_variants_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- zstd frame header variants

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 19 |
| Active scenarios | 19 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
