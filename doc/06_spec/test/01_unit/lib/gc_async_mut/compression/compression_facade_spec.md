# Compression Facade Specification

> <details>

<!-- sdn-diagram:id=compression_facade_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=compression_facade_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

compression_facade_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=compression_facade_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Compression Facade Specification

## Scenarios

### gc_async_mut compression facades

#### re-exports RLE helpers

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(rle_decode(rle_encode("aaaabbbcc"))).to_equal("aaaabbbcc")
expect(rle_decode_bytes(rle_encode_bytes([7, 7, 7, 8]))).to_equal([7, 7, 7, 8])
```

</details>

#### re-exports LZ77 helpers

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val compressed = lz77_compress("abcabcabc")
expect(lz77_decompress(compressed)).to_equal("abcabcabc")
```

</details>

#### re-exports gzip package helpers

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val payload: [u8] = [0x61u8, 0x62u8, 0x63u8, 0x61u8, 0x62u8, 0x63u8]
val compressed = gzip_compress(payload, 1)
val decompressed = gzip_decompress(compressed)

expect(gzip_is_compressed(compressed)).to_equal(true)
expect(_bytes_equal(decompressed, payload)).to_equal(true)
expect(crc32_calculate(payload)).to_be_greater_than(0)
```

</details>

#### re-exports brotli encoder and decoder helpers

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val payload: [u8] = [0x41u8, 0x42u8, 0x43u8, 0x44u8]
val encoded = brotli_encode_uncompressed(payload)
val decoded = brotli_decode(encoded)

expect(decoded.is_err()).to_equal(false)
expect(_bytes_equal(decoded.unwrap(), payload)).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/compression/compression_facade_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- gc_async_mut compression facades

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
