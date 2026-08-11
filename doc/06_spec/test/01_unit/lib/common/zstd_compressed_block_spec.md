# Zstd Compressed Block Specification

> <details>

<!-- sdn-diagram:id=zstd_compressed_block_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=zstd_compressed_block_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

zstd_compressed_block_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=zstd_compressed_block_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 14 | 14 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Zstd Compressed Block Specification

## Scenarios

### zstd compressed blocks with zero sequences

#### decodes a compressed block containing raw literals and nbSeq == 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val frame = _zstd_frame(3, _compressed_block([
    0x18u8,
    0x61u8, 0x62u8, 0x63u8,
    0x00u8
]))
val decoded = zstd_decompress_frame(frame)
expect(decoded.is_err()).to_equal(false)
expect(decoded.unwrap()).to_equal([0x61u8, 0x62u8, 0x63u8])
```

</details>

#### decodes a compressed block containing RLE literals and nbSeq == 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val frame = _zstd_frame(4, _compressed_block([
    0x21u8,
    0x41u8,
    0x00u8
]))
val decoded = zstd_decompress_frame(frame)
expect(decoded.is_err()).to_equal(false)
expect(decoded.unwrap()).to_equal([0x41u8, 0x41u8, 0x41u8, 0x41u8])
```

</details>

#### rejects the host-rejected fresh-table single-stream direct-weight candidate

- ] +  exact direct weight literals payload
   - Expected: decoded.is_err() is true
-  expect compression error


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val frame = _zstd_frame(4, _compressed_block([
    0x42u8, 0x80u8, 0x01u8
] + _exact_direct_weight_literals_payload() + [
    0x00u8
]))
val decoded = zstd_decompress_frame(frame)
expect(decoded.is_err()).to_equal(true)
_expect_compression_error(decoded.unwrap_err(), "UnsupportedFeature", "fresh-table compressed literals")
```

</details>

#### rejects fresh-table four-stream compressed literals until the path is host-validated

-  expect compression error


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val frame = _zstd_frame(4, _compressed_block([
    0x46u8, 0x80u8, 0x01u8,
    0x84u8, 0x43u8, 0x20u8, 0x10u8,
    0x80u8, 0x0Du8,
    0x00u8
]))
val decoded = zstd_decompress_frame(frame)
expect(decoded.is_err()).to_equal(true)
_expect_compression_error(decoded.unwrap_err(), "UnsupportedFeature", "fresh-table compressed literals")
```

</details>

#### rejects fresh-table single-stream direct-weight payloads behind the 4-byte header form

-  expect compression error


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val frame = _zstd_frame(4, _compressed_block(_compressed_literals_header(2, 2, 4, 6) + _exact_direct_weight_literals_payload() + [
    0x00u8
]))
val decoded = zstd_decompress_frame(frame)
expect(decoded.is_err()).to_equal(true)
_expect_compression_error(decoded.unwrap_err(), "UnsupportedFeature", "fresh-table compressed literals")
```

</details>

#### rejects fresh-table single-stream direct-weight payloads with non-pinned literal bytes

-  expect compression error


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val frame = _zstd_frame(4, _compressed_block([
    0x42u8, 0x80u8, 0x01u8,
    0x84u8, 0x43u8, 0x20u8, 0x10u8,
    0x80u8, 0x0Cu8,
    0x00u8
]))
val decoded = zstd_decompress_frame(frame)
expect(decoded.is_err()).to_equal(true)
_expect_compression_error(decoded.unwrap_err(), "UnsupportedFeature", "fresh-table compressed literals")
```

</details>

#### rejects fresh-table single-stream direct-weight payloads with non-pinned regenerated size

- ] +  exact direct weight literals payload
   - Expected: decoded.is_err() is true
-  expect compression error


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val frame = _zstd_frame(5, _compressed_block([
    0x52u8, 0x80u8, 0x01u8
] + _exact_direct_weight_literals_payload() + [
    0x00u8
]))
val decoded = zstd_decompress_frame(frame)
expect(decoded.is_err()).to_equal(true)
_expect_compression_error(decoded.unwrap_err(), "UnsupportedFeature", "fresh-table compressed literals")
```

</details>

#### rejects fresh-table four-stream compressed literals with the 5-byte header form

-  expect compression error


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val frame = _zstd_frame(4, _compressed_block(_unsupported_literals_payload(2, 3)))
val decoded = zstd_decompress_frame(frame)
expect(decoded.is_err()).to_equal(true)
_expect_compression_error(decoded.unwrap_err(), "UnsupportedFeature", "fresh-table compressed literals")
```

</details>

#### rejects sequence-bearing compressed blocks explicitly

-  expect compression error


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val frame = _zstd_frame(3, _compressed_block([
    0x18u8,
    0x61u8, 0x62u8, 0x63u8,
    0x01u8
]))
val decoded = zstd_decompress_frame(frame)
expect(decoded.is_err()).to_equal(true)
_expect_compression_error(decoded.unwrap_err(), "TruncatedInput", "sequence")
```

</details>

#### rejects treeless single-stream compressed literals without prior Huffman state

-  expect compression error


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val frame = _zstd_frame(4, _compressed_block([
    0x43u8, 0x80u8, 0x01u8,
    0x84u8, 0x43u8, 0x20u8, 0x10u8,
    0x80u8, 0x0Du8,
    0x00u8
]))
val decoded = zstd_decompress_frame(frame)
expect(decoded.is_err()).to_equal(true)
_expect_compression_error(decoded.unwrap_err(), "UnsupportedFeature", "treeless literals")
```

</details>

#### rejects treeless four-stream compressed literals without prior Huffman state

-  expect compression error


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val frame = _zstd_frame(4, _compressed_block([
    0x47u8, 0x80u8, 0x01u8,
    0x84u8, 0x43u8, 0x20u8, 0x10u8,
    0x80u8, 0x0Du8,
    0x00u8
]))
val decoded = zstd_decompress_frame(frame)
expect(decoded.is_err()).to_equal(true)
_expect_compression_error(decoded.unwrap_err(), "UnsupportedFeature", "treeless literals")
```

</details>

#### rejects treeless single-stream compressed literals with the 4-byte header form

-  expect compression error


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val frame = _zstd_frame(4, _compressed_block(_unsupported_literals_payload(3, 2)))
val decoded = zstd_decompress_frame(frame)
expect(decoded.is_err()).to_equal(true)
_expect_compression_error(decoded.unwrap_err(), "UnsupportedFeature", "treeless literals")
```

</details>

#### rejects treeless four-stream compressed literals with the 5-byte header form

-  expect compression error


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val frame = _zstd_frame(4, _compressed_block(_unsupported_literals_payload(3, 3)))
val decoded = zstd_decompress_frame(frame)
expect(decoded.is_err()).to_equal(true)
_expect_compression_error(decoded.unwrap_err(), "UnsupportedFeature", "treeless literals")
```

</details>

#### keeps the former FSE-compressed Huffman-weight fresh-table fixture out of scope

-  expect compression error


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val frame = _zstd_frame(1, _compressed_block([
    0x12u8, 0x80u8, 0x00u8,
    0x01u8,
    0x01u8,
    0x00u8
]))
val decoded = zstd_decompress_frame(frame)
expect(decoded.is_err()).to_equal(true)
_expect_compression_error(decoded.unwrap_err(), "UnsupportedFeature", "fresh-table compressed literals")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/zstd_compressed_block_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- zstd compressed blocks with zero sequences

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 14 |
| Active scenarios | 14 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
