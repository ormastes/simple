# Zstd Single Sequence Compress Specification

> <details>

<!-- sdn-diagram:id=zstd_single_sequence_compress_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=zstd_single_sequence_compress_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

zstd_single_sequence_compress_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=zstd_single_sequence_compress_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Zstd Single Sequence Compress Specification

## Scenarios

### zstd repeated-tail encoder fallback

#### keeps the host-rejected direct-weight single-stream candidate on the raw-block path

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val payload = _fresh_table_payload()
val encoded = zstd_compress_frame(payload, default_compression_options(CompressionCodec.zstd))
expect((encoded[6] & 0x07u8)).to_equal(0x01u8)
expect(encoded.len()).to_equal(6 + 3 + payload.len())
expect(zstd_decompress_frame(encoded).unwrap()).to_equal(payload)
```

</details>

#### keeps level 1 on the raw-block path for the bounded fresh-table lane

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val payload = _fresh_table_payload()
val options = _with_level(default_compression_options(CompressionCodec.zstd), 1)
val encoded = zstd_compress_frame(payload, options)
expect((encoded[6] & 0x07u8)).to_equal(0x01u8)
expect(zstd_decompress_frame(encoded).unwrap()).to_equal(payload)
```

</details>

#### keeps repeated tails on the raw-block path until a host-valid sequence encoder exists

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val payload = _repeated_tail_payload()
val encoded = zstd_compress_frame(payload, default_compression_options(CompressionCodec.zstd))
expect((encoded[6] & 0x07u8)).to_equal(0x01u8)
expect(encoded.len()).to_equal(6 + 3 + payload.len())
expect(zstd_decompress_frame(encoded).unwrap()).to_equal(payload)
```

</details>

#### fails closed on an exact host-zstd fresh-table single-stream frame with one predefined-table sequence

1.  expect compression error


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(HOST_VALID_FRESH_TABLE_FRAME[9] & 0x03u8).to_equal(0x02u8)
expect((HOST_VALID_FRESH_TABLE_FRAME[9] >> 2u8) & 0x03u8).to_equal(0x00u8)
expect(HOST_VALID_FRESH_TABLE_FRAME[64]).to_equal(0x01u8)
val decoded = zstd_decompress_frame(HOST_VALID_FRESH_TABLE_FRAME)
expect(decoded.is_err()).to_equal(true)
_expect_compression_error(decoded.unwrap_err(), "UnsupportedFeature", "fresh-table compressed literals")
```

</details>

#### emits the exact raw-block frame bytes for repeated tails

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val payload = _repeated_tail_payload()
val encoded = zstd_compress_frame(payload, default_compression_options(CompressionCodec.zstd))
expect(encoded).to_equal([
    0x28u8, 0xB5u8, 0x2Fu8, 0xFDu8,
    0x20u8,
    0x0Cu8,
    0x61u8, 0x00u8, 0x00u8,
    0x61u8, 0x62u8, 0x63u8,
    0x61u8, 0x62u8, 0x63u8,
    0x61u8, 0x62u8, 0x63u8,
    0x61u8, 0x62u8, 0x63u8
])
```

</details>

#### keeps level 1 on the raw-block fallback

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val payload = _repeated_tail_payload()
val options = _with_level(default_compression_options(CompressionCodec.zstd), 1)
val encoded = zstd_compress_frame(payload, options)
expect((encoded[6] & 0x07u8)).to_equal(0x01u8)
expect(zstd_decompress_frame(encoded).unwrap()).to_equal(payload)
```

</details>

#### preserves checksum on the repeated-tail raw-block fallback

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val payload = _repeated_tail_payload()
val options = _with_checksum(default_compression_options(CompressionCodec.zstd), true)
val encoded = zstd_compress_frame(payload, options)
expect((encoded[6] & 0x07u8)).to_equal(0x01u8)
expect(zstd_decompress_frame(encoded).unwrap()).to_equal(payload)
```

</details>

#### fails closed on the host-rejected direct-weight single-stream candidate

1.  expect compression error


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val frame = _host_rejected_direct_weight_frame()
val decoded = zstd_decompress_frame(frame)
expect(decoded.is_err()).to_equal(true)
_expect_compression_error(decoded.unwrap_err(), "UnsupportedFeature", "fresh-table compressed literals")
```

</details>

#### host zstd rejects the direct-weight candidate bytes

1.  ensure tmp root
2.  write hex file
   - Expected: run.exit_code != 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
_ensure_tmp_root()
val compressed_path = TMP_ROOT + "/direct_weight_candidate.zst"
_write_hex_file(compressed_path, HOST_REJECTED_DIRECT_WEIGHT_FRAME_HEX)
val run = shell("zstd -q -d -f '" + compressed_path + "' -o '" + compressed_path + ".out'")
expect(run.exit_code != 0).to_equal(true)
```

</details>

#### host zstd accepts the pinned fresh-table single-stream frame

1.  ensure tmp root
2.  write hex file
3. print
4. print
   - Expected: run.exit_code equals `0`
   - Expected: _read_bytes(output_path) equals `[`


<details>
<summary>Executable SSpec</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
_ensure_tmp_root()
val compressed_path = TMP_ROOT + "/host_valid_fresh_table_frame.zst"
val output_path = TMP_ROOT + "/host_valid_fresh_table_frame.out"
_write_hex_file(compressed_path, HOST_VALID_FRESH_TABLE_FRAME_HEX)
val run = shell("zstd -q -d -f '" + compressed_path + "' -o '" + output_path + "'")
if run.exit_code != 0:
    print(run.stdout)
    print(run.stderr)
expect(run.exit_code).to_equal(0)
expect(_read_bytes(output_path)).to_equal([
    0x54u8, 0x68u8, 0x69u8, 0x73u8, 0x20u8, 0x69u8, 0x73u8, 0x20u8,
    0x61u8, 0x20u8, 0x73u8, 0x68u8, 0x6Fu8, 0x72u8, 0x74u8, 0x20u8,
    0x65u8, 0x6Eu8, 0x67u8, 0x6Cu8, 0x69u8, 0x73u8, 0x68u8, 0x20u8,
    0x73u8, 0x65u8, 0x6Eu8, 0x74u8, 0x65u8, 0x6Eu8, 0x63u8, 0x65u8,
    0x20u8, 0x77u8, 0x69u8, 0x74u8, 0x68u8, 0x20u8, 0x72u8, 0x65u8,
    0x70u8, 0x65u8, 0x61u8, 0x74u8, 0x65u8, 0x64u8, 0x20u8, 0x6Cu8,
    0x65u8, 0x74u8, 0x74u8, 0x65u8, 0x72u8, 0x73u8, 0x20u8, 0x61u8,
    0x6Eu8, 0x64u8, 0x20u8, 0x73u8, 0x70u8, 0x61u8, 0x63u8, 0x65u8,
    0x73u8, 0x2Eu8, 0x20u8, 0x54u8, 0x68u8, 0x69u8, 0x73u8, 0x20u8,
    0x69u8, 0x73u8, 0x20u8, 0x61u8, 0x20u8, 0x73u8, 0x68u8, 0x6Fu8,
    0x72u8, 0x74u8, 0x20u8, 0x65u8, 0x6Eu8, 0x67u8, 0x6Cu8, 0x69u8,
    0x73u8, 0x68u8, 0x20u8, 0x73u8, 0x65u8, 0x6Eu8, 0x74u8, 0x65u8,
    0x6Eu8, 0x63u8, 0x65u8, 0x20u8, 0x77u8, 0x69u8, 0x74u8, 0x68u8,
    0x20u8, 0x72u8, 0x65u8, 0x70u8, 0x65u8, 0x61u8, 0x74u8, 0x65u8,
    0x64u8, 0x20u8, 0x6Cu8, 0x65u8, 0x74u8, 0x74u8, 0x65u8, 0x72u8,
    0x73u8, 0x20u8, 0x61u8, 0x6Eu8, 0x64u8, 0x20u8, 0x73u8, 0x70u8,
    0x61u8, 0x63u8, 0x65u8, 0x73u8, 0x2Eu8, 0x20u8
])
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/zstd_single_sequence_compress_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- zstd repeated-tail encoder fallback

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
