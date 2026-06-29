# Common Compression Framework Facade Specification

> <details>

<!-- sdn-diagram:id=common_compression_framework_facade_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=common_compression_framework_facade_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

common_compression_framework_facade_spec -> std
common_compression_framework_facade_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=common_compression_framework_facade_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Common Compression Framework Facade Specification

## Scenarios

### common compression facade integration

#### keeps the kernel zstd adapter byte-identical with the public facade on deterministic frames

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val payload = _payload(4096)
val encoded = compress_bytes(payload, default_compression_options(CompressionCodec.zstd))
val facade = decompress_bytes(encoded, Some(CompressionCodec.zstd))
val adapter = zstd_decompress(encoded)
expect(facade.is_err()).to_equal(false)
expect(adapter.is_err()).to_equal(false)
expect(adapter.unwrap()).to_equal(facade.unwrap())
expect(adapter.unwrap()).to_equal(payload)
```

</details>

#### keeps the kernel zstd adapter aligned with concatenated-frame facade decode

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val left = compress_bytes(_payload(256), default_compression_options(CompressionCodec.zstd))
val right = compress_bytes(_payload(384), default_compression_options(CompressionCodec.zstd))
val combined = left + right
val facade = decompress_bytes(combined, Some(CompressionCodec.zstd))
val adapter = zstd_decompress(combined)
expect(facade.is_err()).to_equal(false)
expect(adapter.is_err()).to_equal(false)
expect(adapter.unwrap()).to_equal(facade.unwrap())
```

</details>

#### translates public checksum failures through the kernel adapter deterministically

1. var encoded = compress bytes
2. encoded[encoded len
   - Expected: facade.is_err() is true
   - Expected: adapter.is_err() is true
   - Expected: adapter.unwrap_err() equals `_error_text(facade.unwrap_err())`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val payload = _payload(1024)
var encoded = compress_bytes(payload, _zstd_checksum_options())
encoded[encoded.len() - 1] = encoded[encoded.len() - 1] ^ 0x01u8
val facade = decompress_bytes(encoded, Some(CompressionCodec.zstd))
val adapter = zstd_decompress(encoded)
expect(facade.is_err()).to_equal(true)
expect(adapter.is_err()).to_equal(true)
expect(adapter.unwrap_err()).to_equal(_error_text(facade.unwrap_err()))
```

</details>

#### translates public invalid-header failures through the kernel adapter deterministically

1. var encoded = compress bytes
   - Expected: facade.is_err() is true
   - Expected: adapter.is_err() is true
   - Expected: adapter.unwrap_err() equals `_error_text(facade.unwrap_err())`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val payload = _payload(128)
var encoded = compress_bytes(payload, default_compression_options(CompressionCodec.zstd))
encoded[0] = encoded[0] ^ 0x01u8
val facade = decompress_bytes(encoded, Some(CompressionCodec.zstd))
val adapter = zstd_decompress(encoded)
expect(facade.is_err()).to_equal(true)
expect(adapter.is_err()).to_equal(true)
expect(adapter.unwrap_err()).to_equal(_error_text(facade.unwrap_err()))
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/02_integration/core/common_compression_framework_facade_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- common compression facade integration

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
