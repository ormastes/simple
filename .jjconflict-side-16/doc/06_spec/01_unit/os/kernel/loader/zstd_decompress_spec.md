# Zstd Decompress Specification

> 1. Err

<!-- sdn-diagram:id=zstd_decompress_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=zstd_decompress_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

zstd_decompress_spec -> std
zstd_decompress_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=zstd_decompress_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Zstd Decompress Specification

## Scenarios

### kernel zstd adapter

#### decodes frames produced by the shared compression module

1. Err


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val options = default_compression_options(CompressionCodec.zstd)
val encoded = compress_bytes(_fixture_bytes(), options)
val decoded = zstd_decompress(encoded)
match decoded:
    Ok(bytes): expect(bytes).to_equal(_fixture_bytes())
    Err(message): fail("zstd_decompress rejected a frame produced by compress_bytes: {message}")
```

</details>

#### returns stable shared decode errors for invalid frames

1. Ok


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val decoded = zstd_decompress([0x00u8, 0x01u8, 0x02u8, 0x03u8])
match decoded:
    Ok(_): fail("zstd_decompress accepted invalid frame bytes")
    Err(message): expect(message).to_contain("codec auto-detect failed")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/kernel/loader/zstd_decompress_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- kernel zstd adapter

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
