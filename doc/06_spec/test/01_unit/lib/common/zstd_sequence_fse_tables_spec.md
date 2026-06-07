# Zstd Sequence Fse Tables Specification

> <details>

<!-- sdn-diagram:id=zstd_sequence_fse_tables_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=zstd_sequence_fse_tables_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

zstd_sequence_fse_tables_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=zstd_sequence_fse_tables_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Zstd Sequence Fse Tables Specification

## Scenarios

### zstd sequence fse table parsing gates

#### rejects truncated predefined sequence data

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val frame = _zstd_frame(3, _compressed_block(_raw_literals_prefix() + [0x01u8, 0x00u8]))
val decoded = decompress_bytes(frame, Some(CompressionCodec.zstd))
expect(decoded.is_err()).to_equal(true)
```

</details>

#### rejects truncated fse-compressed ll/ml table data

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val frame = _zstd_frame(3, _compressed_block(_raw_literals_prefix() + [
    0x01u8,
    0x88u8,
    0x10u8, 0x3Fu8,
    0x10u8, 0x3Fu8
]))
val decoded = decompress_bytes(frame, Some(CompressionCodec.zstd))
expect(decoded.is_err()).to_equal(true)
```

</details>

#### fails closed on truncated fse table descriptions

1.  expect compression error


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val frame = _zstd_frame(3, _compressed_block(_raw_literals_prefix() + [
    0x01u8,
    0x80u8,
    0x10u8
]))
val decoded = decompress_bytes(frame, Some(CompressionCodec.zstd))
expect(decoded.is_err()).to_equal(true)
_expect_compression_error(decoded.unwrap_err(), "TruncatedInput", "normalized counts")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/zstd_sequence_fse_tables_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- zstd sequence fse table parsing gates

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
