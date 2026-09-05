# Upx Byte Text Specification

> <details>

<!-- sdn-diagram:id=upx_byte_text_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=upx_byte_text_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

upx_byte_text_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=upx_byte_text_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Upx Byte Text Specification

## Scenarios

### nogc_sync_mut UPX path byte conversion

#### decodes path bytes without text.from_utf8

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val decoded = upx_path_bytes_to_text([47u8, 116u8, 109u8, 112u8, 47u8, 117u8, 112u8, 120u8, 10u8, 13u8, 9u8, 255u8])
expect(decoded).to_equal("/tmp/upx\n\r\t?")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_sync_mut/compression/upx_byte_text_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- nogc_sync_mut UPX path byte conversion

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
