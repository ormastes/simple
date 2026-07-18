# Convert Specification

> <details>

<!-- sdn-diagram:id=convert_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=convert_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

convert_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=convert_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Convert Specification

## Scenarios

### nogc_async_mut platform convert

#### guards truncated u32 byte arrays before fixed-position reads

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = nogc_platform_convert_source()
expect(source).to_contain("fn recv_bytes_u32(host: PlatformConfig, remote: PlatformConfig, bytes: [i64]) -> i64:")
expect(source).to_contain("if bytes.len() < 4:")
expect(source).to_contain("return 0")
expect(source).to_contain("val v0 = bytes[0]")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut/platform/convert_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- nogc_async_mut platform convert

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
