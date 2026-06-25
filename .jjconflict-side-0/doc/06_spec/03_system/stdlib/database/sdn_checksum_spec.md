# Sdn Checksum Specification

> <details>

<!-- sdn-diagram:id=sdn_checksum_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=sdn_checksum_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

sdn_checksum_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=sdn_checksum_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Sdn Checksum Specification

## Scenarios

### CRC32 Runtime

#### returns consistent hash for same input

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val crc1 = rt_crc32_text("hello")
val crc2 = rt_crc32_text("hello")
expect crc1 == crc2
```

</details>

#### returns different hash for different input

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val crc1 = rt_crc32_text("hello")
val crc2 = rt_crc32_text("world")
expect crc1 != crc2
```

</details>

#### handles empty string

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val crc = rt_crc32_text("")
expect crc == 0
```

</details>

#### matches known CRC32 test vector

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val crc = rt_crc32_text("123456789")
expect crc == 3421780262
```

</details>

### SDN Checksum Integration

#### computes and verifies checksum header

1. expect content starts with


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val body = "test data here\n"
val crc = rt_crc32_text(body)
val content = "#sdn-crc32:{crc}\n" + body
expect content.starts_with("#sdn-crc32:")
```

</details>

#### detects corruption in body

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val body = "original data\n"
val crc = rt_crc32_text(body)
val corrupted = "corrupted data\n"
val crc2 = rt_crc32_text(corrupted)
expect crc != crc2
```

</details>

#### parses checksum header correctly

1. expect header line starts with


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val body = "table_data|col1,col2|\n1\tAlice\n"
val crc = rt_crc32_text(body)
val content = "#sdn-crc32:{crc}\n" + body
val lines = content.split("\n")
val header_line = lines[0]
expect header_line.starts_with("#sdn-crc32:")
val stored_str = header_line.slice(11, header_line.len())
val stored_crc = stored_str.to_int() ?? -1
expect stored_crc == crc
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/stdlib/database/sdn_checksum_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- CRC32 Runtime
- SDN Checksum Integration

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
