# Ls Specification

> <details>

<!-- sdn-diagram:id=ls_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=ls_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

ls_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=ls_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Ls Specification

## Scenarios

### ls tool

#### size formatting

#### formats bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = format_size_human(500)
expect(result).to_equal("500B")
```

</details>

#### formats kilobytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = format_size_human(2048)
expect(result).to_equal("2K")
```

</details>

#### formats megabytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = format_size_human(1048576)
expect(result).to_equal("1M")
```

</details>

#### formats gigabytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = format_size_human(1073741824)
expect(result).to_equal("1G")
```

</details>

#### size alignment

#### right-aligns size

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = format_size(42, 8)
expect(result).to_equal("      42")
```

</details>

#### type character

#### returns d for directory

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = format_type_char("/tmp")
expect(result).to_equal("d")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/01_unit/tools/ls_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- ls tool

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
