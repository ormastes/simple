# Nvfs Pure Simple Specification

> <details>

<!-- sdn-diagram:id=nvfs_pure_simple_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=nvfs_pure_simple_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

nvfs_pure_simple_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=nvfs_pure_simple_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Nvfs Pure Simple Specification

## Scenarios

### nvfs_pure_simple

### alloc_zeroed_bytes

#### AC-3: alloc_zeroed_bytes(64) returns array of length 64

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val buf = alloc_zeroed_bytes(64)
expect buf.len == 64
```

</details>

#### AC-3: alloc_zeroed_bytes(64) first element is zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val buf = alloc_zeroed_bytes(64)
expect buf[0] == 0
```

</details>

#### AC-3: alloc_zeroed_bytes(64) last element is zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val buf = alloc_zeroed_bytes(64)
expect buf[63] == 0
```

</details>

#### AC-3: alloc_zeroed_bytes(0) returns empty array

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val buf = alloc_zeroed_bytes(0)
expect buf.len == 0
```

</details>

#### AC-3: alloc_zeroed_bytes(1) returns single-element zero array

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val buf = alloc_zeroed_bytes(1)
expect buf.len == 1
```

</details>

#### AC-3: alloc_zeroed_bytes(1) single element is zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val buf = alloc_zeroed_bytes(1)
expect buf[0] == 0
```

</details>

### text_to_bytes_pure

#### AC-3: text_to_bytes_pure(\

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes = text_to_bytes_pure("ABC")
expect bytes.len == 3
```

</details>

#### AC-3: text_to_bytes_pure(\

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes = text_to_bytes_pure("ABC")
expect bytes[0] == 65
```

</details>

#### AC-3: text_to_bytes_pure(\

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes = text_to_bytes_pure("ABC")
expect bytes[1] == 66
```

</details>

#### AC-3: text_to_bytes_pure(\

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes = text_to_bytes_pure("ABC")
expect bytes[2] == 67
```

</details>

#### AC-3: text_to_bytes_pure(\

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes = text_to_bytes_pure("")
expect bytes.len == 0
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/fs_driver/nvfs_pure_simple_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- nvfs_pure_simple
- alloc_zeroed_bytes
- text_to_bytes_pure

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
