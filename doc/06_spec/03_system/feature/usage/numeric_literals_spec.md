# Numeric Literals Specification

> Tests for various numeric literal formats including hexadecimal, binary, octal, and numeric separators with underscores.

<!-- sdn-diagram:id=numeric_literals_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=numeric_literals_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

numeric_literals_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=numeric_literals_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 16 | 16 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Numeric Literals Specification

Tests for various numeric literal formats including hexadecimal, binary, octal, and numeric separators with underscores.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #NUM-001 |
| Category | Language \| Literals |
| Status | Implemented |
| Source | `test/03_system/feature/usage/numeric_literals_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests for various numeric literal formats including hexadecimal, binary,
octal, and numeric separators with underscores.

## Syntax

```simple
val hex = 0xFF         # Hexadecimal (255)
val bin = 0b1010       # Binary (10)
val oct = 0o755        # Octal (493)
val sep = 1_000_000    # Underscores for readability
```

## Scenarios

### Hexadecimal Literals

#### parses basic hex literal

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 0xFF
expect x == 255
```

</details>

#### parses lowercase hex

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 0xff
expect x == 255
```

</details>

#### parses mixed case hex

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 0xAb
expect x == 171
```

</details>

#### performs hex arithmetic

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 0x10 + 0x20
expect x == 48  # 16 + 32
```

</details>

#### compares hex and decimal

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect 0x10 == 16
expect 0x100 == 256
```

</details>

### Binary Literals

#### parses basic binary literal

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 0b1010
expect x == 10
```

</details>

#### parses binary with underscores

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 0b1111_0000
expect x == 240
```

</details>

#### performs binary arithmetic

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 0b1000 + 0b0100
expect x == 12  # 8 + 4
```

</details>

#### uses binary for bit patterns

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val flags = 0b0101
expect flags == 5
```

</details>

### Octal Literals

#### parses basic octal literal

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 0o755
expect x == 493  # 7*64 + 5*8 + 5
```

</details>

#### parses small octal

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 0o10
expect x == 8
```

</details>

#### performs octal arithmetic

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 0o10 + 0o10
expect x == 16  # 8 + 8
```

</details>

### Numeric Separators

#### parses decimal with separators

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 1_000_000
expect x == 1000000
```

</details>

#### parses hex with separators

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 0xFF_FF
expect x == 65535
```

</details>

#### parses binary with separators

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 0b1010_1010
expect x == 170
```

</details>

#### allows multiple underscores

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 100__000
expect x == 100000
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 16 |
| Active scenarios | 16 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
