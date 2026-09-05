# Format Specification

> <details>

<!-- sdn-diagram:id=format_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=format_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

format_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=format_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 19 | 19 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Format Specification

## Scenarios

### format stdlib

### str_repeat

#### repeats string N times

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(str_repeat("ab", 3)).to_equal("ababab")
```

</details>

#### repeat 0 times gives empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(str_repeat("x", 0)).to_equal("")
```

</details>

### format_left

#### pads right with spaces

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(format_left("hi", 5)).to_equal("hi   ")
```

</details>

#### no padding if already long enough

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(format_left("hello", 3)).to_equal("hello")
```

</details>

### format_right

#### pads left with spaces

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(format_right("hi", 5)).to_equal("   hi")
```

</details>

#### no padding if already long enough

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(format_right("hello", 3)).to_equal("hello")
```

</details>

### format_zero_pad

#### pads with zeros

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(format_zero_pad("42", 5)).to_equal("00042")
```

</details>

#### no padding if long enough

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(format_zero_pad("12345", 3)).to_equal("12345")
```

</details>

### format_hex

#### formats zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(format_hex(0)).to_equal("0")
```

</details>

#### formats decimal 255

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(format_hex(255)).to_equal("ff")
```

</details>

#### formats decimal 16

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(format_hex(16)).to_equal("10")
```

</details>

### format_hex_upper

#### formats uppercase hex

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(format_hex_upper(255)).to_equal("FF")
```

</details>

### format_binary

#### formats zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(format_binary(0)).to_equal("0")
```

</details>

#### formats 8 as binary

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(format_binary(8)).to_equal("1000")
```

</details>

#### formats 255 as binary

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(format_binary(255)).to_equal("11111111")
```

</details>

### format_signed

#### positive with plus sign

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(format_signed(42)).to_equal("+42")
```

</details>

#### negative keeps minus

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(format_signed(-5)).to_equal("-5")
```

</details>

### format_align

#### left align

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(format_align("x", 3, "left")).to_equal("x  ")
```

</details>

#### right align

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(format_align("x", 3, "right")).to_equal("  x")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/format_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- format stdlib
- str_repeat
- format_left
- format_right
- format_zero_pad
- format_hex
- format_hex_upper
- format_binary
- format_signed
- format_align

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 19 |
| Active scenarios | 19 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
