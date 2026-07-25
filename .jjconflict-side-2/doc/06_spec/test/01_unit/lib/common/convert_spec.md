# Convert Specification

> <details>

<!-- sdn-diagram:id=convert_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=convert_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

convert_spec -> std
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
| 22 | 22 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Convert Specification

## Scenarios

### std.convert

### digit_value

#### returns value for digits 0-9

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(digit_value("0")).to_equal(0)
expect(digit_value("5")).to_equal(5)
expect(digit_value("9")).to_equal(9)
```

</details>

#### returns -1 for non-digits

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(digit_value("a")).to_equal(-1)
expect(digit_value(" ")).to_equal(-1)
expect(digit_value("")).to_equal(-1)
```

</details>

### safe_parse_int

#### parses positive integers

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(safe_parse_int("42")).to_equal(42)
expect(safe_parse_int("0")).to_equal(0)
expect(safe_parse_int("12345")).to_equal(12345)
```

</details>

#### parses negative integers

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(safe_parse_int("-1")).to_equal(-1)
expect(safe_parse_int("-999")).to_equal(-999)
```

</details>

#### returns 0 for invalid input

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(safe_parse_int("")).to_equal(0)
expect(safe_parse_int("abc")).to_equal(0)
expect(safe_parse_int("-")).to_equal(0)
```

</details>

#### handles whitespace

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(safe_parse_int("  42  ")).to_equal(42)
```

</details>

### parse_u16

#### parses valid u16 values

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(parse_u16("0")).to_equal(0)
expect(parse_u16("65535")).to_equal(65535)
expect(parse_u16("1000")).to_equal(1000)
```

</details>

#### returns 0 for out of range

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(parse_u16("65536")).to_equal(0)
expect(parse_u16("-1")).to_equal(0)
```

</details>

### parse_u32

#### parses valid u32 values

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(parse_u32("0")).to_equal(0)
expect(parse_u32("1000000")).to_equal(1000000)
```

</details>

#### returns 0 for negative

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(parse_u32("-1")).to_equal(0)
```

</details>

### parse_u64

#### parses valid positive values

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(parse_u64("0")).to_equal(0)
expect(parse_u64("999999999")).to_equal(999999999)
```

</details>

#### returns 0 for negative

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(parse_u64("-5")).to_equal(0)
```

</details>

### i64_to_usize

#### passes through positive values

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(i64_to_usize(42)).to_equal(42)
expect(i64_to_usize(0)).to_equal(0)
```

</details>

#### clamps negatives to 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(i64_to_usize(-1)).to_equal(0)
expect(i64_to_usize(-999)).to_equal(0)
```

</details>

### usize_to_i64

#### is identity operation

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(usize_to_i64(42)).to_equal(42)
expect(usize_to_i64(0)).to_equal(0)
```

</details>

### to_bool

#### recognizes truthy strings

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(to_bool("true")).to_equal(true)
expect(to_bool("1")).to_equal(true)
expect(to_bool("yes")).to_equal(true)
expect(to_bool("on")).to_equal(true)
```

</details>

#### is case-insensitive

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(to_bool("TRUE")).to_equal(true)
expect(to_bool("Yes")).to_equal(true)
```

</details>

#### returns false for other strings

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(to_bool("false")).to_equal(false)
expect(to_bool("no")).to_equal(false)
expect(to_bool("")).to_equal(false)
expect(to_bool("random")).to_equal(false)
```

</details>

### bool_to_text

#### converts true to text

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(bool_to_text(true)).to_equal("true")
```

</details>

#### converts false to text

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(bool_to_text(false)).to_equal("false")
```

</details>

### i64_to_text

#### converts integers to text

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(i64_to_text(42)).to_equal("42")
expect(i64_to_text(0)).to_equal("0")
expect(i64_to_text(-1)).to_equal("-1")
```

</details>

### f64_to_text

#### converts floats to text

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = f64_to_text(3.14)
expect(result).to_contain("3.14")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/convert_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- std.convert
- digit_value
- safe_parse_int
- parse_u16
- parse_u32
- parse_u64
- i64_to_usize
- usize_to_i64
- to_bool
- bool_to_text
- i64_to_text
- f64_to_text

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 22 |
| Active scenarios | 22 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
