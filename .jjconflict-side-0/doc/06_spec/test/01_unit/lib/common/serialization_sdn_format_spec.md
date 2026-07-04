# Serialization SDN Format Coverage Specification

> Branch-coverage tests for SDN format functions, format detection, and pretty printing:

<!-- sdn-diagram:id=serialization_sdn_format_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=serialization_sdn_format_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

serialization_sdn_format_spec -> serialization
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=serialization_sdn_format_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 49 | 49 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Serialization SDN Format Coverage Specification

Branch-coverage tests for SDN format functions, format detection, and pretty printing:

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #SERIAL-COV-SDN |
| Category | Stdlib |
| Difficulty | 2/5 |
| Status | Implemented |
| Source | `test/01_unit/lib/common/serialization_sdn_format_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Branch-coverage tests for SDN format functions, format detection, and pretty printing:
- to_sdn_* functions (formats.spl)
- detect_format, is_numeric_text, is_valid_sdn (formats.spl)
- pretty_print_indent, pretty_list, pretty_tuple, pretty_dict (utilities.spl)

## Scenarios

### to_sdn_int

#### converts positive integer

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(to_sdn_int(42)).to_equal("42")
```

</details>

#### converts zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(to_sdn_int(0)).to_equal("0")
```

</details>

#### converts negative integer

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(to_sdn_int(-5)).to_equal("-5")
```

</details>

### to_sdn_bool

#### converts true

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(to_sdn_bool(true)).to_equal("true")
```

</details>

#### converts false

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(to_sdn_bool(false)).to_equal("false")
```

</details>

### to_sdn_nil

#### converts nil value

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(to_sdn_nil()).to_equal("nil")
```

</details>

### to_sdn_text

#### quotes text

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = to_sdn_text("hello")
expect(result).to_equal("\"hello\"")
```

</details>

### to_sdn_list

#### converts empty list

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(to_sdn_list([])).to_equal("[]")
```

</details>

#### converts non-empty list

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(to_sdn_list(["1", "2"])).to_equal("[1, 2]")
```

</details>

### to_sdn_tuple

#### converts empty tuple

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(to_sdn_tuple([])).to_equal("()")
```

</details>

#### converts non-empty tuple

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(to_sdn_tuple(["a", "b"])).to_equal("(a, b)")
```

</details>

### to_sdn_dict

#### converts empty dict

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(to_sdn_dict([])).to_equal("{}")
```

</details>

#### converts non-empty dict

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(to_sdn_dict([("k", "v")])).to_equal("{k: v}")
```

</details>

### is_numeric_text

#### returns false for empty string

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_numeric_text("")).to_equal(false)
```

</details>

#### returns false for minus sign only

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_numeric_text("-")).to_equal(false)
```

</details>

#### returns true for single digit

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_numeric_text("5")).to_equal(true)
```

</details>

#### returns true for multi-digit number

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_numeric_text("12345")).to_equal(true)
```

</details>

#### returns true for negative number

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_numeric_text("-42")).to_equal(true)
```

</details>

#### returns false for alphabetic text

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_numeric_text("abc")).to_equal(false)
```

</details>

#### returns false for mixed text

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_numeric_text("12a")).to_equal(false)
```

</details>

#### returns true for zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_numeric_text("0")).to_equal(true)
```

</details>

### detect_format

#### returns unknown for empty string

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(detect_format("")).to_equal("unknown")
```

</details>

#### detects tagged format

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(detect_format("@MyType\{payload\}")).to_equal("tagged")
```

</details>

#### detects sdn for dict starting with brace

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(detect_format("{key: val}")).to_equal("sdn")
```

</details>

#### detects sdn for list starting with bracket

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(detect_format("[1, 2, 3]")).to_equal("sdn")
```

</details>

#### detects sdn for quoted string

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(detect_format("\"hello\"")).to_equal("sdn")
```

</details>

#### detects sdn for true

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(detect_format("true")).to_equal("sdn")
```

</details>

#### detects sdn for false

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(detect_format("false")).to_equal("sdn")
```

</details>

#### detects sdn for nil

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(detect_format("nil")).to_equal("sdn")
```

</details>

#### detects sdn for numeric string

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(detect_format("42")).to_equal("sdn")
```

</details>

#### returns unknown for unrecognized format

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(detect_format("random_text")).to_equal("unknown")
```

</details>

### is_valid_sdn

#### returns true for valid sdn list

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_valid_sdn("[1, 2]")).to_equal(true)
```

</details>

#### returns true for tagged format

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_valid_sdn("@Type\{payload\}")).to_equal(true)
```

</details>

#### returns true for sdn boolean

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_valid_sdn("true")).to_equal(true)
```

</details>

#### returns false for invalid input

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_valid_sdn("")).to_equal(false)
```

</details>

#### returns false for unknown format

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_valid_sdn("random_text")).to_equal(false)
```

</details>

### pretty_print_indent

#### adds no indent at level 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = pretty_print_indent("hello", 0)
expect(result).to_equal("hello")
```

</details>

#### adds two spaces per indent level

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = pretty_print_indent("hello", 2)
expect(result).to_start_with("    ")
expect(result).to_end_with("hello")
```

</details>

#### adds single level indent

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = pretty_print_indent("x", 1)
expect(result).to_equal("  x")
```

</details>

### pretty_list

#### returns bracket pair for empty list

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = pretty_list([], 0)
expect(result).to_equal("[]")
```

</details>

#### formats single item list

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = pretty_list(["a"], 0)
expect(result).to_start_with("[\n")
expect(result).to_contain("a")
```

</details>

#### formats multi-item list with commas

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = pretty_list(["a", "b"], 0)
expect(result).to_contain(",")
```

</details>

#### does not add comma after last item

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = pretty_list(["a"], 0)
expect(result).to_contain("a\n")
```

</details>

### pretty_tuple

#### returns parens for empty tuple

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = pretty_tuple([], 0)
expect(result).to_equal("()")
```

</details>

#### formats single value tuple

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = pretty_tuple(["x"], 0)
expect(result).to_start_with("(\n")
expect(result).to_contain("x")
```

</details>

#### formats multi-value tuple with commas

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = pretty_tuple(["x", "y"], 0)
expect(result).to_contain(",")
```

</details>

### pretty_dict

#### returns braces for empty dict

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = pretty_dict([], 0)
expect(result).to_equal("{}")
```

</details>

#### formats single entry dict

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = pretty_dict([("k", "v")], 0)
expect(result).to_start_with("{\n")
expect(result).to_contain("k: v")
```

</details>

#### formats multi-entry dict with commas

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = pretty_dict([("a", "1"), ("b", "2")], 0)
expect(result).to_contain(",")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 49 |
| Active scenarios | 49 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
