# Sdn Specification

> 1. expect sdn contains

<!-- sdn-diagram:id=sdn_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=sdn_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

sdn_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=sdn_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 22 | 22 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Sdn Specification

## Scenarios

### SDN - basic parsing

#### parses key-value pairs

1. expect sdn contains
2. expect sdn contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sdn = "name: John\nage: 30"
# Would parse to: {"name": "John", "age": 30}
expect sdn.contains("name:")
expect sdn.contains("age:")
```

</details>

#### parses nested structures

1. expect sdn contains
2. expect sdn contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sdn = "person:\n  name: Alice\n  age: 25"
expect sdn.contains("person:")
expect sdn.contains("  name:")
```

</details>

#### parses lists

1. expect sdn contains
2. expect sdn contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sdn = "items:\n  - apple\n  - banana\n  - orange"
expect sdn.contains("items:")
expect sdn.contains("  - apple")
```

</details>

### SDN - data types

#### parses strings

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val value = "hello"
expect value == "hello"
```

</details>

#### parses integers

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val value = 42
expect value == 42
```

</details>

#### parses floats

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val value = 3.14
expect value > 3.0
```

</details>

#### parses booleans

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val true_val = true
val false_val = false
expect true_val
expect not false_val
```

</details>

### SDN - table format

#### parses table headers

1. expect header contains
2. expect header contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val header = "users |id, name, age|"
expect header.contains("|id,")
expect header.contains("name,")
```

</details>

#### parses table rows

1. expect row contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val row = "    1, Alice, 30"
expect row.contains("Alice")
```

</details>

#### parses multiple rows

1. expect rows len


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rows = [
    "    1, Alice, 30",
    "    2, Bob, 25",
    "    3, Carol, 35"
]

expect rows.len() == 3
```

</details>

### SDN - serialization

#### serializes simple values

1. expect data has


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data = {"name": "John", "age": 30}
# Should produce: name: John\nage: 30
expect data.has("name")
```

</details>

#### serializes nested objects

1. expect data has


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data = {
    "person": {
        "name": "Alice",
        "details": {"age": 25, "city": "NYC"}
    }
}

expect data.has("person")
```

</details>

#### serializes arrays

1. expect data has
2. expect data["items"] len


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data = {"items": ["apple", "banana", "orange"]}
expect data.has("items")
expect data["items"].len() == 3
```

</details>

### SDN - round-trip

#### preserves data through parse and serialize

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val original = {"name": "Test", "value": 42}
# parse(serialize(data)) == data
expect original["name"] == "Test"
expect original["value"] == 42
```

</details>

#### preserves table data

1. expect table sdn contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val table_sdn = "users |id, name|\n    1, Alice\n    2, Bob"
# Parse and serialize should preserve structure
expect table_sdn.contains("|id, name|")
```

</details>

### SDN - error handling

#### handles malformed input gracefully

1. expect bad sdn len


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bad_sdn = "invalid: [\n  incomplete"
# Should return parse error, not crash
expect bad_sdn.len() > 0
```

</details>

#### reports line numbers in errors

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Error on line 3
val error_info = {"line": 3, "message": "Unexpected token"}
expect error_info["line"] == 3
```

</details>

### SDN - comments

#### supports hash comments

1. expect sdn contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sdn = "# This is a comment\nname: John"
expect sdn.contains("#")
```

</details>

#### ignores comments in parsing

1. expect sdn with comment contains
2. expect sdn without contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sdn_with_comment = "# comment\nvalue: 42"
val sdn_without = "value: 42"
# Both should parse to same data
expect sdn_with_comment.contains("value:")
expect sdn_without.contains("value:")
```

</details>

### SDN - special characters

#### handles quotes in strings

1. expect value contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val value = "He said \"hello\""
expect value.contains("\"")
```

</details>

#### handles newlines in strings

1. expect value contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val value = "Line 1\nLine 2"
expect value.contains("\n")
```

</details>

#### handles Unicode characters

1. expect value len


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val value = "Hello 世界 🌍"
expect value.len() > 5
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/sdn_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- SDN - basic parsing
- SDN - data types
- SDN - table format
- SDN - serialization
- SDN - round-trip
- SDN - error handling
- SDN - comments
- SDN - special characters

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 22 |
| Active scenarios | 22 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
