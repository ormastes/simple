# String Interpolation Specification

> String interpolation allows embedding expressions directly in string literals using curly braces. Simple treats interpolation as the default for regular strings, with raw strings available when needed.

<!-- sdn-diagram:id=string_interpolation_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=string_interpolation_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

string_interpolation_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=string_interpolation_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 14 | 14 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# String Interpolation Specification

String interpolation allows embedding expressions directly in string literals using curly braces. Simple treats interpolation as the default for regular strings, with raw strings available when needed.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #INTERP-001 to #INTERP-020 |
| Category | Language \| Syntax |
| Status | Implemented |
| Source | `test/03_system/feature/usage/string_interpolation_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

String interpolation allows embedding expressions directly in string literals
using curly braces. Simple treats interpolation as the default for regular
strings, with raw strings available when needed.

## Syntax

```simple
# Default interpolation (no special prefix needed)
val name = "Alice"
print "Hello, {name}!"          # Output: Hello, Alice!

# Expressions in braces
print "Result: {2 + 3}"         # Output: Result: 5

# Raw strings (no interpolation)
val regex = r"pattern: \d+"     # Backslashes not escaped, no interpolation
```

## Key Concepts

| Concept | Syntax | Escaping | Interpolation |
|---------|--------|----------|---------------|
| Default String | `"..."` | Standard | Yes |
| Raw String | `r"..."` | None | No |
| Expression | `{expr}` | Within braces | Yes |
| Escape Sequence | `\n, \t, \\` | Standard | Processed |

## Behavior

- Expressions in braces are evaluated at runtime
- Any expression can appear in braces, not just variables
- Raw strings skip interpolation and escape processing

## Scenarios

### Basic String Interpolation

#### interpolates variable in string

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val name = "Alice"
val result = "Hello, {name}!"
var r = 0
if result == "Hello, Alice!":
    r = 1
expect r == 1
```

</details>

#### interpolates multiple variables

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val first = "John"
val last = "Doe"
val result = "{first} {last}"
var r = 0
if result == "John Doe":
    r = 1
expect r == 1
```

</details>

#### interpolates at start of string

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val value = 42
val result = "{value} is the answer"
var r = 0
if result == "42 is the answer":
    r = 1
expect r == 1
```

</details>

#### interpolates at end of string

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val value = 42
val result = "The answer is {value}"
var r = 0
if result == "The answer is 42":
    r = 1
expect r == 1
```

</details>

### Expression Interpolation

#### interpolates arithmetic expression

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = 10
val b = 20
val result = "Sum: {a + b}"
var r = 0
if result == "Sum: 30":
    r = 1
expect r == 1
```

</details>

#### interpolates multiplication expression

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 5
val y = 3
val result = "Product: {x * y}"
var r = 0
if result == "Product: 15":
    r = 1
expect r == 1
```

</details>

#### interpolates boolean value

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val b = true
val result = "flag: {b}"
var r = 0
if result == "flag: true":
    r = 1
expect r == 1
```

</details>

#### interpolates false boolean value

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val b = false
val result = "flag: {b}"
var r = 0
if result == "flag: false":
    r = 1
expect r == 1
```

</details>

### Raw Strings

#### raw string preserves braces

1. expect template len


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val template = r"{name}"
expect template.len() == 6
```

</details>

#### raw string preserves backslashes

1. expect path len


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = r"C:\Users\test"
expect path.len() == 13
```

</details>

### F-String Syntax

#### f-string basic interpolation

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 42
val s = f"value is {x}"
var r = 0
if s == "value is 42":
    r = 1
expect r == 1
```

</details>

#### f-string with expression

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = 10
val b = 20
val s = f"sum is {a + b}"
var r = 0
if s == "sum is 30":
    r = 1
expect r == 1
```

</details>

#### f-string multiple interpolations

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val name = "world"
val count = 3
val s = f"hello {name}, count={count}"
var r = 0
if s == "hello world, count=3":
    r = 1
expect r == 1
```

</details>

#### f-string no interpolation

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = f"just a string"
var r = 0
if s == "just a string":
    r = 1
expect r == 1
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 14 |
| Active scenarios | 14 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
