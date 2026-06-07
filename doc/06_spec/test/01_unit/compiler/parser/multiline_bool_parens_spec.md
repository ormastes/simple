# Multiline Bool Parens Specification

> <details>

<!-- sdn-diagram:id=multiline_bool_parens_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=multiline_bool_parens_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

multiline_bool_parens_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=multiline_bool_parens_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Multiline Bool Parens Specification

## Scenarios

### Multi-line Boolean Expressions with Parentheses

#### suppresses newlines inside round parentheses

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = true
val b = true
val result = (a and
    b)
expect(result).to_equal(true)
```

</details>

#### suppresses newlines for complex boolean expressions

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = true
val b = true
val c = true
val d = true
val result = (a and
    b and
    c or
    d)
expect(result).to_equal(true)
```

</details>

#### square brackets do not suppress newlines

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Items in arrays work with newlines too (commas separate)
val arr = [1,
    2,
    3]
expect(arr.len()).to_equal(3)
expect(arr[0]).to_equal(1)
```

</details>

#### suppresses indentation inside round parentheses

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = true
val b = true
val result = if (a and
        b):
    "yes"
else:
    "no"
expect(result).to_equal("yes")
```

</details>

#### handles nested parentheses correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = true
val b = false
val c = true
val result = ((a and
    b) or
    c)
expect(result).to_equal(true)
```

</details>

#### handles multi-line function calls with parentheses

1. fn add3
   - Expected: result equals `6`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn add3(x: i64, y: i64, z: i64) -> i64:
    x + y + z
val result = add3(
    1,
    2,
    3)
expect(result).to_equal(6)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/parser/multiline_bool_parens_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Multi-line Boolean Expressions with Parentheses

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
