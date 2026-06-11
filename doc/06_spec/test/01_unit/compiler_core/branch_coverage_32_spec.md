# Branch Coverage Test Suite - Complex String Operations

> Tests complex string interpolation, nested braces, and multi-part string operations to cover translate_expr branches (lines 678, 720, 757-765).

<!-- sdn-diagram:id=branch_coverage_32_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=branch_coverage_32_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

branch_coverage_32_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=branch_coverage_32_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 19 | 19 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Branch Coverage Test Suite - Complex String Operations

Tests complex string interpolation, nested braces, and multi-part string operations to cover translate_expr branches (lines 678, 720, 757-765).

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #BRANCH #STRING_COMPLEX #INTERPOLATION |
| Category | Testing |
| Status | Implemented |
| Source | `test/01_unit/compiler_core/branch_coverage_32_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests complex string interpolation, nested braces, and multi-part
string operations to cover translate_expr branches (lines 678, 720, 757-765).

## Scenarios

### Complex String Interpolation

#### multiple interpolations

1. check
2. check
3. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 5
val y = 10
val z = 15
val s = "{x} + {y} + {z}"
check(s.contains("5"))
check(s.contains("10"))
check(s.contains("15"))
```

</details>

#### interpolation with expressions

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = 3
val b = 4
val result = "{a * b}"
check(result.contains("12"))
```

</details>

#### nested expression interpolation

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 2
val y = 3
val complex = "{x * (y + 1)}"
check(complex.contains("8"))
```

</details>

#### interpolation with method calls

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = "hello"
val msg = "Length is {s.len()}"
check(msg.contains("5"))
```

</details>

### String Concatenation Chains

#### multiple concat

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s1 = "a" + "b" + "c"
check(s1 == "abc")
```

</details>

#### long concat chain

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s2 = "a" + "b" + "c" + "d" + "e"
check(s2 == "abcde")
```

</details>

#### concat with variables

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = "hello"
val y = "world"
val z = x + " " + y
check(z == "hello world")
```

</details>

#### concat in expression

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = "test"
val b = ("x" + "y") + ("z")
check(b == "xyz")
```

</details>

### String Method Chains

#### trim and operations

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = "  hello  "
val clean = s.trim()
check(clean == "hello")
```

</details>

#### multiple replacements

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val text = "abc"
val r1 = text.replace("a", "x")
val r2 = r1.replace("b", "y")
check(r2 == "xyc")
```

</details>

#### slice operations

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = "abcdefgh"
val sub = s[2..5]
check(sub.len() == 3)
```

</details>

### String Edge Cases

#### empty interpolation

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = "{0}"
check(s.contains("0"))
```

</details>

#### consecutive interpolations

1. check
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 1
val y = 2
val s = "{x}{y}"
check(s.contains("1"))
check(s.contains("2"))
```

</details>

#### interpolation at start

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 5
val s = "{x} is the value"
check(s.starts_with("5"))
```

</details>

#### interpolation at end

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 5
val s = "Value is {x}"
check(s.ends_with("5"))
```

</details>

### Special String Cases

#### multiline string

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = """line1
```

</details>

#### raw string

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = r"no {interpolation}"
check(r.contains("{"))
```

</details>

#### escaped characters

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val e = "line1\nline2"
check(e.contains("\n"))
```

</details>

#### string with quotes

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val q = "He said \"hello\""
check(q.contains("\""))
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 19 |
| Active scenarios | 19 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
