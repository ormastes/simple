# String Literals Specification

> <details>

<!-- sdn-diagram:id=string_literals_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=string_literals_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

string_literals_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=string_literals_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 24 | 24 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# String Literals Specification

## Scenarios

### text Literal Syntax

#### double-quoted strings (interpolated by default)

#### creates simple string

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = "hello"
expect s == "hello"
```

</details>

#### supports escape sequences

1. expect s contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = "hello\nworld"
expect s.contains("\n") == true
```

</details>

#### supports expression interpolation

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = "Sum: {1 + 2}"
expect result == "Sum: 3"
```

</details>

#### escapes braces with double braces

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = "{{key}}"
expect json == '{key}'  # Raw string for comparison
```

</details>

#### single-quoted strings (raw)

#### creates raw string

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = 'hello'
expect s == "hello"
```

</details>

#### preserves backslashes literally

1. expect s contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = 'hello\nworld'
expect s.contains("\\n") == true
```

</details>

#### preserves braces literally

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = '{name}'
expect s == '{name}'  # Raw string preserves {name} literally
```

</details>

#### is useful for regex patterns

1. expect pattern contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pattern = '\d+\.\d+'
expect pattern.contains("\\d") == true
```

</details>

#### triple-quoted strings (docstrings)

#### creates multi-line string

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = """line1
```

</details>

#### preserves braces literally

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = """{name}"""
expect s == '{name}'  # Raw string for comparison
```

</details>

#### allows embedded double quotes

1. expect s contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = """He said "hello" """
expect s.contains("\"") == true
```

</details>

#### raw double-quoted strings (r prefix)

#### creates raw string with double quotes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = r"hello"
expect s == "hello"
```

</details>

#### preserves backslashes

1. expect s contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = r"C:\Users\name"
expect s.contains("\\") == true
```

</details>

#### preserves braces

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = r"{name}"
expect s == '{name}'  # Raw string for comparison
```

</details>

#### is useful for Windows paths

1. expect path starts with


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = r"C:\Program Files\App"
expect path.starts_with("C:") == true
```

</details>

#### raw triple-quoted strings (r prefix)

#### creates multi-line raw string

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = r"""line1
```

</details>

#### preserves backslashes in multi-line

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = r"""path\to
```

</details>

#### explicit f-string prefix (redundant but valid)

#### works same as regular double-quoted

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val name = "World"
val s = f"Hello, {name}!"
expect s == "Hello, World!"
```

</details>

#### supports expressions

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = f"Result: {2 * 3}"
expect s == "Result: 6"
```

</details>

#### triple-quoted f-strings (f prefix)

#### creates multi-line interpolated string

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val name = "World"
val s = f"""Hello, {name}!
```

</details>

#### supports expressions in multi-line

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = f"""Sum: {1 + 2}
```

</details>

#### allows embedded double quotes

1. expect s contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val name = "test"
val s = f"""He said "{name}" """
expect s.contains("\"test\"") == true
```

</details>

#### escapes braces with double braces

1. expect json contains
2. expect json contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val value = 42
val json = f"""{{"key": {value}}}"""
expect json.contains('{') == true  # Use raw string to check for literal {
expect json.contains("42") == true
```

</details>

#### string type compatibility

#### all string types are compatible

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = "hello"
val b = 'hello'
val c = """hello"""
val d = r"hello"
expect a == b
expect b == c
expect c == d
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/string_literals_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- text Literal Syntax

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 24 |
| Active scenarios | 24 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
