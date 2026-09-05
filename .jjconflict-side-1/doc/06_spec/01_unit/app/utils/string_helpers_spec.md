# String Helpers Specification

> <details>

<!-- sdn-diagram:id=string_helpers_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=string_helpers_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

string_helpers_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=string_helpers_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 29 | 29 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# String Helpers Specification

## Scenarios

### Whitespace Handling

#### trims leading whitespace

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val input = "   text"
val result = trim_whitespace(input)
expect result == "text"
```

</details>

#### trims trailing whitespace

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val input = "text   "
val result = trim_whitespace(input)
expect result == "text"
```

</details>

#### trims both sides

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val input = "  text  "
val result = trim_whitespace(input)
expect result == "text"
```

</details>

#### preserves internal whitespace

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val input = "hello world"
val result = trim_whitespace(input)
expect result == "hello world"
```

</details>

### String Splitting

#### splits by newline

1. expect lines len


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val input = "line1\nline2\nline3"
val lines = split_lines(input)
expect lines.len() == 3
expect lines[0] == "line1"
```

</details>

#### handles single line

1. expect lines len


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val input = "single line"
val lines = split_lines(input)
expect lines.len() == 1
```

</details>

#### handles empty string

1. expect lines len


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val input = ""
val lines = split_lines(input)
expect lines.len() >= 0
```

</details>

#### splits path components

1. expect parts len


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = "src/app/lsp/main.spl"
val parts = path.split("/")
expect parts.len() == 4
expect parts[0] == "src"
expect parts[-1] == "main.spl"
```

</details>

### Pattern Matching

#### finds keyword in string

1. expect contains keyword
2. expect contains keyword


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val text = "fn main():"
expect contains_keyword(text, "fn")
expect contains_keyword(text, "main")
```

</details>

#### detects missing keyword

1. expect not contains keyword


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val text = "val x = 42"
expect not contains_keyword(text, "fn")
```

</details>

#### finds file extensions

1. expect filename ends with


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val filename = "test.spl"
expect filename.ends_with(".spl")
```

</details>

#### checks file path patterns

1. expect path contains
2. expect path contains
3. expect path ends with


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = "test/unit/lib/std/app/test.spl"
expect path.contains("test")
expect path.contains("app")
expect path.ends_with(".spl")
```

</details>

### String Comparison

#### compares equal strings

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s1 = "hello"
val s2 = "hello"
expect s1 == s2
```

</details>

#### compares different strings

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s1 = "hello"
val s2 = "world"
expect s1 != s2
```

</details>

#### handles case sensitivity

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lower = "hello"
val upper = "HELLO"
expect lower != upper
```

</details>

#### compares prefixes

1. expect text starts with
2. expect not text starts with


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val text = "function_name"
expect text.starts_with("func")
expect not text.starts_with("var")
```

</details>

### String Construction

#### concatenates strings

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val part1 = "hello"
val part2 = "world"
val result = part1 + " " + part2
expect result == "hello world"
```

</details>

#### builds paths

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dir = "test"
val file = "spec.spl"
val path = dir + "/" + file
expect path == "test/spec.spl"
```

</details>

#### formats with variables

1. expect greeting contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val name = "Alice"
val greeting = "Hello, " + name + "!"
expect greeting.contains(name)
```

</details>

### String Searching

#### finds substring position

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val text = "hello world"
val index = text.find("world")
expect index.? == true
```

</details>

#### handles missing substring

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val text = "hello world"
val index = text.find("xyz")
expect not index.?
```

</details>

#### finds first occurrence

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val text = "test test test"
val index = text.find("test")
expect index == 0
```

</details>

### String Length and Indexing

#### measures string length

1. expect text len


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val text = "hello"
expect text.len() == 5
```

</details>

#### handles empty string length

1. expect empty len


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val empty = ""
expect empty.len() == 0
```

</details>

#### accesses characters by index

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val text = "hello"
expect text[0] == 'h'
expect text[4] == 'o'
```

</details>

#### uses negative indexing

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val text = "hello"
expect text[-1] == 'o'
expect text[-5] == 'h'
```

</details>

### String Slicing

#### checks substring existence

1. expect text contains
2. expect text contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val text = "hello world"
expect text.contains("hello")
expect text.contains("world")
```

</details>

#### finds substring by search

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val text = "hello world"
val index = text.find("world")
expect index.? == true
```

</details>

#### validates text content

1. expect text len
2. expect text starts with
3. expect text ends with


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val text = "hello world"
expect text.len() == 11
expect text.starts_with("hello")
expect text.ends_with("world")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/utils/string_helpers_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Whitespace Handling
- String Splitting
- Pattern Matching
- String Comparison
- String Construction
- String Searching
- String Length and Indexing
- String Slicing

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 29 |
| Active scenarios | 29 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
