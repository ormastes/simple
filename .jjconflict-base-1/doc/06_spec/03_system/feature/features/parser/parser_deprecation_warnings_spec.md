# Parser Deprecation Warnings Specification

> use std.parser.{Parser, ErrorHint, ErrorHintLevel}

<!-- sdn-diagram:id=parser_deprecation_warnings_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=parser_deprecation_warnings_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

parser_deprecation_warnings_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=parser_deprecation_warnings_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 31 | 31 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Parser Deprecation Warnings Specification

use std.parser.{Parser, ErrorHint, ErrorHintLevel}

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #PARSER-DEPREC-001 to #PARSER-DEPREC-031 |
| Category | Infrastructure \| Parser |
| Status | Implemented |
| Source | `test/03_system/feature/features/parser/parser_deprecation_warnings_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Key Deprecations

- Generic syntax: `[]` deprecated in favor of `<>`
- Affects: functions, structs, classes, enums, traits, impl blocks
- Array types `[i32]` and literals `[1,2,3]` should NOT warn

## API

```simple
use std.parser.{Parser, ErrorHint, ErrorHintLevel}

var parser = Parser.new(source)
parser.parse()
val hints = parser.error_hints()
```

## Scenarios

### Function Generic Deprecation Warnings

#### warns about deprecated [] syntax in function generics

1. var parser = Parser new
2. parser parse


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var parser = Parser.new("fn test[T](x: T) -> T:\n    x")
parser.parse()
val hints = parser.error_hints()
val has_warning = hints.any(_1.level == ErrorHintLevel::Warning and h.message.contains("Deprecated"))
expect has_warning
```

</details>

#### warns about deprecated [] syntax with multiple params

1. var parser = Parser new
2. parser parse


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var parser = Parser.new("fn map[T, U](f: fn(T) -> U) -> U:\n    pass")
parser.parse()
val hints = parser.error_hints()
val has_warning = hints.any(_1.level == ErrorHintLevel::Warning and h.message.contains("Deprecated"))
expect has_warning
```

</details>

#### does NOT warn about <> syntax in function generics

1. var parser = Parser new
2. parser parse


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var parser = Parser.new("fn test<T>(x: T) -> T:\n    x")
parser.parse()
val hints = parser.error_hints()
val has_deprecation = hints.any(_1.message.contains("Deprecated") and h.message.contains("generic"))
expect not has_deprecation
```

</details>

### Struct Generic Deprecation Warnings

#### warns about deprecated [] syntax in struct

1. var parser = Parser new
2. parser parse


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var parser = Parser.new("struct Container[T]:\n    value: T")
parser.parse()
val hints = parser.error_hints()
val has_warning = hints.any(_1.level == ErrorHintLevel::Warning and h.message.contains("Deprecated"))
expect has_warning
```

</details>

#### does NOT warn about <> syntax in struct

1. var parser = Parser new
2. parser parse


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var parser = Parser.new("struct Container<T>:\n    value: T")
parser.parse()
val hints = parser.error_hints()
val has_deprecation = hints.any(_1.message.contains("Deprecated") and h.message.contains("generic"))
expect not has_deprecation
```

</details>

### Type Annotation Deprecation Warnings

#### warns about deprecated [] syntax in Option type

1. var parser = Parser new
2. parser parse


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var parser = Parser.new("val x: Option[Int] = None")
parser.parse()
val hints = parser.error_hints()
val has_warning = hints.any(_1.level == ErrorHintLevel::Warning and h.message.contains("Deprecated"))
expect has_warning
```

</details>

#### warns about deprecated [] syntax in Result type

1. var parser = Parser new
2. parser parse


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var parser = Parser.new("val x: Result[Int, String] = Ok(42)")
parser.parse()
val hints = parser.error_hints()
val has_warning = hints.any(_1.level == ErrorHintLevel::Warning and h.message.contains("Deprecated"))
expect has_warning
```

</details>

#### warns about deprecated [] syntax in List type

1. var parser = Parser new
2. parser parse


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var parser = Parser.new("val nums: List[Int] = []")
parser.parse()
val hints = parser.error_hints()
val has_warning = hints.any(_1.level == ErrorHintLevel::Warning and h.message.contains("Deprecated"))
expect has_warning
```

</details>

#### does NOT warn about <> syntax in type annotation

1. var parser = Parser new
2. parser parse


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var parser = Parser.new("val x: Option<Int> = None")
parser.parse()
val hints = parser.error_hints()
val has_deprecation = hints.any(_1.message.contains("Deprecated") and h.message.contains("generic"))
expect not has_deprecation
```

</details>

### Nested Generic Deprecation Warnings

#### warns about both nested [] usages

1. var parser = Parser new
2. parser parse


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var parser = Parser.new("val x: List[Option[String]] = []")
parser.parse()
val hints = parser.error_hints()
val warning_count = hints.filter(_1.level == ErrorHintLevel::Warning and h.message.contains("Deprecated")).len()
expect warning_count >= 2
```

</details>

#### does NOT warn about nested <> syntax

1. var parser = Parser new
2. parser parse


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var parser = Parser.new("val x: List<Option<String>> = []")
parser.parse()
val hints = parser.error_hints()
val has_deprecation = hints.any(_1.message.contains("Deprecated") and h.message.contains("generic"))
expect not has_deprecation
```

</details>

### Array Type No Deprecation Warnings

#### does NOT warn about array type [i32]

1. var parser = Parser new
2. parser parse


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var parser = Parser.new("val arr: [i32] = [1, 2, 3]")
parser.parse()
val hints = parser.error_hints()
val has_deprecation = hints.any(_1.message.contains("Deprecated") and h.message.contains("generic"))
expect not has_deprecation
```

</details>

#### does NOT warn about fixed-size array [i32; 10]

1. var parser = Parser new
2. parser parse


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var parser = Parser.new("val arr: [i32; 10] = []")
parser.parse()
val hints = parser.error_hints()
val has_deprecation = hints.any(_1.message.contains("Deprecated") and h.message.contains("generic"))
expect not has_deprecation
```

</details>

### Array Literal No Deprecation Warnings

#### does NOT warn about array literal

1. var parser = Parser new
2. parser parse


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var parser = Parser.new("val arr = [1, 2, 3, 4, 5]")
parser.parse()
val hints = parser.error_hints()
val has_deprecation = hints.any(_1.message.contains("Deprecated") and h.message.contains("generic"))
expect not has_deprecation
```

</details>

#### does NOT warn about empty array literal

1. var parser = Parser new
2. parser parse


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var parser = Parser.new("val arr = []")
parser.parse()
val hints = parser.error_hints()
val has_deprecation = hints.any(_1.message.contains("Deprecated") and h.message.contains("generic"))
expect not has_deprecation
```

</details>

### String and Comment No Deprecation Warnings

#### does NOT warn about [] in string literal

1. var parser = Parser new
2. parser parse


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var parser = Parser.new("val s = \"This is List[T] in a string\"")
parser.parse()
val hints = parser.error_hints()
val has_deprecation = hints.any(_1.message.contains("Deprecated") and h.message.contains("generic"))
expect not has_deprecation
```

</details>

#### does NOT warn about [] in comment

1. var parser = Parser new
2. parser parse


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var parser = Parser.new("# This is Option[T] in a comment\nval x = 42")
parser.parse()
val hints = parser.error_hints()
val has_deprecation = hints.any(_1.message.contains("Deprecated") and h.message.contains("generic"))
expect not has_deprecation
```

</details>

### Multiple Deprecation Warnings

#### warns about multiple deprecations in same file

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = """
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 31 |
| Active scenarios | 31 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
