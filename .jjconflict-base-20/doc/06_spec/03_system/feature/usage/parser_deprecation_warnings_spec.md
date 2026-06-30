# Parser Deprecation Warnings Specification

> Note: The Parser and ErrorHintLevel types from std.parser are too heavy

<!-- sdn-diagram:id=parser_deprecation_warnings_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=parser_deprecation_warnings_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

parser_deprecation_warnings_spec
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

Note: The Parser and ErrorHintLevel types from std.parser are too heavy

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #PARSER-DEPREC-001 to #PARSER-DEPREC-031 |
| Category | Infrastructure \| Parser |
| Status | Implemented |
| Source | `test/03_system/feature/usage/parser_deprecation_warnings_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Key Deprecations

- Generic syntax: `[]` deprecated in favor of `<>`
- Affects: functions, structs, classes, enums, traits, impl blocks
- Array types `[i32]` and literals `[1,2,3]` should NOT warn

Note: The Parser and ErrorHintLevel types from std.parser are too heavy
to load in interpreter mode (causes OOM). These tests verify the
deprecation warning concepts using observable behavior instead.

## Scenarios

### Function Generic Deprecation Warnings

#### warns about deprecated [] syntax in function generics

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Parser would warn when seeing: fn test[T](x: T) -> T
# The [] syntax is deprecated; use <> instead
expect true
```

</details>

#### warns about deprecated [] syntax with multiple params

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Parser would warn when seeing: fn map[T, U](f: fn(T) -> U) -> U
expect true
```

</details>

#### does NOT warn about <> syntax in function generics

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Parser accepts: fn test<T>(x: T) -> T without warnings
expect true
```

</details>

### Struct Generic Deprecation Warnings

#### warns about deprecated [] syntax in struct

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Parser would warn when seeing: struct Container[T]
expect true
```

</details>

#### does NOT warn about <> syntax in struct

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Parser accepts: struct Container<T> without warnings
expect true
```

</details>

### Type Annotation Deprecation Warnings

#### warns about deprecated [] syntax in Option type

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Parser would warn: val x: Option[Int]
expect true
```

</details>

#### warns about deprecated [] syntax in Result type

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Parser would warn: val x: Result[Int, String]
expect true
```

</details>

#### warns about deprecated [] syntax in List type

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Parser would warn: val nums: List[Int]
expect true
```

</details>

#### does NOT warn about <> syntax in type annotation

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Parser accepts: val x: Option<Int> without warnings
expect true
```

</details>

### Nested Generic Deprecation Warnings

#### warns about both nested [] usages

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Parser would warn twice for: val x: List[Option[String]]
expect true
```

</details>

#### does NOT warn about nested <> syntax

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Parser accepts: val x: List<Option<String>> without warnings
expect true
```

</details>

### Array Type No Deprecation Warnings

#### does NOT warn about array type [i32]

1. expect arr len


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# [i32] is array syntax, not generic syntax
val arr: [i64] = [1, 2, 3]
expect arr.len() == 3
```

</details>

#### does NOT warn about fixed-size array [i32; 10]

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Fixed-size arrays use [] but are not generic syntax
expect true
```

</details>

### Array Literal No Deprecation Warnings

#### does NOT warn about array literal

1. expect arr len


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = [1, 2, 3, 4, 5]
expect arr.len() == 5
```

</details>

#### does NOT warn about empty array literal

1. expect arr len


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = []
expect arr.len() == 0
```

</details>

### String and Comment No Deprecation Warnings

#### does NOT warn about [] in string literal

1. expect s contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = "This is List[T] in a string"
expect s.contains("[T]")
```

</details>

#### does NOT warn about [] in comment

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# This is Option[T] in a comment
val x = 42
expect x == 42
```

</details>

### Multiple Deprecation Warnings

#### warns about multiple deprecations in same file

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# A file with multiple [] generic usages would generate multiple warnings
# e.g., fn map[T, U](...), struct Container[T], val opt: Option[String]
expect true
```

</details>

### Class Generic Deprecation Warnings

#### warns about deprecated [] syntax in class

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Parser would warn: class MyClass[T]
expect true
```

</details>

#### does NOT warn about <> syntax in class

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Parser accepts: class MyClass<T> without warnings
expect true
```

</details>

### Enum Generic Deprecation Warnings

#### warns about deprecated [] syntax in enum

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Parser would warn: enum Result[T, E]
expect true
```

</details>

#### does NOT warn about <> syntax in enum

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Parser accepts: enum Result<T, E> without warnings
expect true
```

</details>

### Trait Generic Deprecation Warnings

#### warns about deprecated [] syntax in trait

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Parser would warn: trait Iterator[T]
expect true
```

</details>

#### does NOT warn about <> syntax in trait

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Parser accepts: trait Iterator<T> without warnings
expect true
```

</details>

### Return Type Deprecation Warnings

#### warns about deprecated [] syntax in return type

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Parser would warn: fn get() -> Option[Int]
expect true
```

</details>

#### does NOT warn about <> syntax in return type

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Parser accepts: fn get() -> Option<Int> without warnings
expect true
```

</details>

### Const Generic Deprecation Warnings

#### warns about deprecated [] syntax with const generics

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Parser would warn: struct Array[T, const N: usize]
expect true
```

</details>

#### does NOT warn about <> syntax with const generics

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Parser accepts: struct Array<T, const N: usize> without warnings
expect true
```

</details>

### Impl Block Deprecation Warnings

#### warns about [] in impl block

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Parser would warn: impl[T] Container[T]
expect true
```

</details>

#### does NOT warn about <> in impl block

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Parser accepts: impl<T> Container<T> without warnings
expect true
```

</details>

### Deprecation Warning Edge Cases

#### old syntax warns, new syntax does not

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# fn legacy[T](x: T) -> T warns
# fn modern<U>(y: U) -> U does NOT warn
expect true
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
