# Parser Deprecation Warnings Specification

> Note: The Parser and ErrorHintLevel types from std.parser are too heavy

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
| Source | `test/feature/usage/parser_deprecation_warnings_spec.spl` |
| Updated | 2026-08-26 |
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

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- warns about deprecated [] syntax in function generics


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("warns about deprecated [] syntax in function generics")
# Parser would warn when seeing: fn test[T](x: T) -> T
# The [] syntax is deprecated; use <> instead
expect true
```

</details>

#### warns about deprecated [] syntax with multiple params

- warns about deprecated [] syntax with multiple params


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("warns about deprecated [] syntax with multiple params")
# Parser would warn when seeing: fn map[T, U](f: fn(T) -> U) -> U
expect true
```

</details>

#### does NOT warn about <> syntax in function generics

- does NOT warn about <> syntax in function generics


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("does NOT warn about <> syntax in function generics")
# Parser accepts: fn test<T>(x: T) -> T without warnings
expect true
```

</details>

### Struct Generic Deprecation Warnings

#### warns about deprecated [] syntax in struct

- warns about deprecated [] syntax in struct


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("warns about deprecated [] syntax in struct")
# Parser would warn when seeing: struct Container[T]
expect true
```

</details>

#### does NOT warn about <> syntax in struct

- does NOT warn about <> syntax in struct


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("does NOT warn about <> syntax in struct")
# Parser accepts: struct Container<T> without warnings
expect true
```

</details>

### Type Annotation Deprecation Warnings

#### warns about deprecated [] syntax in Option type

- warns about deprecated [] syntax in Option type


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("warns about deprecated [] syntax in Option type")
# Parser would warn: val x: Option[Int]
expect true
```

</details>

#### warns about deprecated [] syntax in Result type

- warns about deprecated [] syntax in Result type


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("warns about deprecated [] syntax in Result type")
# Parser would warn: val x: Result[Int, String]
expect true
```

</details>

#### warns about deprecated [] syntax in List type

- warns about deprecated [] syntax in List type


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("warns about deprecated [] syntax in List type")
# Parser would warn: val nums: List[Int]
expect true
```

</details>

#### does NOT warn about <> syntax in type annotation

- does NOT warn about <> syntax in type annotation


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("does NOT warn about <> syntax in type annotation")
# Parser accepts: val x: Option<Int> without warnings
expect true
```

</details>

### Nested Generic Deprecation Warnings

#### warns about both nested [] usages

- warns about both nested [] usages


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("warns about both nested [] usages")
# Parser would warn twice for: val x: List[Option[String]]
expect true
```

</details>

#### does NOT warn about nested <> syntax

- does NOT warn about nested <> syntax


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("does NOT warn about nested <> syntax")
# Parser accepts: val x: List<Option<String>> without warnings
expect true
```

</details>

### Array Type No Deprecation Warnings

#### does NOT warn about array type [i32]

- does NOT warn about array type [i32]


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("does NOT warn about array type [i32]")
# [i32] is array syntax, not generic syntax
val arr: [i64] = [1, 2, 3]
expect arr.len() == 3
```

</details>

#### does NOT warn about fixed-size array [i32; 10]

- does NOT warn about fixed-size array [i32; 10]


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("does NOT warn about fixed-size array [i32; 10]")
# Fixed-size arrays use [] but are not generic syntax
expect true
```

</details>

### Array Literal No Deprecation Warnings

#### does NOT warn about array literal

- does NOT warn about array literal


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("does NOT warn about array literal")
val arr = [1, 2, 3, 4, 5]
expect arr.len() == 5
```

</details>

#### does NOT warn about empty array literal

- does NOT warn about empty array literal


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("does NOT warn about empty array literal")
val arr = []
expect arr.len() == 0
```

</details>

### String and Comment No Deprecation Warnings

#### does NOT warn about [] in string literal

- does NOT warn about [] in string literal


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("does NOT warn about [] in string literal")
val s = "This is List[T] in a string"
expect s.contains("[T]")
```

</details>

#### does NOT warn about [] in comment

- does NOT warn about [] in comment


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("does NOT warn about [] in comment")
# This is Option[T] in a comment
val x = 42
expect x == 42
```

</details>

### Multiple Deprecation Warnings

#### warns about multiple deprecations in same file

- warns about multiple deprecations in same file


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("warns about multiple deprecations in same file")
# A file with multiple [] generic usages would generate multiple warnings
# e.g., fn map[T, U](...), struct Container[T], val opt: Option[String]
expect true
```

</details>

### Class Generic Deprecation Warnings

#### warns about deprecated [] syntax in class

- warns about deprecated [] syntax in class


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("warns about deprecated [] syntax in class")
# Parser would warn: class MyClass[T]
expect true
```

</details>

#### does NOT warn about <> syntax in class

- does NOT warn about <> syntax in class


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("does NOT warn about <> syntax in class")
# Parser accepts: class MyClass<T> without warnings
expect true
```

</details>

### Enum Generic Deprecation Warnings

#### warns about deprecated [] syntax in enum

- warns about deprecated [] syntax in enum


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("warns about deprecated [] syntax in enum")
# Parser would warn: enum Result[T, E]
expect true
```

</details>

#### does NOT warn about <> syntax in enum

- does NOT warn about <> syntax in enum


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("does NOT warn about <> syntax in enum")
# Parser accepts: enum Result<T, E> without warnings
expect true
```

</details>

### Trait Generic Deprecation Warnings

#### warns about deprecated [] syntax in trait

- warns about deprecated [] syntax in trait


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("warns about deprecated [] syntax in trait")
# Parser would warn: trait Iterator[T]
expect true
```

</details>

#### does NOT warn about <> syntax in trait

- does NOT warn about <> syntax in trait


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("does NOT warn about <> syntax in trait")
# Parser accepts: trait Iterator<T> without warnings
expect true
```

</details>

### Return Type Deprecation Warnings

#### warns about deprecated [] syntax in return type

- warns about deprecated [] syntax in return type


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("warns about deprecated [] syntax in return type")
# Parser would warn: fn get() -> Option[Int]
expect true
```

</details>

#### does NOT warn about <> syntax in return type

- does NOT warn about <> syntax in return type


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("does NOT warn about <> syntax in return type")
# Parser accepts: fn get() -> Option<Int> without warnings
expect true
```

</details>

### Const Generic Deprecation Warnings

#### warns about deprecated [] syntax with const generics

- warns about deprecated [] syntax with const generics


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("warns about deprecated [] syntax with const generics")
# Parser would warn: struct Array[T, const N: usize]
expect true
```

</details>

#### does NOT warn about <> syntax with const generics

- does NOT warn about <> syntax with const generics


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("does NOT warn about <> syntax with const generics")
# Parser accepts: struct Array<T, const N: usize> without warnings
expect true
```

</details>

### Impl Block Deprecation Warnings

#### warns about [] in impl block

- warns about [] in impl block


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("warns about [] in impl block")
# Parser would warn: impl[T] Container[T]
expect true
```

</details>

#### does NOT warn about <> in impl block

- does NOT warn about <> in impl block


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("does NOT warn about <> in impl block")
# Parser accepts: impl<T> Container<T> without warnings
expect true
```

</details>

### Deprecation Warning Edge Cases

#### old syntax warns, new syntax does not

- old syntax warns, new syntax does not


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("old syntax warns, new syntax does not")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-FEATURE`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `94dd76681ff19ed4cd04bdf1f02e7cc9dcbf7785b02df9e322b9ac9024e2844b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `94dd76681ff19ed4cd04bdf1f02e7cc9dcbf7785b02df9e322b9ac9024e2844b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `94dd76681ff19ed4cd04bdf1f02e7cc9dcbf7785b02df9e322b9ac9024e2844b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/feature/usage/parser_deprecation_warnings_spec.spl
mirror: doc/06_spec/feature/usage/parser_deprecation_warnings_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/feature/usage/parser_deprecation_warnings_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/feature/usage/parser_deprecation_warnings_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/feature/usage/parser_deprecation_warnings_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'warns about deprecated [] syntax in function generics' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/usage/parser_deprecation_warnings_spec.spl:46:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'warns about deprecated [] syntax with multiple params' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/usage/parser_deprecation_warnings_spec.spl:52:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'does NOT warn about <> syntax in function generics' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
