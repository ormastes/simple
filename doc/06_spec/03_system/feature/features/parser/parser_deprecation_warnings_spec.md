# Parser Deprecation Warnings Specification

> use std.spec.step

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 31 | 31 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Parser Deprecation Warnings Specification

use std.spec.step

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #PARSER-DEPREC-001 to #PARSER-DEPREC-031 |
| Category | Infrastructure \| Parser |
| Status | Implemented |
| Source | `test/03_system/feature/features/parser/parser_deprecation_warnings_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Key Deprecations

- Generic syntax: `[]` deprecated in favor of `<>`
- Affects: functions, structs, classes, enums, traits, impl blocks
- Array types `[i32]` and literals `[1,2,3]` should NOT warn

## API

```simple
use std.spec.step

use std.parser.{Parser, ErrorHint, ErrorHintLevel}

var parser = Parser.new(source)
parser.parse()
val hints = parser.error_hints()
```

## Scenarios

### Function Generic Deprecation Warnings

#### warns about deprecated [] syntax in function generics

- warns about deprecated [] syntax in function generics


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("warns about deprecated [] syntax in function generics")
var parser = Parser.new("fn test[T](x: T) -> T:\n    x")
parser.parse()
val hints = parser.error_hints()
val has_warning = hints.any(_1.level == ErrorHintLevel::Warning and h.message.contains("Deprecated"))
expect has_warning
```

</details>

#### warns about deprecated [] syntax with multiple params

- warns about deprecated [] syntax with multiple params


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("warns about deprecated [] syntax with multiple params")
var parser = Parser.new("fn map[T, U](f: fn(T) -> U) -> U:\n    pass")
parser.parse()
val hints = parser.error_hints()
val has_warning = hints.any(_1.level == ErrorHintLevel::Warning and h.message.contains("Deprecated"))
expect has_warning
```

</details>

#### does NOT warn about <> syntax in function generics

- does NOT warn about <> syntax in function generics


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("does NOT warn about <> syntax in function generics")
var parser = Parser.new("fn test<T>(x: T) -> T:\n    x")
parser.parse()
val hints = parser.error_hints()
val has_deprecation = hints.any(_1.message.contains("Deprecated") and h.message.contains("generic"))
expect not has_deprecation
```

</details>

### Struct Generic Deprecation Warnings

#### warns about deprecated [] syntax in struct

- warns about deprecated [] syntax in struct


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("warns about deprecated [] syntax in struct")
var parser = Parser.new("struct Container[T]:\n    value: T")
parser.parse()
val hints = parser.error_hints()
val has_warning = hints.any(_1.level == ErrorHintLevel::Warning and h.message.contains("Deprecated"))
expect has_warning
```

</details>

#### does NOT warn about <> syntax in struct

- does NOT warn about <> syntax in struct


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("does NOT warn about <> syntax in struct")
var parser = Parser.new("struct Container<T>:\n    value: T")
parser.parse()
val hints = parser.error_hints()
val has_deprecation = hints.any(_1.message.contains("Deprecated") and h.message.contains("generic"))
expect not has_deprecation
```

</details>

### Type Annotation Deprecation Warnings

#### warns about deprecated [] syntax in Option type

- warns about deprecated [] syntax in Option type


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("warns about deprecated [] syntax in Option type")
var parser = Parser.new("val x: Option[Int] = None")
parser.parse()
val hints = parser.error_hints()
val has_warning = hints.any(_1.level == ErrorHintLevel::Warning and h.message.contains("Deprecated"))
expect has_warning
```

</details>

#### warns about deprecated [] syntax in Result type

- warns about deprecated [] syntax in Result type


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("warns about deprecated [] syntax in Result type")
var parser = Parser.new("val x: Result[Int, String] = Ok(42)")
parser.parse()
val hints = parser.error_hints()
val has_warning = hints.any(_1.level == ErrorHintLevel::Warning and h.message.contains("Deprecated"))
expect has_warning
```

</details>

#### warns about deprecated [] syntax in List type

- warns about deprecated [] syntax in List type


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("warns about deprecated [] syntax in List type")
var parser = Parser.new("val nums: List[Int] = []")
parser.parse()
val hints = parser.error_hints()
val has_warning = hints.any(_1.level == ErrorHintLevel::Warning and h.message.contains("Deprecated"))
expect has_warning
```

</details>

#### does NOT warn about <> syntax in type annotation

- does NOT warn about <> syntax in type annotation


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("does NOT warn about <> syntax in type annotation")
var parser = Parser.new("val x: Option<Int> = None")
parser.parse()
val hints = parser.error_hints()
val has_deprecation = hints.any(_1.message.contains("Deprecated") and h.message.contains("generic"))
expect not has_deprecation
```

</details>

### Nested Generic Deprecation Warnings

#### warns about both nested [] usages

- warns about both nested [] usages


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("warns about both nested [] usages")
var parser = Parser.new("val x: List[Option[String]] = []")
parser.parse()
val hints = parser.error_hints()
val warning_count = hints.filter(_1.level == ErrorHintLevel::Warning and h.message.contains("Deprecated")).len()
expect warning_count >= 2
```

</details>

#### does NOT warn about nested <> syntax

- does NOT warn about nested <> syntax


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("does NOT warn about nested <> syntax")
var parser = Parser.new("val x: List<Option<String>> = []")
parser.parse()
val hints = parser.error_hints()
val has_deprecation = hints.any(_1.message.contains("Deprecated") and h.message.contains("generic"))
expect not has_deprecation
```

</details>

### Array Type No Deprecation Warnings

#### does NOT warn about array type [i32]

- does NOT warn about array type [i32]


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("does NOT warn about array type [i32]")
var parser = Parser.new("val arr: [i32] = [1, 2, 3]")
parser.parse()
val hints = parser.error_hints()
val has_deprecation = hints.any(_1.message.contains("Deprecated") and h.message.contains("generic"))
expect not has_deprecation
```

</details>

#### does NOT warn about fixed-size array [i32; 10]

- does NOT warn about fixed-size array [i32; 10]


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("does NOT warn about fixed-size array [i32; 10]")
var parser = Parser.new("val arr: [i32; 10] = []")
parser.parse()
val hints = parser.error_hints()
val has_deprecation = hints.any(_1.message.contains("Deprecated") and h.message.contains("generic"))
expect not has_deprecation
```

</details>

### Array Literal No Deprecation Warnings

#### does NOT warn about array literal

- does NOT warn about array literal


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("does NOT warn about array literal")
var parser = Parser.new("val arr = [1, 2, 3, 4, 5]")
parser.parse()
val hints = parser.error_hints()
val has_deprecation = hints.any(_1.message.contains("Deprecated") and h.message.contains("generic"))
expect not has_deprecation
```

</details>

#### does NOT warn about empty array literal

- does NOT warn about empty array literal


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("does NOT warn about empty array literal")
var parser = Parser.new("val arr = []")
parser.parse()
val hints = parser.error_hints()
val has_deprecation = hints.any(_1.message.contains("Deprecated") and h.message.contains("generic"))
expect not has_deprecation
```

</details>

### String and Comment No Deprecation Warnings

#### does NOT warn about [] in string literal

- does NOT warn about [] in string literal


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("does NOT warn about [] in string literal")
var parser = Parser.new("val s = \"This is List[T] in a string\"")
parser.parse()
val hints = parser.error_hints()
val has_deprecation = hints.any(_1.message.contains("Deprecated") and h.message.contains("generic"))
expect not has_deprecation
```

</details>

#### does NOT warn about [] in comment

- does NOT warn about [] in comment


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("does NOT warn about [] in comment")
var parser = Parser.new("# This is Option[T] in a comment\nval x = 42")
parser.parse()
val hints = parser.error_hints()
val has_deprecation = hints.any(_1.message.contains("Deprecated") and h.message.contains("generic"))
expect not has_deprecation
```

</details>

### Multiple Deprecation Warnings

#### warns about multiple deprecations in same file

- warns about multiple deprecations in same file


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("warns about multiple deprecations in same file")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `dad4c27fcf022eec8eb8465edef5ad608937d1d0d8155ad6bbd4aaf7e53893a4`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `dad4c27fcf022eec8eb8465edef5ad608937d1d0d8155ad6bbd4aaf7e53893a4`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `dad4c27fcf022eec8eb8465edef5ad608937d1d0d8155ad6bbd4aaf7e53893a4`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/feature/features/parser/parser_deprecation_warnings_spec.spl
mirror: doc/06_spec/03_system/feature/features/parser/parser_deprecation_warnings_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/features/parser/parser_deprecation_warnings_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/features/parser/parser_deprecation_warnings_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/features/parser/parser_deprecation_warnings_spec.spl:52:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'warns about deprecated [] syntax in function generics' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/features/parser/parser_deprecation_warnings_spec.spl:61:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'warns about deprecated [] syntax with multiple params' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/features/parser/parser_deprecation_warnings_spec.spl:70:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'does NOT warn about <> syntax in function generics' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
