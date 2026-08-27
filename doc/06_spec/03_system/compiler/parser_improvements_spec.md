# parser_improvements_spec

> Parser Improvement Tests for the Simple language compiler.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 19 | 19 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# parser_improvements_spec

Parser Improvement Tests for the Simple language compiler.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/03_system/compiler/parser_improvements_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Parser Improvement Tests for the Simple language compiler.
Validates implemented parser enhancements including match arrow syntax,
function return types, generics, struct literals, and string operations.

## Scenarios

### Parser Improvements - Working Features

#### Match Arrow Syntax

#### supports arrow syntax in match expressions

- supports arrow syntax in match expressions


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("supports arrow syntax in match expressions")
val value = 2
val result = match value:
    1 -> "one"
    2 -> "two"
    _ -> "other"
expect result == "two"
```

</details>

#### supports multiple patterns with arrows

- supports multiple patterns with arrows


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("supports multiple patterns with arrows")
val x = 3
val msg = match x:
    0 -> "zero"
    1 -> "one"
    2 -> "two"
    _ -> "many"
expect msg == "many"
```

</details>

#### Function Return Types

#### parses return type annotations

- parses return type annotations


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses return type annotations")
expect double(5) == 10
```

</details>

#### supports complex return types

- supports complex return types


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("supports complex return types")
val result = make_pair(42)
expect result.is_some == true
```

</details>

#### Generic Types

#### supports Option generic type

- supports Option generic type


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("supports Option generic type")
val v = make_pair(42)
expect v.unwrap() == 42
```

</details>

#### supports Result generic type

- supports Result generic type


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("supports Result generic type")
val r = compute()
expect r.is_ok == true
```

</details>

#### Struct Literal Syntax

#### supports named field initialization

- supports named field initialization


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("supports named field initialization")
val p = Point { x: 10, y: 20 }
expect p.x == 10
expect p.y == 20
```

</details>

#### supports multi-line struct literals

- supports multi-line struct literals


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("supports multi-line struct literals")
val c = Config {
    name: "test",
    value: 42
}
expect c.name == "test"
```

</details>

#### text Multiplication

#### repeats string with * operator

- repeats string with * operator


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("repeats string with * operator")
val sep = "=" * 5
expect sep == "====="
```

</details>

#### handles zero repetition

- handles zero repetition


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("handles zero repetition")
val empty = "x" * 0
expect empty == ""
```

</details>

#### handles single repetition

- handles single repetition


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("handles single repetition")
val single = "ab" * 1
expect single == "ab"
```

</details>

### Parser Improvements - Now Implemented

#### Multi-line Method Chaining

#### supports method chaining across lines

- supports method chaining across lines


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("supports method chaining across lines")
# Multi-line chaining now works
class ChainBuilder:
    val_: i32
    static fn start() -> ChainBuilder:
        ChainBuilder(val_: 0)
    me add(n: i32) -> ChainBuilder:
        self.val_ = self.val_ + n
        self
val result = ChainBuilder__start()
    .add(1)
    .add(2)
expect result.val_ == 3
```

</details>

#### supports fluent interface pattern

- supports fluent interface pattern


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("supports fluent interface pattern")
class Fluent:
    data: text
    static fn create() -> Fluent:
        Fluent(data: "")
    me append(s: text) -> Fluent:
        self.data = self.data + s
        self
val f = Fluent__create()
    .append("a")
    .append("b")
expect f.data == "ab"
```

</details>

#### Enum Variant Construction

#### supports qualified enum variant creation

- supports qualified enum variant creation


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("supports qualified enum variant creation")
val variant = ParserImprovementVariant.Ready
val result = match variant:
    ParserImprovementVariant.Ready -> "ready"
    _ -> "other"
expect result == "ready"
```

</details>

#### supports enum variant with data

- supports enum variant with data


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("supports enum variant with data")
val variant = ParserImprovementVariant.WithData(7)
val result = match variant:
    ParserImprovementVariant.WithData(value) -> value
    _ -> 0
expect result == 7
```

</details>

#### Qualified Method Calls

#### supports method call chains

- supports method call chains


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("supports method call chains")
# Basic method chaining works
class Container:
    inner_val: i32
    static fn create() -> Container:
        Container(inner_val: 42)
    fn get_value() -> i32:
        self.inner_val
val v = Container__create().get_value()
expect v == 42
```

</details>

#### supports module-level access

- supports module-level access


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("supports module-level access")
# Module function access works via alias
# sp imported at module level (use inside it blocks causes stack overflow)
sp.expect(true == true)
```

</details>

#### String Interpolation

#### supports string interpolation with variables

- supports string interpolation with variables


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("supports string interpolation with variables")
val name = "World"
val greeting = "Hello, {name}!"
expect greeting == "Hello, World!"
```

</details>

#### supports expressions in braces

- supports expressions in braces


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("supports expressions in braces")
val x = 5
val y = 3
val result = "Sum: {x + y}"
expect result == "Sum: 8"
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `a92827209eb0db16ce53228526459b2b62db547d7898aca1732e300c7217ec47`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a92827209eb0db16ce53228526459b2b62db547d7898aca1732e300c7217ec47`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a92827209eb0db16ce53228526459b2b62db547d7898aca1732e300c7217ec47`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/compiler/parser_improvements_spec.spl
mirror: doc/06_spec/03_system/compiler/parser_improvements_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/compiler/parser_improvements_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/compiler/parser_improvements_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/compiler/parser_improvements_spec.spl:56:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'supports arrow syntax in match expressions' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/compiler/parser_improvements_spec.spl:66:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'supports multiple patterns with arrows' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/compiler/parser_improvements_spec.spl:80:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses return type annotations' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
