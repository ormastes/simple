# Parser Syntax Validation Specification

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 36 | 36 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Parser Syntax Validation Specification

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #PARSER-VAL-001 to #PARSER-VAL-015 |
| Category | Infrastructure \| Parser |
| Status | Implemented |
| Source | `test/03_system/feature/usage/parser_syntax_validation_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Key Validations

- Proper indentation handling
- Comment parsing (single-line, multi-line)
- Whitespace handling
- Newline requirements
- Block structure validation

## Scenarios

### Comment Parsing

#### single-line comments

#### parses code with trailing comment

- parses code with trailing comment


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses code with trailing comment")
val x = 42  # This is a comment
expect x == 42
```

</details>

#### parses comment-only lines

- parses comment-only lines


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses comment-only lines")
# This is a full-line comment
val x = 42
# Another comment
expect x == 42
```

</details>

#### parses multiple comment styles

- parses multiple comment styles


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses multiple comment styles")
val x = 42  # Hash comment
expect x == 42
```

</details>

#### multi-line comments

#### parses block comment

- parses block comment


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses block comment")
# This is a multi-line comment
# that spans several lines.
val x = 42
expect x == 42
```

</details>

#### parses inline docstring

- parses inline docstring


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses inline docstring")
fn documented() -> i64:
    # Returns the answer.
    42
expect documented() == 42
```

</details>

### Indentation Handling

#### parses simple indented block

- parses simple indented block


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses simple indented block")
if true:
    val x = 42
    expect x == 42
```

</details>

#### parses nested indentation

- parses nested indentation


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses nested indentation")
if true:
    if true:
        if true:
            val x = 42
            expect x == 42
```

</details>

#### parses dedent correctly

- parses dedent correctly


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses dedent correctly")
var total = 0
if true:
    total = 10
if true:
    total = total + 32
expect total == 42
```

</details>

#### parses multiple statements in block

- parses multiple statements in block


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses multiple statements in block")
var a = 0
var b = 0
if true:
    a = 10
    b = 20
    val c = 12
    a = a + c
expect a + b == 42
```

</details>

### Correct Keyword Usage

#### variable keywords

#### uses val for immutable

- uses val for immutable


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("uses val for immutable")
val x = 42
expect x == 42
```

</details>

#### uses var for mutable

- uses var for mutable


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("uses var for mutable")
var x = 0
x = 42
expect x == 42
```

</details>

#### uses let for binding

- uses let for binding


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("uses let for binding")
let x = 42
expect x == 42
```

</details>

#### function keywords

#### uses fn for function

- uses fn for function


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("uses fn for function")
fn get_value() -> i64:
    42
expect get_value() == 42
```

</details>

#### uses return for early return

- uses return for early return


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("uses return for early return")
fn check(x: i64) -> i64:
    if x < 0:
        return 0
    x
expect check(42) == 42
```

</details>

#### control flow keywords

#### uses elif not else if

- uses elif not else if


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("uses elif not else if")
fn classify(x: i64) -> text:
    if x < 0:
        "negative"
    elif x == 0:
        "zero"
    else:
        "positive"
expect classify(5) == "positive"
```

</details>

### Boolean Literal Validation

#### uses lowercase true

- uses lowercase true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("uses lowercase true")
val x = true
expect x == true
```

</details>

#### uses lowercase false

- uses lowercase false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("uses lowercase false")
val x = false
expect x == false
```

</details>

#### uses booleans in conditions

- uses booleans in conditions


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("uses booleans in conditions")
if true:
    expect true
if not false:
    expect true
```

</details>

### Nil Value Validation

#### uses nil for null value

- uses nil for null value


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("uses nil for null value")
val x = nil
expect x == nil
```

</details>

#### uses None for Option

- uses None for Option


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("uses None for Option")
val opt: Option<i64> = None
expect not opt.?
```

</details>

#### uses Some for Option with value

- uses Some for Option with value


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("uses Some for Option with value")
val opt = Some(42)
expect opt.?
```

</details>

### Type Annotation Validation

#### uses colon for type annotation

- uses colon for type annotation


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("uses colon for type annotation")
val x: i64 = 42
expect x == 42
```

</details>

#### uses arrow for return type

- uses arrow for return type


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("uses arrow for return type")
fn get_value() -> i64:
    42
expect get_value() == 42
```

</details>

#### uses angle brackets for generics

- uses angle brackets for generics


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("uses angle brackets for generics")
fn identity<T>(x: T) -> T:
    x
expect identity(42) == 42
```

</details>

#### uses Option for optional types

- uses Option for optional types


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("uses Option for optional types")
val opt: Option<i64> = Some(42)
expect opt.unwrap() == 42
```

</details>

### String Syntax Validation

#### uses double quotes for interpolated strings

- uses double quotes for interpolated strings


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("uses double quotes for interpolated strings")
val name = "World"
val greeting = "Hello, {name}!"
expect greeting == "Hello, World!"
```

</details>

#### uses single quotes for raw strings

- uses single quotes for raw strings


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("uses single quotes for raw strings")
val raw = 'Hello\nWorld'
expect raw.contains("\\n")
```

</details>

#### uses r prefix for raw double-quoted

- uses r prefix for raw double-quoted


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("uses r prefix for raw double-quoted")
val raw = r"Path\to\file"
expect raw.contains("\\")
```

</details>

### Collection Syntax Validation

#### uses square brackets for arrays

- uses square brackets for arrays


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("uses square brackets for arrays")
val arr = [1, 2, 3]
expect arr.len() == 3
```

</details>

#### uses parentheses for tuples

- uses parentheses for tuples


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("uses parentheses for tuples")
val t = (1, 2, 3)
expect t.0 == 1
```

</details>

#### uses braces for dictionaries

- uses braces for dictionaries


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("uses braces for dictionaries")
val d = {"key": 42}
expect d["key"] == 42
```

</details>

### Struct Instantiation Validation

#### uses braces for struct literal

- uses braces for struct literal


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("uses braces for struct literal")
struct Point:
    x: i64
    y: i64
val p = Point { x: 10, y: 20 }
expect p.x == 10
```

</details>

#### uses colon in struct literal

- uses colon in struct literal


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("uses colon in struct literal")
struct Data:
    value: i64
val d = Data { value: 42 }
expect d.value == 42
```

</details>

### Pattern Matching Validation

#### uses case keyword for patterns

- uses case keyword for patterns


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("uses case keyword for patterns")
fn classify(x: i64) -> text:
    match x:
        case 0:
            "zero"
        case _:
            "other"
expect classify(0) == "zero"
```

</details>

#### uses if for guards

- uses if for guards


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("uses if for guards")
fn classify(x: i64) -> text:
    match x:
        case n if n < 0:
            "negative"
        case _:
            "non-negative"
expect classify(-5) == "negative"
```

</details>

#### uses double colon for enum variants

- uses double colon for enum variants


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("uses double colon for enum variants")
enum Status:
    Ok
    Error
fn check(s: Status) -> text:
    match s:
        case Status.Ok:
            "ok"
        case Status.Error:
            "error"
expect check(Status.Ok) == "ok"
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 36 |
| Active scenarios | 36 |
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

- Canonical SPipe generation for source `732964c0cf52e942afd3595521b470766299e8339204e369a41f07fb49752ce6`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `732964c0cf52e942afd3595521b470766299e8339204e369a41f07fb49752ce6`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `732964c0cf52e942afd3595521b470766299e8339204e369a41f07fb49752ce6`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/feature/usage/parser_syntax_validation_spec.spl
mirror: doc/06_spec/03_system/feature/usage/parser_syntax_validation_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/usage/parser_syntax_validation_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/usage/parser_syntax_validation_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/usage/parser_syntax_validation_spec.spl:46:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses code with trailing comment' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/usage/parser_syntax_validation_spec.spl:52:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses comment-only lines' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/usage/parser_syntax_validation_spec.spl:60:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses multiple comment styles' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
