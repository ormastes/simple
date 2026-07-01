# Parser Syntax Validation Specification

> <details>

<!-- sdn-diagram:id=parser_syntax_validation_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=parser_syntax_validation_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

parser_syntax_validation_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=parser_syntax_validation_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

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
| Updated | 2026-06-01 |
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 42  # This is a comment
expect x == 42
```

</details>

#### parses comment-only lines

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# This is a full-line comment
val x = 42
# Another comment
expect x == 42
```

</details>

#### parses multiple comment styles

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 42  # Hash comment
expect x == 42
```

</details>

#### multi-line comments

#### parses block comment

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# This is a multi-line comment
# that spans several lines.
val x = 42
expect x == 42
```

</details>

#### parses inline docstring

1. fn documented
2. expect documented


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn documented() -> i64:
    # Returns the answer.
    42
expect documented() == 42
```

</details>

### Indentation Handling

#### parses simple indented block

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if true:
    val x = 42
    expect x == 42
```

</details>

#### parses nested indentation

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if true:
    if true:
        if true:
            val x = 42
            expect x == 42
```

</details>

#### parses dedent correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var total = 0
if true:
    total = 10
if true:
    total = total + 32
expect total == 42
```

</details>

#### parses multiple statements in block

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 42
expect x == 42
```

</details>

#### uses var for mutable

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var x = 0
x = 42
expect x == 42
```

</details>

#### uses let for binding

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
let x = 42
expect x == 42
```

</details>

#### function keywords

#### uses fn for function

1. fn get value
2. expect get value


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn get_value() -> i64:
    42
expect get_value() == 42
```

</details>

#### uses return for early return

1. fn check
2. expect check


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn check(x: i64) -> i64:
    if x < 0:
        return 0
    x
expect check(42) == 42
```

</details>

#### control flow keywords

#### uses elif not else if

1. fn classify
2. expect classify


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = true
expect x == true
```

</details>

#### uses lowercase false

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = false
expect x == false
```

</details>

#### uses booleans in conditions

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if true:
    expect true
if not false:
    expect true
```

</details>

### Nil Value Validation

#### uses nil for null value

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = nil
expect x == nil
```

</details>

#### uses None for Option

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opt: Option<i64> = None
expect not opt.?
```

</details>

#### uses Some for Option with value

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opt = Some(42)
expect opt.?
```

</details>

### Type Annotation Validation

#### uses colon for type annotation

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x: i64 = 42
expect x == 42
```

</details>

#### uses arrow for return type

1. fn get value
2. expect get value


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn get_value() -> i64:
    42
expect get_value() == 42
```

</details>

#### uses angle brackets for generics

1. fn identity<T>
2. expect identity


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn identity<T>(x: T) -> T:
    x
expect identity(42) == 42
```

</details>

#### uses Option for optional types

1. expect opt unwrap


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opt: Option<i64> = Some(42)
expect opt.unwrap() == 42
```

</details>

### String Syntax Validation

#### uses double quotes for interpolated strings

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val name = "World"
val greeting = "Hello, {name}!"
expect greeting == "Hello, World!"
```

</details>

#### uses single quotes for raw strings

1. expect raw contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val raw = 'Hello\nWorld'
expect raw.contains("\\n")
```

</details>

#### uses r prefix for raw double-quoted

1. expect raw contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val raw = r"Path\to\file"
expect raw.contains("\\")
```

</details>

### Collection Syntax Validation

#### uses square brackets for arrays

1. expect arr len


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = [1, 2, 3]
expect arr.len() == 3
```

</details>

#### uses parentheses for tuples

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = (1, 2, 3)
expect t.0 == 1
```

</details>

#### uses braces for dictionaries

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val d = {"key": 42}
expect d["key"] == 42
```

</details>

### Struct Instantiation Validation

#### uses braces for struct literal

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
struct Point:
    x: i64
    y: i64
val p = Point { x: 10, y: 20 }
expect p.x == 10
```

</details>

#### uses colon in struct literal

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
struct Data:
    value: i64
val d = Data { value: 42 }
expect d.value == 42
```

</details>

### Pattern Matching Validation

#### uses case keyword for patterns

1. fn classify
2. expect classify


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. fn classify
2. expect classify


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. fn check
2. expect check


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
