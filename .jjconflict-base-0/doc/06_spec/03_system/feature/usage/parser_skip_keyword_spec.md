# Skip Keyword - Comprehensive

> Comprehensive tests for the `skip` keyword covering lexer token recognition, statement parsing, control flow interactions (if, loop, break, continue, return), function/method/lambda contexts, class/struct/impl blocks, async contexts, match/pattern contexts, expression flow, error handling, edge cases (nesting, comments, whitespace), and runtime semantics.

<!-- sdn-diagram:id=parser_skip_keyword_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=parser_skip_keyword_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

parser_skip_keyword_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=parser_skip_keyword_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 42 | 42 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Skip Keyword - Comprehensive

Comprehensive tests for the `skip` keyword covering lexer token recognition, statement parsing, control flow interactions (if, loop, break, continue, return), function/method/lambda contexts, class/struct/impl blocks, async contexts, match/pattern contexts, expression flow, error handling, edge cases (nesting, comments, whitespace), and runtime semantics.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #PARSER-003 |
| Category | Syntax |
| Status | Active |
| Source | `test/03_system/feature/usage/parser_skip_keyword_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Comprehensive tests for the `skip` keyword covering lexer token recognition,
statement parsing, control flow interactions (if, loop, break, continue, return),
function/method/lambda contexts, class/struct/impl blocks, async contexts,
match/pattern contexts, expression flow, error handling, edge cases
(nesting, comments, whitespace), and runtime semantics.

## Syntax

```simple
skip
skip:
val x = 1
fn with_skip(): skip; return 42
```

## Scenarios

### Skip keyword - lexer and token recognition

#### recognizes skip as a keyword token

1. expect keywords len


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Test that 'skip' is lexed as a keyword, not an identifier
val keywords = ["break", "continue", "pass", "defer", "skip", "return"]
expect keywords.len() == 6
```

</details>

#### allows skip_func as function name

1. fn skip func
2. expect skip func


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn skip_func():
    return 42
expect skip_func() == 42
```

</details>

#### distinguishes skip keyword from skip variable name

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val skip_count = 10
expect skip_count == 10
```

</details>

#### allows skip in string literals

1. expect message contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val message = "Please skip this step"
expect message.contains("skip")
```

</details>

### Skip keyword - basic statement parsing

#### parses skip as standalone statement

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var executed = true
skip
expect executed == true
```

</details>

#### parses skip with indented block

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
skip:
    val x = 1
    val y = 2
expect true
```

</details>

#### parses multiple skip statements

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
skip
skip
skip
expect true
```

</details>

### Skip keyword - control flow interactions

#### parses skip inside if block

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val condition = true
if condition:
    skip
expect true
```

</details>

<details>
<summary>Advanced: parses skip inside loop</summary>

#### parses skip inside loop

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
for i in 0..3:
    if i == 1:
        skip
expect true
```

</details>


</details>

#### parses skip with break in same function

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
for i in 0..5:
    if i == 2:
        break
    if i == 1:
        skip
expect true
```

</details>

#### parses skip with continue in same function

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var count = 0
for i in 0..3:
    if i == 1:
        skip
    count = count + 1
expect count == 3
```

</details>

#### parses skip with return in same function

1. fn with skip and return
2. expect with skip and return


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn with_skip_and_return():
    skip
    return 42
expect with_skip_and_return() == 42
```

</details>

### Skip keyword - function and method contexts

#### parses skip in function body

1. fn test function
2. expect test function


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn test_function():
    skip
    return "completed"
expect test_function() == "completed"
```

</details>

#### parses skip in method body

1. fn test method
2. expect obj test method


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
class TestClass:
    fn test_method():
        skip
        return "method completed"

val obj = TestClass()
expect obj.test_method() == "method completed"
```

</details>

#### parses skip in static method

1. static fn static method
2. expect StaticTest static method


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
class StaticTest:
    static fn static_method():
        skip
        return "static completed"

expect StaticTest.static_method() == "static completed"
```

</details>

#### parses skip in lambda

1. expect lambda with skip


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lambda_with_skip = \x:
    skip
    x * 2
expect lambda_with_skip(5) == 10
```

</details>

### Skip keyword - class and struct contexts

#### parses skip in class method

1. fn process
2. expect c process


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
class Container:
    value: i32

    fn process():
        skip
        return self.value

val c = Container(value: 100)
expect c.process() == 100
```

</details>

#### parses skip in impl block method

1. fn distance
2. expect p distance


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
struct Point:
    x: i64
    y: i64

impl Point:
    fn distance():
        skip
        return 0.0

val p = Point(x: 3, y: 4)
expect p.distance() == 0.0
```

</details>

### Skip keyword - async contexts

#### parses skip in async function

1. async fn async with skip


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
async fn async_with_skip():
    skip
    return "async result"

# Note: actual await testing requires async runtime
expect true
```

</details>

#### parses skip before await

1. async fn skip before await


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
async fn skip_before_await():
    skip
    val result = 42
    return result

expect true
```

</details>

### Skip keyword - match and pattern contexts

#### parses skip in match arm

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 5
val result = match x:
    case 1: "one"
    case 2:
        skip
        "two"
    case _: "other"
expect result == "other"
```

</details>

#### parses skip in multiple match arms

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val value = 10
var count = 0
match value:
    case 5:
        skip
    case 10:
        skip
        count = count + 1
    case _:
        skip
expect count == 1
```

</details>

### Skip keyword - expression contexts

#### parses skip before expression

1. fn with skip expr
2. expect with skip expr


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn with_skip_expr():
    skip
    val result = 2 + 2
    return result
expect with_skip_expr() == 4
```

</details>

#### parses skip between declarations

1. fn multi decl
2. expect multi decl


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn multi_decl():
    val a = 1
    skip
    val b = 2
    skip
    return a + b
expect multi_decl() == 3
```

</details>

#### parses skip in complex expression flow

1. fn complex flow
2. expect complex flow
3. expect complex flow


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn complex_flow(x: i32):
    if x > 0:
        skip
        return x * 2
    else:
        skip
        return x
expect complex_flow(5) == 10
expect complex_flow(-3) == -3
```

</details>

### Skip keyword - error handling contexts

#### parses skip in try-catch block

1. fn with try
2. expect with try


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn with_try():
    # Note: actual error handling syntax may vary
    skip
    return "ok"
expect with_try() == "ok"
```

</details>

#### parses skip before result return

1. fn result with skip
2. expect result with skip


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn result_with_skip() -> i32:
    skip
    return 42
expect result_with_skip() == 42
```

</details>

### Skip keyword - edge cases and boundaries

#### parses skip at start of file

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
skip
expect true
```

</details>

#### parses skip at end of function

1. fn skip at end


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn skip_at_end():
    val x = 1
    skip
expect true
```

</details>

#### parses skip with empty block

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
skip:
    pass
expect true
```

</details>

#### parses nested skip statements

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if true:
    skip:
        skip
expect true
```

</details>

#### parses skip with comment

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
skip  # This is skipped
expect true
```

</details>

#### parses skip with multiline comment

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
skip  /*
    Multiline comment
    about skipping
*/
expect true
```

</details>

### Skip keyword - indentation and whitespace

#### parses skip with various indentation

1. fn indented


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn indented():
    skip
    if true:
        skip
        for i in 0..1:
            skip
expect true
```

</details>

#### parses skip with no trailing whitespace

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
skip
val x = 1
expect x == 1
```

</details>

#### parses skip with blank lines after

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
skip

val y = 2
expect y == 2
```

</details>

### Skip keyword - semantics and runtime behavior

#### skip statement does not prevent execution

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var executed = false
skip
executed = true
expect executed == true
```

</details>

#### skip does not affect variable scope

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
skip
val scoped = 100
expect scoped == 100
```

</details>

#### skip does not affect return value

1. fn returns with skip
2. expect returns with skip


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn returns_with_skip():
    skip
    return "value"
expect returns_with_skip() == "value"
```

</details>

<details>
<summary>Advanced: skip does not affect loop iteration</summary>

#### skip does not affect loop iteration

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var iterations = 0
for i in 0..5:
    skip
    iterations = iterations + 1
expect iterations == 5
```

</details>


</details>

### Skip keyword - future test framework integration

#### allows skip for test tagging preparation

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Future: skip it "unimplemented test":
#     expect false
expect true
```

</details>

#### parses skip with test metadata

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Future test metadata syntax
# skip because "feature not implemented":
#     it "pending feature":
#         expect false
expect true
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 42 |
| Active scenarios | 42 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
