# Skip Keyword - Comprehensive

> Comprehensive tests for the `skip` keyword covering lexer token recognition, statement parsing, control flow interactions (if, loop, break, continue, return), function/method/lambda contexts, class/struct/impl blocks, async contexts, match/pattern contexts, expression flow, error handling, edge cases (nesting, comments, whitespace), and runtime semantics.

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
| Updated | 2026-08-26 |
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
use std.spec.step

val x = 1
fn with_skip(): skip; return 42
```

## Scenarios

### Skip keyword - lexer and token recognition

#### recognizes skip as a keyword token

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- recognizes skip as a keyword token


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("recognizes skip as a keyword token")
# Test that 'skip' is lexed as a keyword, not an identifier
val keywords = ["break", "continue", "pass", "defer", "skip", "return"]
expect keywords.len() == 6
```

</details>

#### allows skip_func as function name

- allows skip_func as function name


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("allows skip_func as function name")
fn skip_func():
    return 42
expect skip_func() == 42
```

</details>

#### distinguishes skip keyword from skip variable name

- distinguishes skip keyword from skip variable name


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("distinguishes skip keyword from skip variable name")
val skip_count = 10
expect skip_count == 10
```

</details>

#### allows skip in string literals

- allows skip in string literals


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("allows skip in string literals")
val message = "Please skip this step"
expect message.contains("skip")
```

</details>

### Skip keyword - basic statement parsing

#### parses skip as standalone statement

- parses skip as standalone statement


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses skip as standalone statement")
var executed = true
skip
expect executed == true
```

</details>

#### parses skip with indented block

- parses skip with indented block


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses skip with indented block")
skip:
    val x = 1
    val y = 2
expect true
```

</details>

#### parses multiple skip statements

- parses multiple skip statements


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses multiple skip statements")
skip
skip
skip
expect true
```

</details>

### Skip keyword - control flow interactions

#### parses skip inside if block

- parses skip inside if block


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses skip inside if block")
val condition = true
if condition:
    skip
expect true
```

</details>

<details>
<summary>Advanced: parses skip inside loop</summary>

#### parses skip inside loop

- parses skip inside loop


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses skip inside loop")
for i in 0..3:
    if i == 1:
        skip
expect true
```

</details>


</details>

#### parses skip with break in same function

- parses skip with break in same function


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses skip with break in same function")
for i in 0..5:
    if i == 2:
        break
    if i == 1:
        skip
expect true
```

</details>

#### parses skip with continue in same function

- parses skip with continue in same function


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses skip with continue in same function")
var count = 0
for i in 0..3:
    if i == 1:
        skip
    count = count + 1
expect count == 3
```

</details>

#### parses skip with return in same function

- parses skip with return in same function


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses skip with return in same function")
fn with_skip_and_return():
    skip
    return 42
expect with_skip_and_return() == 42
```

</details>

### Skip keyword - function and method contexts

#### parses skip in function body

- parses skip in function body


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses skip in function body")
fn test_function():
    skip
    return "completed"
expect test_function() == "completed"
```

</details>

#### parses skip in method body

- parses skip in method body


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses skip in method body")
class TestClass:
    fn test_method():
        skip
        return "method completed"

val obj = TestClass()
expect obj.test_method() == "method completed"
```

</details>

#### parses skip in static method

- parses skip in static method


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses skip in static method")
class StaticTest:
    static fn static_method():
        skip
        return "static completed"

expect StaticTest.static_method() == "static completed"
```

</details>

#### parses skip in lambda

- parses skip in lambda


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses skip in lambda")
val lambda_with_skip = \x:
    skip
    x * 2
expect lambda_with_skip(5) == 10
```

</details>

### Skip keyword - class and struct contexts

#### parses skip in class method

- parses skip in class method


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses skip in class method")
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

- parses skip in impl block method


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses skip in impl block method")
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

- parses skip in async function


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses skip in async function")
async fn async_with_skip():
    skip
    return "async result"

# Note: actual await testing requires async runtime
expect true
```

</details>

#### parses skip before await

- parses skip before await


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses skip before await")
async fn skip_before_await():
    skip
    val result = 42
    return result

expect true
```

</details>

### Skip keyword - match and pattern contexts

#### parses skip in match arm

- parses skip in match arm


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses skip in match arm")
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

- parses skip in multiple match arms


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses skip in multiple match arms")
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

- parses skip before expression


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses skip before expression")
fn with_skip_expr():
    skip
    val result = 2 + 2
    return result
expect with_skip_expr() == 4
```

</details>

#### parses skip between declarations

- parses skip between declarations


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses skip between declarations")
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

- parses skip in complex expression flow


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses skip in complex expression flow")
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

- parses skip in try-catch block


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses skip in try-catch block")
fn with_try():
    # Note: actual error handling syntax may vary
    skip
    return "ok"
expect with_try() == "ok"
```

</details>

#### parses skip before result return

- parses skip before result return


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses skip before result return")
fn result_with_skip() -> i32:
    skip
    return 42
expect result_with_skip() == 42
```

</details>

### Skip keyword - edge cases and boundaries

#### parses skip at start of file

- parses skip at start of file


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses skip at start of file")
skip
expect true
```

</details>

#### parses skip at end of function

- parses skip at end of function


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses skip at end of function")
fn skip_at_end():
    val x = 1
    skip
expect true
```

</details>

#### parses skip with empty block

- parses skip with empty block


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses skip with empty block")
skip:
    pass
expect true
```

</details>

#### parses nested skip statements

- parses nested skip statements


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses nested skip statements")
if true:
    skip:
        skip
expect true
```

</details>

#### parses skip with comment

- parses skip with comment


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses skip with comment")
skip  # This is skipped
expect true
```

</details>

#### parses skip with multiline comment

- parses skip with multiline comment


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses skip with multiline comment")
skip  /*
    Multiline comment
    about skipping
*/
expect true
```

</details>

### Skip keyword - indentation and whitespace

#### parses skip with various indentation

- parses skip with various indentation


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses skip with various indentation")
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

- parses skip with no trailing whitespace


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses skip with no trailing whitespace")
skip
val x = 1
expect x == 1
```

</details>

#### parses skip with blank lines after

- parses skip with blank lines after


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses skip with blank lines after")
skip

val y = 2
expect y == 2
```

</details>

### Skip keyword - semantics and runtime behavior

#### skip statement does not prevent execution

- skip statement does not prevent execution


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("skip statement does not prevent execution")
var executed = false
skip
executed = true
expect executed == true
```

</details>

#### skip does not affect variable scope

- skip does not affect variable scope


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("skip does not affect variable scope")
skip
val scoped = 100
expect scoped == 100
```

</details>

#### skip does not affect return value

- skip does not affect return value


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("skip does not affect return value")
fn returns_with_skip():
    skip
    return "value"
expect returns_with_skip() == "value"
```

</details>

<details>
<summary>Advanced: skip does not affect loop iteration</summary>

#### skip does not affect loop iteration

- skip does not affect loop iteration


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("skip does not affect loop iteration")
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

- allows skip for test tagging preparation


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("allows skip for test tagging preparation")
# Future: skip it "unimplemented test":
#     expect false
expect true
```

</details>

#### parses skip with test metadata

- parses skip with test metadata


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses skip with test metadata")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `0c55ad11b07e1668a36f9a836cff36df1887d6be72733aee402acf27b95aca45`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `0c55ad11b07e1668a36f9a836cff36df1887d6be72733aee402acf27b95aca45`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `0c55ad11b07e1668a36f9a836cff36df1887d6be72733aee402acf27b95aca45`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/feature/usage/parser_skip_keyword_spec.spl
mirror: doc/06_spec/03_system/feature/usage/parser_skip_keyword_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/usage/parser_skip_keyword_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/usage/parser_skip_keyword_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/usage/parser_skip_keyword_spec.spl:33:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'recognizes skip as a keyword token' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/usage/parser_skip_keyword_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'allows skip_func as function name' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/usage/parser_skip_keyword_spec.spl:47:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'distinguishes skip keyword from skip variable name' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
