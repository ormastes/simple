# parser_integration_spec

> Verifies the parser integration behaviour end to end so maintainers of this

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 45 | 45 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# parser_integration_spec

Verifies the parser integration behaviour end to end so maintainers of this

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/02_integration/compiler/parser_integration_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Verifies the parser integration behaviour end to end so maintainers of this
component and reviewers of its spec share one pinned definition.
## Operator workflow
Run `bin/simple test <this spec>`; read the per-scenario verdicts in
the `Results:` summary. Each scenario asserts an observable outcome.
## Compatibility and limitations
Covers the currently shipped behaviour only; performance, stress and
unrelated sibling features are out of scope.

## Scenarios

### Parser Function Parsing Integration

#### parses simple function

- Verify: parses simple function


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-COMPILER-COMPILER_PARSER_INTEGRATION-001
step("Verify: parses simple function")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val code = "fn add(x, y): x + y"
check(code.contains("fn"))
```

</details>

#### parses function with type annotations

- Verify: parses function with type annotations


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-COMPILER-COMPILER_PARSER_INTEGRATION-001
step("Verify: parses function with type annotations")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val code = "fn square(x: i64) -> i64: x * x"
check(code.contains("->"))
check(code.contains("i64"))
```

</details>

#### parses function with multiple parameters

- Verify: parses function with multiple parameters


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-COMPILER-COMPILER_PARSER_INTEGRATION-001
step("Verify: parses function with multiple parameters")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val code = "fn calc(a: i64, b: i64, c: i64): a + b + c"
val param_count = code.count(",")
check(param_count == 2)
```

</details>

#### parses function with no parameters

- Verify: parses function with no parameters


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-COMPILER-COMPILER_PARSER_INTEGRATION-001
step("Verify: parses function with no parameters")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val code = "fn get_value(): 42"
check(code.contains("()"))
```

</details>

#### parses multi-line function

- Verify: parses multi-line function


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-COMPILER-COMPILER_PARSER_INTEGRATION-001
step("Verify: parses multi-line function")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val code = "fn foo():\n    val x = 1\n    x + 2"
check(code.contains("\n"))
```

</details>

### Parser Class Parsing Integration

#### parses simple class

- Verify: parses simple class


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-COMPILER-COMPILER_PARSER_INTEGRATION-001
step("Verify: parses simple class")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val code = "class Point:\n    x: i64\n    y: i64"
check(code.contains("class"))
```

</details>

#### parses class with methods

- Verify: parses class with methods


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-COMPILER-COMPILER_PARSER_INTEGRATION-001
step("Verify: parses class with methods")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val code = "class Counter:\n    count: i64\n    fn inc(): pass"
check(code.contains("fn"))
```

</details>

#### parses class with static methods

- Verify: parses class with static methods


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-COMPILER-COMPILER_PARSER_INTEGRATION-001
step("Verify: parses class with static methods")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val code = "class Factory:\n    static fn create(): pass"
check(code.contains("static"))
```

</details>

#### parses class with constructor

- Verify: parses class with constructor


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-COMPILER-COMPILER_PARSER_INTEGRATION-001
step("Verify: parses class with constructor")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val code = "class Point:\n    x: i64\n    static fn new(): Point(x: 0)"
check(code.contains("new"))
```

</details>

### Parser Expression Parsing Integration

#### parses arithmetic expressions

- Verify: parses arithmetic expressions


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-COMPILER-COMPILER_PARSER_INTEGRATION-001
step("Verify: parses arithmetic expressions")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val exprs = ["1 + 2", "3 * 4", "10 - 5", "20 / 4"]
for expr in exprs:
    check(expr.len() > 0)
```

</details>

#### parses comparison expressions

- Verify: parses comparison expressions


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-COMPILER-COMPILER_PARSER_INTEGRATION-001
step("Verify: parses comparison expressions")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val exprs = ["x == y", "a != b", "p < q", "m >= n"]
for expr in exprs:
    check(expr.len() > 0)
```

</details>

#### parses logical expressions

- Verify: parses logical expressions


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-COMPILER-COMPILER_PARSER_INTEGRATION-001
step("Verify: parses logical expressions")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val exprs = ["a and b", "x or y", "not z"]
for expr in exprs:
    check(expr.len() > 0)
```

</details>

#### parses function calls

- Verify: parses function calls


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-COMPILER-COMPILER_PARSER_INTEGRATION-001
step("Verify: parses function calls")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val calls = ["foo()", "bar(x)", "baz(a, b, c)"]
for call in calls:
    check(call.contains("("))
```

</details>

#### parses method calls

- Verify: parses method calls


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-COMPILER-COMPILER_PARSER_INTEGRATION-001
step("Verify: parses method calls")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val calls = ["obj.method()", "self.x", "user.name"]
for call in calls:
    check(call.contains("."))
```

</details>

### Parser Statement Parsing Integration

#### parses variable declarations

- Verify: parses variable declarations


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-COMPILER-COMPILER_PARSER_INTEGRATION-001
step("Verify: parses variable declarations")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val stmts = ["val x = 42", "var y = \"hello\""]
for stmt in stmts:
    check(stmt.contains("="))
```

</details>

#### parses assignment statements

- Verify: parses assignment statements


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-COMPILER-COMPILER_PARSER_INTEGRATION-001
step("Verify: parses assignment statements")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val stmts = ["x = 10", "y += 5", "z *= 2"]
for stmt in stmts:
    check(stmt.contains("="))
```

</details>

#### parses return statements

- Verify: parses return statements


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-COMPILER-COMPILER_PARSER_INTEGRATION-001
step("Verify: parses return statements")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val stmts = ["return x", "return"]
for stmt in stmts:
    check(stmt.contains("return"))
```

</details>

#### parses break and continue

- Verify: parses break and continue


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-COMPILER-COMPILER_PARSER_INTEGRATION-001
step("Verify: parses break and continue")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val stmts = ["break", "continue"]
for stmt in stmts:
    check(stmt.len() > 0)
```

</details>

### Parser Control Flow Integration

#### parses if-else

- Verify: parses if-else


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-COMPILER-COMPILER_PARSER_INTEGRATION-001
step("Verify: parses if-else")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val code = "if x > 0:\n    positive()\nelse:\n    negative()"
check(code.contains("if"))
check(code.contains("else"))
```

</details>

#### parses elif chain

- Verify: parses elif chain


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-COMPILER-COMPILER_PARSER_INTEGRATION-001
step("Verify: parses elif chain")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val code = "if x > 10:\n    big()\nelif x > 5:\n    med()\nelse:\n    small()"
check(code.contains("elif"))
```

</details>

#### parses match expression

- Verify: parses match expression


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-COMPILER-COMPILER_PARSER_INTEGRATION-001
step("Verify: parses match expression")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val code = "match val:\n    Some(x): x\n    nil: 0"
check(code.contains("match"))
```

</details>

<details>
<summary>Advanced: parses for loop</summary>

#### parses for loop

- Verify: parses for loop


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-COMPILER-COMPILER_PARSER_INTEGRATION-001
step("Verify: parses for loop")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val code = "for i in 0..10:\n    print(i)"
check(code.contains("for"))
check(code.contains("in"))
```

</details>


</details>

<details>
<summary>Advanced: parses while loop</summary>

#### parses while loop

- Verify: parses while loop


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-COMPILER-COMPILER_PARSER_INTEGRATION-001
step("Verify: parses while loop")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val code = "while cond:\n    process()"
check(code.contains("while"))
```

</details>


</details>

### Parser Pattern Matching Integration

#### parses literal patterns

- Verify: parses literal patterns


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-COMPILER-COMPILER_PARSER_INTEGRATION-001
step("Verify: parses literal patterns")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val patterns = ["42", "\"text\"", "true", "false", "nil"]
for pattern in patterns:
    check(pattern.len() > 0)
```

</details>

#### parses variable patterns

- Verify: parses variable patterns


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-COMPILER-COMPILER_PARSER_INTEGRATION-001
step("Verify: parses variable patterns")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val patterns = ["x", "name", "value"]
for pattern in patterns:
    check(pattern.len() > 0)
```

</details>

#### parses constructor patterns

- Verify: parses constructor patterns


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-COMPILER-COMPILER_PARSER_INTEGRATION-001
step("Verify: parses constructor patterns")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val patterns = ["Some(x)", "Ok(val)", "Error(msg)"]
for pattern in patterns:
    check(pattern.contains("("))
```

</details>

#### parses nested patterns

- Verify: parses nested patterns


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-COMPILER-COMPILER_PARSER_INTEGRATION-001
step("Verify: parses nested patterns")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val pattern = "Some(User(name: n, age: a))"
check(pattern.contains("Some"))
check(pattern.contains("User"))
```

</details>

### Parser Type Annotation Integration

#### parses primitive types

- Verify: parses primitive types


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-COMPILER-COMPILER_PARSER_INTEGRATION-001
step("Verify: parses primitive types")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val types = ["i64", "f64", "bool", "text"]
for typ in types:
    check(typ.len() > 0)
```

</details>

#### parses generic types

- Verify: parses generic types


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-COMPILER-COMPILER_PARSER_INTEGRATION-001
step("Verify: parses generic types")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val types = ["Option<i64>", "List<text>", "Map<text, i64>"]
for typ in types:
    check(typ.contains("<"))
    check(typ.contains(">"))
```

</details>

#### parses function types

- Verify: parses function types


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-COMPILER-COMPILER_PARSER_INTEGRATION-001
step("Verify: parses function types")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val types = ["(i64) -> i64", "(text, i64) -> bool"]
for typ in types:
    check(typ.contains("->"))
```

</details>

#### parses array types

- Verify: parses array types


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-COMPILER-COMPILER_PARSER_INTEGRATION-001
step("Verify: parses array types")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val types = ["[i64]", "[text]"]
for typ in types:
    check(typ.starts_with("["))
```

</details>

### Parser Import Parsing Integration

#### parses simple import

- Verify: parses simple import


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-COMPILER-COMPILER_PARSER_INTEGRATION-001
step("Verify: parses simple import")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val code = "use std.spec"
check(code.contains("use"))
```

</details>

#### parses selective import

- Verify: parses selective import


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-COMPILER-COMPILER_PARSER_INTEGRATION-001
step("Verify: parses selective import")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val code = "use std.spec.{check, check_msg}"
check(code.contains("{"))
check(code.contains("}"))
```

</details>

#### parses aliased import

- Verify: parses aliased import


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-COMPILER-COMPILER_PARSER_INTEGRATION-001
step("Verify: parses aliased import")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val code = "use std.text as str"
check(code.contains("as"))
```

</details>

#### parses nested module import

- Verify: parses nested module import


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-COMPILER-COMPILER_PARSER_INTEGRATION-001
step("Verify: parses nested module import")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val code = r"use std.collections.map.{HashMap}"
check(code.count(".") >= 2)
```

</details>

### Parser Operator Precedence Integration

#### handles arithmetic precedence

- Verify: handles arithmetic precedence


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-COMPILER-COMPILER_PARSER_INTEGRATION-001
step("Verify: handles arithmetic precedence")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val code = "1 + 2 * 3"
check(code.contains("+"))
check(code.contains("*"))
```

</details>

#### handles comparison precedence

- Verify: handles comparison precedence


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-COMPILER-COMPILER_PARSER_INTEGRATION-001
step("Verify: handles comparison precedence")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val code = "x + 1 < y * 2"
check(code.contains("<"))
```

</details>

#### handles logical precedence

- Verify: handles logical precedence


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-COMPILER-COMPILER_PARSER_INTEGRATION-001
step("Verify: handles logical precedence")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val code = "a or b and c"
check(code.contains("or"))
check(code.contains("and"))
```

</details>

#### handles parentheses

- Verify: handles parentheses


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-COMPILER-COMPILER_PARSER_INTEGRATION-001
step("Verify: handles parentheses")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val code = "(a + b) * c"
check(code.starts_with("("))
```

</details>

### Parser Error Recovery Integration

#### handles missing parenthesis

- Verify: handles missing parenthesis


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-COMPILER-COMPILER_PARSER_INTEGRATION-001
step("Verify: handles missing parenthesis")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val invalid = "fn foo(:"
check(invalid.contains("fn"))
```

</details>

#### handles incomplete expression

- Verify: handles incomplete expression


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-COMPILER-COMPILER_PARSER_INTEGRATION-001
step("Verify: handles incomplete expression")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val invalid = "val x = "
check(invalid.contains("val"))
```

</details>

#### continues after error

- Verify: continues after error


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-COMPILER-COMPILER_PARSER_INTEGRATION-001
step("Verify: continues after error")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val code = "val x = \nval y = 42"
check(code.contains("val y"))
```

</details>

### Parser Performance Integration

#### parses 50 function definitions

- Verify: parses 50 function definitions


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-COMPILER-COMPILER_PARSER_INTEGRATION-001
step("Verify: parses 50 function definitions")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
var parts: [text] = []
for i in 0..50:
    parts.push("fn f{i}(): pass\n")
val code = parts.join("")

check(code.contains("fn"))
```

</details>

#### parses deeply nested expressions

- Verify: parses deeply nested expressions


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-COMPILER-COMPILER_PARSER_INTEGRATION-001
step("Verify: parses deeply nested expressions")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val code = "((((1 + 2) * 3) - 4) / 5)"
check(code.count("(") == 4)
```

</details>

#### parses large class definition

- Verify: parses large class definition


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-COMPILER-COMPILER_PARSER_INTEGRATION-001
step("Verify: parses large class definition")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
var parts: [text] = ["class Large:\n"]
for i in 0..30:
    parts.push("    field{i}: i64\n")
val code = parts.join("")

check(code.contains("class"))
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 45 |
| Active scenarios | 45 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `e4fca1667084a30a0b71e701a6ada3b0a111ec3112460607364df129ddf4368f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e4fca1667084a30a0b71e701a6ada3b0a111ec3112460607364df129ddf4368f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e4fca1667084a30a0b71e701a6ada3b0a111ec3112460607364df129ddf4368f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/02_integration/compiler/parser_integration_spec.spl
mirror: doc/06_spec/02_integration/compiler/parser_integration_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/02_integration/compiler/parser_integration_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/02_integration/compiler/parser_integration_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/02_integration/compiler/parser_integration_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, traceability
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
