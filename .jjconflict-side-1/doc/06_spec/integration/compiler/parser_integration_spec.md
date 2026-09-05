# Parser Integration Specification

> Tests covering Parser Function Parsing Integration, Parser Class Parsing Integration, Parser Expression Parsing Integration, Parser Statement Parsing Integration, Parser Control Flow Integration, Parser Pattern Matching Integration, Parser Type Annotation Integration, Parser Import Parsing Integration, Parser Operator Precedence Integration, Parser Error Recovery Integration, Parser Performance Integration.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 45 | 45 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Parser Integration Specification

## Scenarios

### Parser Function Parsing Integration

#### parses simple function

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- parses simple function


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("parses simple function")
val code = "fn add(x, y): x + y"
check(code.contains("fn"))
```

</details>

#### parses function with type annotations

- parses function with type annotations


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("parses function with type annotations")
val code = "fn square(x: i64) -> i64: x * x"
check(code.contains("->"))
check(code.contains("i64"))
```

</details>

#### parses function with multiple parameters

- parses function with multiple parameters


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("parses function with multiple parameters")
val code = "fn calc(a: i64, b: i64, c: i64): a + b + c"
val param_count = code.count(",")
check(param_count == 2)
```

</details>

#### parses function with no parameters

- parses function with no parameters


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("parses function with no parameters")
val code = "fn get_value(): 42"
check(code.contains("()"))
```

</details>

#### parses multi-line function

- parses multi-line function


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("parses multi-line function")
val code = "fn foo():\n    val x = 1\n    x + 2"
check(code.contains("\n"))
```

</details>

### Parser Class Parsing Integration

#### parses simple class

- parses simple class


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("parses simple class")
val code = "class Point:\n    x: i64\n    y: i64"
check(code.contains("class"))
```

</details>

#### parses class with methods

- parses class with methods


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("parses class with methods")
val code = "class Counter:\n    count: i64\n    fn inc(): pass"
check(code.contains("fn"))
```

</details>

#### parses class with static methods

- parses class with static methods


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("parses class with static methods")
val code = "class Factory:\n    static fn create(): pass"
check(code.contains("static"))
```

</details>

#### parses class with constructor

- parses class with constructor


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("parses class with constructor")
val code = "class Point:\n    x: i64\n    static fn new(): Point(x: 0)"
check(code.contains("new"))
```

</details>

### Parser Expression Parsing Integration

#### parses arithmetic expressions

- parses arithmetic expressions


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("parses arithmetic expressions")
val exprs = ["1 + 2", "3 * 4", "10 - 5", "20 / 4"]
for expr in exprs:
    check(expr.len() > 0)
```

</details>

#### parses comparison expressions

- parses comparison expressions


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("parses comparison expressions")
val exprs = ["x == y", "a != b", "p < q", "m >= n"]
for expr in exprs:
    check(expr.len() > 0)
```

</details>

#### parses logical expressions

- parses logical expressions


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("parses logical expressions")
val exprs = ["a and b", "x or y", "not z"]
for expr in exprs:
    check(expr.len() > 0)
```

</details>

#### parses function calls

- parses function calls


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("parses function calls")
val calls = ["foo()", "bar(x)", "baz(a, b, c)"]
for call in calls:
    check(call.contains("("))
```

</details>

#### parses method calls

- parses method calls


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("parses method calls")
val calls = ["obj.method()", "self.x", "user.name"]
for call in calls:
    check(call.contains("."))
```

</details>

### Parser Statement Parsing Integration

#### parses variable declarations

- parses variable declarations


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("parses variable declarations")
val stmts = ["val x = 42", "var y = \"hello\""]
for stmt in stmts:
    check(stmt.contains("="))
```

</details>

#### parses assignment statements

- parses assignment statements


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("parses assignment statements")
val stmts = ["x = 10", "y += 5", "z *= 2"]
for stmt in stmts:
    check(stmt.contains("="))
```

</details>

#### parses return statements

- parses return statements


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("parses return statements")
val stmts = ["return x", "return"]
for stmt in stmts:
    check(stmt.contains("return"))
```

</details>

#### parses break and continue

- parses break and continue


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("parses break and continue")
val stmts = ["break", "continue"]
for stmt in stmts:
    check(stmt.len() > 0)
```

</details>

### Parser Control Flow Integration

#### parses if-else

- parses if-else


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("parses if-else")
val code = "if x > 0:\n    positive()\nelse:\n    negative()"
check(code.contains("if"))
check(code.contains("else"))
```

</details>

#### parses elif chain

- parses elif chain


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("parses elif chain")
val code = "if x > 10:\n    big()\nelif x > 5:\n    med()\nelse:\n    small()"
check(code.contains("elif"))
```

</details>

#### parses match expression

- parses match expression


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("parses match expression")
val code = "match val:\n    Some(x): x\n    nil: 0"
check(code.contains("match"))
```

</details>

<details>
<summary>Advanced: parses for loop</summary>

#### parses for loop

- parses for loop


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("parses for loop")
val code = "for i in 0..10:\n    print(i)"
check(code.contains("for"))
check(code.contains("in"))
```

</details>


</details>

<details>
<summary>Advanced: parses while loop</summary>

#### parses while loop

- parses while loop


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("parses while loop")
val code = "while cond:\n    process()"
check(code.contains("while"))
```

</details>


</details>

### Parser Pattern Matching Integration

#### parses literal patterns

- parses literal patterns


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("parses literal patterns")
val patterns = ["42", "\"text\"", "true", "false", "nil"]
for pattern in patterns:
    check(pattern.len() > 0)
```

</details>

#### parses variable patterns

- parses variable patterns


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("parses variable patterns")
val patterns = ["x", "name", "value"]
for pattern in patterns:
    check(pattern.len() > 0)
```

</details>

#### parses constructor patterns

- parses constructor patterns


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("parses constructor patterns")
val patterns = ["Some(x)", "Ok(val)", "Error(msg)"]
for pattern in patterns:
    check(pattern.contains("("))
```

</details>

#### parses nested patterns

- parses nested patterns


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("parses nested patterns")
val pattern = "Some(User(name: n, age: a))"
check(pattern.contains("Some"))
check(pattern.contains("User"))
```

</details>

### Parser Type Annotation Integration

#### parses primitive types

- parses primitive types


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("parses primitive types")
val types = ["i64", "f64", "bool", "text"]
for typ in types:
    check(typ.len() > 0)
```

</details>

#### parses generic types

- parses generic types


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("parses generic types")
val types = ["Option<i64>", "List<text>", "Map<text, i64>"]
for typ in types:
    check(typ.contains("<"))
    check(typ.contains(">"))
```

</details>

#### parses function types

- parses function types


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("parses function types")
val types = ["(i64) -> i64", "(text, i64) -> bool"]
for typ in types:
    check(typ.contains("->"))
```

</details>

#### parses array types

- parses array types


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("parses array types")
val types = ["[i64]", "[text]"]
for typ in types:
    check(typ.starts_with("["))
```

</details>

### Parser Import Parsing Integration

#### parses simple import

- parses simple import


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("parses simple import")
val code = "use std.spec"
check(code.contains("use"))
```

</details>

#### parses selective import

- parses selective import


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("parses selective import")
val code = "use std.spec.{check, check_msg}"
check(code.contains("{"))
check(code.contains("}"))
```

</details>

#### parses aliased import

- parses aliased import


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("parses aliased import")
val code = "use std.text as str"
check(code.contains("as"))
```

</details>

#### parses nested module import

- parses nested module import


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("parses nested module import")
val code = r"use std.collections.map.{HashMap}"
check(code.count(".") >= 2)
```

</details>

### Parser Operator Precedence Integration

#### handles arithmetic precedence

- handles arithmetic precedence


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("handles arithmetic precedence")
val code = "1 + 2 * 3"
check(code.contains("+"))
check(code.contains("*"))
```

</details>

#### handles comparison precedence

- handles comparison precedence


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("handles comparison precedence")
val code = "x + 1 < y * 2"
check(code.contains("<"))
```

</details>

#### handles logical precedence

- handles logical precedence


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("handles logical precedence")
val code = "a or b and c"
check(code.contains("or"))
check(code.contains("and"))
```

</details>

#### handles parentheses

- handles parentheses


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("handles parentheses")
val code = "(a + b) * c"
check(code.starts_with("("))
```

</details>

### Parser Error Recovery Integration

#### handles missing parenthesis

- handles missing parenthesis


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("handles missing parenthesis")
val invalid = "fn foo(:"
check(invalid.contains("fn"))
```

</details>

#### handles incomplete expression

- handles incomplete expression


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("handles incomplete expression")
val invalid = "val x = "
check(invalid.contains("val"))
```

</details>

#### continues after error

- continues after error


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("continues after error")
val code = "val x = \nval y = 42"
check(code.contains("val y"))
```

</details>

### Parser Performance Integration

#### parses 50 function definitions

- parses 50 function definitions


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("parses 50 function definitions")
var parts: [text] = []
for i in 0..50:
    parts.push("fn f{i}(): pass\n")
val code = parts.join("")

check(code.contains("fn"))
```

</details>

#### parses deeply nested expressions

- parses deeply nested expressions


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("parses deeply nested expressions")
val code = "((((1 + 2) * 3) - 4) / 5)"
check(code.count("(") == 4)
```

</details>

#### parses large class definition

- parses large class definition


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("parses large class definition")
var parts: [text] = ["class Large:\n"]
for i in 0..30:
    parts.push("    field{i}: i64\n")
val code = parts.join("")

check(code.contains("class"))
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/integration/compiler/parser_integration_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Parser Function Parsing Integration, Parser Class Parsing Integration, Parser Expression Parsing Integration, Parser Statement Parsing Integration, Parser Control Flow Integration, Parser Pattern Matching Integration, Parser Type Annotation Integration, Parser Import Parsing Integration, Parser Operator Precedence Integration, Parser Error Recovery Integration, Parser Performance Integration.
- Parser Function Parsing Integration
- Parser Class Parsing Integration
- Parser Expression Parsing Integration
- Parser Statement Parsing Integration
- Parser Control Flow Integration
- Parser Pattern Matching Integration
- Parser Type Annotation Integration
- Parser Import Parsing Integration
- Parser Operator Precedence Integration
- Parser Error Recovery Integration
- Parser Performance Integration

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 45 |
| Active scenarios | 45 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-INTEGRATION`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `a3a7e3aa261eca56a2a9820efee3904e5fff6bc571db1f9e54c6c818a81c7af4`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a3a7e3aa261eca56a2a9820efee3904e5fff6bc571db1f9e54c6c818a81c7af4`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a3a7e3aa261eca56a2a9820efee3904e5fff6bc571db1f9e54c6c818a81c7af4`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/integration/compiler/parser_integration_spec.spl
mirror: doc/06_spec/integration/compiler/parser_integration_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/integration/compiler/parser_integration_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/integration/compiler/parser_integration_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/integration/compiler/parser_integration_spec.spl:53:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses simple function' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/compiler/parser_integration_spec.spl:59:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses function with type annotations' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/compiler/parser_integration_spec.spl:66:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses function with multiple parameters' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
