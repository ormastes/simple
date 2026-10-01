# Grammar Simple Specification

> Tests covering SimpleGrammar - Core Modern Syntax, SimpleGrammar - Lambda Syntax, SimpleGrammar - Generic Types, SimpleGrammar - Module System, SimpleGrammar - Advanced Types, SimpleGrammar - Operators, SimpleGrammar - Literals, SimpleGrammar - Error Recovery.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 16 | 16 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Grammar Simple Specification

## Scenarios

### SimpleGrammar - Core Modern Syntax

#### parses val declarations

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- parses val declarations


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses val declarations")
val code = "val x = 42"
val ast = parse_code(code)
check(ast.is_ok())
```

</details>

#### parses var declarations

- parses var declarations


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses var declarations")
val code = "var count = 0"
val ast = parse_code(code)
check(ast.is_ok())
```

</details>

#### parses const declarations

- parses const declarations


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses const declarations")
val code = "const MAX_SIZE = 1000"
val ast = parse_code(code)
check(ast.is_ok())
```

</details>

### SimpleGrammar - Lambda Syntax

#### parses fn lambda syntax

- parses fn lambda syntax


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses fn lambda syntax")
val code = "val add = fn(x, y): x + y"
val ast = parse_code(code)
check(ast.is_ok())
```

</details>

#### parses backslash lambda

- parses backslash lambda


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses backslash lambda")
val code = "val double = \\x: x * 2"
val ast = parse_code(code)
check(ast.is_ok())
```

</details>

### SimpleGrammar - Generic Types

#### parses generic type

- parses generic type


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses generic type")
val code = "val items: List<Int> = []"
val ast = parse_code(code)
check(ast.is_ok())
```

</details>

#### parses nested generics

- parses nested generics


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses nested generics")
val code = "val nested: List<Option<Int>> = []"
val ast = parse_code(code)
check(ast.is_ok())
```

</details>

### SimpleGrammar - Module System

#### parses use statement with glob

- parses use statement with glob


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses use statement with glob")
val code = "use std.collections"
val ast = parse_code(code)
check(ast.is_ok())
```

</details>

#### parses use statement with braces

- parses use statement with braces


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses use statement with braces")
val code = "use std.spec.{describe, it}"
val ast = parse_code(code)
check(ast.is_ok())
```

</details>

### SimpleGrammar - Advanced Types

#### parses optional type

- parses optional type


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses optional type")
val code = "val maybe: Int? = None"
val ast = parse_code(code)
check(ast.is_ok())
```

</details>

#### parses result type

- parses result type


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses result type")
val code = "val result: Int! = Ok(42)"
val ast = parse_code(code)
check(ast.is_ok())
```

</details>

### SimpleGrammar - Operators

#### parses compound assignment

- parses compound assignment


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses compound assignment")
val code = "x += 5"
val ast = parse_code(code)
check(ast.is_ok())
```

</details>

#### parses range operators

- parses range operators


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses range operators")
val code = "val range1 = 0..10"
val ast = parse_code(code)
check(ast.is_ok())
```

</details>

### SimpleGrammar - Literals

#### parses typed integer

- parses typed integer


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses typed integer")
val code = "val a = 42i32"
val ast = parse_code(code)
check(ast.is_ok())
```

</details>

#### parses symbols

- parses symbols


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses symbols")
val code = "val status = :success"
val ast = parse_code(code)
check(ast.is_ok())
```

</details>

### SimpleGrammar - Error Recovery

#### recovers from syntax errors

- recovers from syntax errors


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("recovers from syntax errors")
val code = "fn test()"
val ast = parse_code(code)
check(ast.is_ok())
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/unit/compiler/parser/grammar_simple_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering SimpleGrammar - Core Modern Syntax, SimpleGrammar - Lambda Syntax, SimpleGrammar - Generic Types, SimpleGrammar - Module System, SimpleGrammar - Advanced Types, SimpleGrammar - Operators, SimpleGrammar - Literals, SimpleGrammar - Error Recovery.
- SimpleGrammar - Core Modern Syntax
- SimpleGrammar - Lambda Syntax
- SimpleGrammar - Generic Types
- SimpleGrammar - Module System
- SimpleGrammar - Advanced Types
- SimpleGrammar - Operators
- SimpleGrammar - Literals
- SimpleGrammar - Error Recovery

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 16 |
| Active scenarios | 16 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `055308f56ba16a74cc4898221899f3dacbcb52335d58c53ab6abe9c2462bec73`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `055308f56ba16a74cc4898221899f3dacbcb52335d58c53ab6abe9c2462bec73`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `055308f56ba16a74cc4898221899f3dacbcb52335d58c53ab6abe9c2462bec73`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/compiler/parser/grammar_simple_spec.spl
mirror: doc/06_spec/unit/compiler/parser/grammar_simple_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/compiler/parser/grammar_simple_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/compiler/parser/grammar_simple_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/compiler/parser/grammar_simple_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses val declarations' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/parser/grammar_simple_spec.spl:47:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses var declarations' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/parser/grammar_simple_spec.spl:54:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses const declarations' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
