# Parser Edge Cases for Operators, Keywords, and Type Syntax

> The Simple parser must handle several non-trivial syntactic forms that are easy to mis-parse: the matrix-multiplication operator `@`, the keyword-style bitwise `xor` operator, and bracket-based array type annotations `[T]`. This spec exercises each form in isolation and in combination, verifying correct tokenisation, operator precedence, and type annotation parsing. A `super` keyword test is planned but commented out pending interpreter support for inheritance dispatch.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Parser Edge Cases for Operators, Keywords, and Type Syntax

The Simple parser must handle several non-trivial syntactic forms that are easy to mis-parse: the matrix-multiplication operator `@`, the keyword-style bitwise `xor` operator, and bracket-based array type annotations `[T]`. This spec exercises each form in isolation and in combination, verifying correct tokenisation, operator precedence, and type annotation parsing. A `super` keyword test is planned but commented out pending interpreter support for inheritance dispatch.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #PARSER-015 |
| Category | Syntax |
| Status | In Progress |
| Source | `test/feature/usage/parser_edge_cases_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

The Simple parser must handle several non-trivial syntactic forms that are easy to
mis-parse: the matrix-multiplication operator `@`, the keyword-style bitwise `xor`
operator, and bracket-based array type annotations `[T]`. This spec exercises each
form in isolation and in combination, verifying correct tokenisation, operator
precedence, and type annotation parsing. A `super` keyword test is planned but
commented out pending interpreter support for inheritance dispatch.

## Syntax

```simple
# Matrix multiplication operator (@)
use std.spec.step

val result = 3 @ 4          # => 12

# Bitwise XOR keyword operator
val bits = 5 xor 3          # => 6

# Array type annotations with square brackets
fn takes_array(items: [i64]) -> [i64]:
return items

# Combined precedence
val c = (a xor b) @ 2       # xor first, then @
```

## Key Concepts

| Concept | Description |
|---------|-------------|
| `@` operator | Matrix multiplication infix operator parsed as a binary expression |
| `xor` keyword operator | Bitwise XOR expressed as an alphabetic keyword, not a symbol |
| Array type syntax | `[T]` bracket notation used in parameter and return type positions |
| Operator precedence | Verifies correct evaluation order when `@` and `xor` appear together |

## Scenarios

### Parser Edge Cases

#### Matrix Multiplication Operator

#### parses @ operator in expressions

- parses @ operator in expressions


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses @ operator in expressions")
val result = 3 @ 4
expect result == 12
```

</details>

#### parses @ operator with variables

- parses @ operator with variables


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses @ operator with variables")
val a = 2
val b = 5
val result = a @ b
expect result == 10
```

</details>

#### Bitwise XOR Keyword

#### parses xor keyword in expressions

- parses xor keyword in expressions


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses xor keyword in expressions")
val result = 5 xor 3
expect result == 6
```

</details>

#### parses xor keyword with variables

- parses xor keyword with variables


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses xor keyword with variables")
val a = 12
val b = 7
val result = a xor b
expect result == 11
```

</details>

#### parses xor in complex expressions

- parses xor in complex expressions


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses xor in complex expressions")
val result = (5 xor 3) xor 1
expect result == 7
```

</details>

#### Array Type Syntax

#### parses array types with square brackets

- parses array types with square brackets


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses array types with square brackets")
fn takes_array(items: [i64]) -> [i64]:
    return items

val nums = [1, 2, 3]
val result = takes_array(nums)
expect result.length() == 3
```

</details>

#### parses array return types

- parses array return types


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses array return types")
fn make_array() -> [text]:
    return ["a", "b", "c"]

val result = make_array()
expect result[0] == "a"
```

</details>

#### Operator Precedence

#### handles @ and xor together

- handles @ and xor together


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("handles @ and xor together")
val result = (3 @ 2) xor 5
expect result == 3  # (3 @ 2) = 6, 6 xor 5 = 3
```

</details>

#### handles multiple operators

- handles multiple operators


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("handles multiple operators")
val a = 10
val b = 3
val c = (a xor b) @ 2
expect c == 18  # 10 xor 3 = 9, 9 @ 2 = 18
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
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

- Canonical SPipe generation for source `22507c1e55d46046445219e68655c0a72df831abb3fb4a280dff4382d6707e8c`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `22507c1e55d46046445219e68655c0a72df831abb3fb4a280dff4382d6707e8c`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `22507c1e55d46046445219e68655c0a72df831abb3fb4a280dff4382d6707e8c`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/feature/usage/parser_edge_cases_spec.spl
mirror: doc/06_spec/feature/usage/parser_edge_cases_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/feature/usage/parser_edge_cases_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/feature/usage/parser_edge_cases_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/feature/usage/parser_edge_cases_spec.spl:55:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses @ operator in expressions' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/usage/parser_edge_cases_spec.spl:61:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses @ operator with variables' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/usage/parser_edge_cases_spec.spl:70:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses xor keyword in expressions' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
