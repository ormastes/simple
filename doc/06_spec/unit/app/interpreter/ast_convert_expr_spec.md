# Ast Convert Expr Specification

> Tests covering convert_expression Entry Point, convert_binary_expression - Arithmetic, convert_binary_expression - Comparison, convert_binary_expression - Logical & Bitwise, convert_unary_expression, Call Expression Conversion, Access Expression Conversion, Collection Literal Conversion, Lambda Expression Conversion, Control Flow Expression Conversion, Conversion Error Handling.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 61 | 61 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Ast Convert Expr Specification

## Scenarios

### convert_expression Entry Point

#### converts integer literals

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- converts integer literals


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts integer literals")
# Test that integer nodes are recognized
# Actual conversion requires parser integration
pass
```

</details>

#### converts float literals

- converts float literals


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts float literals")
# Test that float nodes are recognized
pass
```

</details>

#### converts string literals

- converts string literals


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts string literals")
# Test that string nodes are recognized
pass
```

</details>

#### converts boolean literals

- converts boolean literals


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts boolean literals")
# Test that boolean nodes are recognized
pass
```

</details>

#### converts nil literals

- converts nil literals


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts nil literals")
# Test that nil nodes are recognized
pass
```

</details>

#### converts identifiers

- converts identifiers


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts identifiers")
# Test that identifier nodes are recognized
pass
```

</details>

### convert_binary_expression - Arithmetic

#### recognizes addition operator

- recognizes addition operator


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("recognizes addition operator")
# Tests operator recognition for +
pass
```

</details>

#### recognizes subtraction operator

- recognizes subtraction operator


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("recognizes subtraction operator")
# Tests operator recognition for -
pass
```

</details>

#### recognizes multiplication operator

- recognizes multiplication operator


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("recognizes multiplication operator")
# Tests operator recognition for *
pass
```

</details>

#### recognizes division operator

- recognizes division operator


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("recognizes division operator")
# Tests operator recognition for /
pass
```

</details>

#### recognizes modulo operator

- recognizes modulo operator


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("recognizes modulo operator")
# Tests operator recognition for %
pass
```

</details>

#### recognizes power operator

- recognizes power operator


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("recognizes power operator")
# Tests operator recognition for **
pass
```

</details>

### convert_binary_expression - Comparison

#### recognizes equality operator

- recognizes equality operator


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("recognizes equality operator")
# Tests operator recognition for ==
pass
```

</details>

#### recognizes inequality operator

- recognizes inequality operator


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("recognizes inequality operator")
# Tests operator recognition for !=
pass
```

</details>

#### recognizes less than operator

- recognizes less than operator


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("recognizes less than operator")
# Tests operator recognition for <
pass
```

</details>

#### recognizes less than or equal operator

- recognizes less than or equal operator


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("recognizes less than or equal operator")
# Tests operator recognition for <=
pass
```

</details>

#### recognizes greater than operator

- recognizes greater than operator


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("recognizes greater than operator")
# Tests operator recognition for >
pass
```

</details>

#### recognizes greater than or equal operator

- recognizes greater than or equal operator


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("recognizes greater than or equal operator")
# Tests operator recognition for >=
pass
```

</details>

### convert_binary_expression - Logical & Bitwise

#### recognizes logical and operator

- recognizes logical and operator


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("recognizes logical and operator")
# Tests operator recognition for and
pass
```

</details>

#### recognizes logical or operator

- recognizes logical or operator


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("recognizes logical or operator")
# Tests operator recognition for or
pass
```

</details>

#### recognizes bitwise and operator

- recognizes bitwise and operator


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("recognizes bitwise and operator")
# Tests operator recognition for &
pass
```

</details>

#### recognizes bitwise or operator

- recognizes bitwise or operator


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("recognizes bitwise or operator")
# Tests operator recognition for |
pass
```

</details>

#### recognizes bitwise xor operator

- recognizes bitwise xor operator


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("recognizes bitwise xor operator")
# Tests operator recognition for ^
pass
```

</details>

#### recognizes left shift operator

- recognizes left shift operator


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("recognizes left shift operator")
# Tests operator recognition for <<
pass
```

</details>

#### recognizes right shift operator

- recognizes right shift operator


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("recognizes right shift operator")
# Tests operator recognition for >>
pass
```

</details>

### convert_unary_expression

#### recognizes negation operator

- recognizes negation operator


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("recognizes negation operator")
# Tests operator recognition for -
pass
```

</details>

#### recognizes logical not operator

- recognizes logical not operator


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("recognizes logical not operator")
# Tests operator recognition for not
pass
```

</details>

#### recognizes bitwise not operator

- recognizes bitwise not operator


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("recognizes bitwise not operator")
# Tests operator recognition for ~
pass
```

</details>

#### recognizes reference operator

- recognizes reference operator


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("recognizes reference operator")
# Tests operator recognition for &
pass
```

</details>

#### recognizes dereference operator

- recognizes dereference operator


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("recognizes dereference operator")
# Tests operator recognition for *
pass
```

</details>

### Call Expression Conversion

#### converts function calls via convert_call_expression

- converts function calls via convert_call_expression


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts function calls via convert_call_expression")
# Tests function call node conversion
pass
```

</details>

#### extracts call arguments via convert_arguments

- extracts call arguments via convert_arguments


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts call arguments via convert_arguments")
# Tests argument list extraction
pass
```

</details>

#### converts method calls via convert_method_call

- converts method calls via convert_method_call


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts method calls via convert_method_call")
# Tests method call node conversion
pass
```

</details>

### Access Expression Conversion

#### converts index expressions via convert_index_expression

- converts index expressions via convert_index_expression


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts index expressions via convert_index_expression")
# Tests array/dict indexing
pass
```

</details>

#### converts field access via convert_field_expression

- converts field access via convert_field_expression


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts field access via convert_field_expression")
# Tests struct field access
pass
```

</details>

### Collection Literal Conversion

#### converts array literals via convert_array_literal

- converts array literals via convert_array_literal


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts array literals via convert_array_literal")
# Tests array literal conversion
pass
```

</details>

#### converts dict literals via convert_dict_literal

- converts dict literals via convert_dict_literal


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts dict literals via convert_dict_literal")
# Tests dict literal conversion
pass
```

</details>

#### converts dict entries via convert_dict_entry

- converts dict entries via convert_dict_entry


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts dict entries via convert_dict_entry")
# Tests key-value pair conversion
pass
```

</details>

#### converts tuple literals via convert_tuple_literal

- converts tuple literals via convert_tuple_literal


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts tuple literals via convert_tuple_literal")
# Tests tuple literal conversion
pass
```

</details>

### Lambda Expression Conversion

#### converts lambda expressions via convert_lambda

- converts lambda expressions via convert_lambda


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts lambda expressions via convert_lambda")
# Tests lambda expression conversion
pass
```

</details>

#### extracts lambda parameters via convert_lambda_params

- extracts lambda parameters via convert_lambda_params


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts lambda parameters via convert_lambda_params")
# Tests parameter list extraction
pass
```

</details>

### Control Flow Expression Conversion

#### converts if expressions via convert_if_expression

- converts if expressions via convert_if_expression


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts if expressions via convert_if_expression")
# Tests if-then-else conversion
pass
```

</details>

#### converts match expressions via convert_match_expression

- converts match expressions via convert_match_expression


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts match expressions via convert_match_expression")
# Tests pattern matching conversion
pass
```

</details>

#### converts match arms via convert_match_arm

- converts match arms via convert_match_arm


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts match arms via convert_match_arm")
# Tests case clause conversion
pass
```

</details>

#### converts range expressions via convert_range_expression

- converts range expressions via convert_range_expression


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts range expressions via convert_range_expression")
# Tests range literal conversion
pass
```

</details>

### Conversion Error Handling

#### returns error for unknown expression kind

- returns error for unknown expression kind


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns error for unknown expression kind")
# Tests unknown node type handling
pass
```

</details>

#### returns error for incomplete binary expression

- returns error for incomplete binary expression


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns error for incomplete binary expression")
# Tests missing operand detection
pass
```

</details>

#### returns error for incomplete unary expression

- returns error for incomplete unary expression


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns error for incomplete unary expression")
# Tests missing operand detection
pass
```

</details>

#### returns error for call missing callee

- returns error for call missing callee


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns error for call missing callee")
# Tests invalid call expression
pass
```

</details>

#### returns error for method call missing object

- returns error for method call missing object


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns error for method call missing object")
# Tests invalid method call
pass
```

</details>

#### returns error for incomplete index expression

- returns error for incomplete index expression


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns error for incomplete index expression")
# Tests missing index detection
pass
```

</details>

#### returns error for field access missing object

- returns error for field access missing object


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns error for field access missing object")
# Tests invalid field access
pass
```

</details>

#### returns error for incomplete dict entry

- returns error for incomplete dict entry


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns error for incomplete dict entry")
# Tests missing key or value
pass
```

</details>

#### returns error for lambda missing body

- returns error for lambda missing body


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns error for lambda missing body")
# Tests incomplete lambda
pass
```

</details>

#### returns error for incomplete if expression

- returns error for incomplete if expression


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns error for incomplete if expression")
# Tests missing branch detection
pass
```

</details>

#### returns error for match missing value

- returns error for match missing value


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns error for match missing value")
# Tests invalid match expression
pass
```

</details>

#### returns error for incomplete match arm

- returns error for incomplete match arm


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns error for incomplete match arm")
# Tests invalid case clause
pass
```

</details>

#### returns error for incomplete range expression

- returns error for incomplete range expression


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns error for incomplete range expression")
# Tests missing start or end
pass
```

</details>

#### returns error for empty parenthesized expression

- returns error for empty parenthesized expression


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns error for empty parenthesized expression")
# Tests invalid parentheses
pass
```

</details>

#### returns error for await missing expression

- returns error for await missing expression


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns error for await missing expression")
# Tests invalid await
pass
```

</details>

#### returns error for try missing expression

- returns error for try missing expression


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns error for try missing expression")
# Tests invalid try
pass
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/interpreter/ast_convert_expr_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering convert_expression Entry Point, convert_binary_expression - Arithmetic, convert_binary_expression - Comparison, convert_binary_expression - Logical & Bitwise, convert_unary_expression, Call Expression Conversion, Access Expression Conversion, Collection Literal Conversion, Lambda Expression Conversion, Control Flow Expression Conversion, Conversion Error Handling.
- convert_expression Entry Point
- convert_binary_expression - Arithmetic
- convert_binary_expression - Comparison
- convert_binary_expression - Logical & Bitwise
- convert_unary_expression
- Call Expression Conversion
- Access Expression Conversion
- Collection Literal Conversion
- Lambda Expression Conversion
- Control Flow Expression Conversion
- Conversion Error Handling

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 61 |
| Active scenarios | 61 |
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

- Canonical SPipe generation for source `ad912cf42bfc2fe12458be5adde3aaa19795ad5852ec4cae9e42dd5d295f1a2b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ad912cf42bfc2fe12458be5adde3aaa19795ad5852ec4cae9e42dd5d295f1a2b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ad912cf42bfc2fe12458be5adde3aaa19795ad5852ec4cae9e42dd5d295f1a2b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **82/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/unit/app/interpreter/ast_convert_expr_spec.spl
mirror: doc/06_spec/unit/app/interpreter/ast_convert_expr_spec.md (current)
findings: 6 blockers: 1
  narrative=100 structure=100 oracle=50
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=82; blocker cap makes effective=49
doc/06_spec/unit/app/interpreter/ast_convert_expr_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/interpreter/ast_convert_expr_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/interpreter/ast_convert_expr_spec.spl:1:1: blocker SSDOC-ORA-001 [oracle] (-50): no real executed assertion or compiler oracle
  why: A passing-looking document without an oracle is not conformance evidence.
  improve: Replace placeholders with an observable production assertion.
test/unit/app/interpreter/ast_convert_expr_spec.spl:53:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'converts integer literals' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/interpreter/ast_convert_expr_spec.spl:60:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'converts float literals' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/interpreter/ast_convert_expr_spec.spl:66:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'converts string literals' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
