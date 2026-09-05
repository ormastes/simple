# Type System Integration Specification

> Tests covering Type Inference in Variable Declarations, Type Checking in Function Calls, Monomorphization Cache, Complex Type System Features.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 17 | 17 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Type System Integration Specification

## Scenarios

### Type Inference in Variable Declarations

#### infers i64 from integer literal

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- infers i64 from integer literal
   - Expected: x equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("infers i64 from integer literal")
val x = 42
expect(x).to_equal(42)
```

</details>

#### infers f64 from float literal

- infers f64 from float literal
   - Expected: pi equals `3.14`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("infers f64 from float literal")
val pi = 3.14
expect(pi).to_equal(3.14)
```

</details>

#### infers text from string literal

- infers text from string literal
   - Expected: greeting equals `Hello`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("infers text from string literal")
val greeting = "Hello"
expect(greeting).to_equal("Hello")
```

</details>

#### infers bool from boolean literal

- infers bool from boolean literal
   - Expected: flag is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("infers bool from boolean literal")
val flag = true
expect(flag).to_equal(true)
```

</details>

#### infers type from binary operation

- infers type from binary operation
   - Expected: sum equals `30`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("infers type from binary operation")
val sum = 10 + 20
expect(sum).to_equal(30)
```

</details>

#### infers bool from comparison

- infers bool from comparison
   - Expected: is_greater is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("infers bool from comparison")
val is_greater = 5 > 3
expect(is_greater).to_equal(true)
```

</details>

#### infers bool from logical operation

- infers bool from logical operation
   - Expected: both_true is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("infers bool from logical operation")
val both_true = true and true
expect(both_true).to_equal(true)
```

</details>

### Type Checking in Function Calls

#### validates correct parameter types

- validates correct parameter types
   - Expected: result equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("validates correct parameter types")
fn multiply(a: i64, b: i64) -> i64:
    a * b
val result = multiply(6, 7)
expect(result).to_equal(42)
```

</details>

#### works with mixed parameter types

- works with mixed parameter types
   - Expected: result equals `100 units`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("works with mixed parameter types")
fn format_number(num: i64, suffix: text) -> text:
    str(num) + suffix
val result = format_number(100, " units")
expect(result).to_equal("100 units")
```

</details>

#### handles bool parameters

- handles bool parameters
   - Expected: result is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles bool parameters")
fn negate(x: bool) -> bool:
    not x
val result = negate(false)
expect(result).to_equal(true)
```

</details>

#### handles f64 parameters

- handles f64 parameters
   - Expected: result equals `16.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles f64 parameters")
fn square(x: f64) -> f64:
    x * x
val result = square(4.0)
expect(result).to_equal(16.0)
```

</details>

### Monomorphization Cache

#### caches function calls with same types

- caches function calls with same types
   - Expected: result1 equals `10`
   - Expected: result2 equals `20`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("caches function calls with same types")
fn identity(x):
    x
val result1 = identity(10)
val result2 = identity(20)
expect(result1).to_equal(10)
expect(result2).to_equal(20)
```

</details>

#### handles different type instantiations

- handles different type instantiations
   - Expected: int_result equals `42`
   - Expected: text_result equals `hello`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles different type instantiations")
fn first(a, b):
    a
val int_result = first(42, 100)
val text_result = first("hello", "world")
expect(int_result).to_equal(42)
expect(text_result).to_equal("hello")
```

</details>

### Complex Type System Features

#### combines type inference with type checking

- combines type inference with type checking
   - Expected: output equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("combines type inference with type checking")
fn process(value: i64) -> i64:
    value * 2
val input = 21
val output = process(input)
expect(output).to_equal(42)
```

</details>

#### works with nested function calls

- works with nested function calls
   - Expected: result equals `30`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("works with nested function calls")
fn add_ten(x: i64) -> i64:
    x + 10
fn double_it(y: i64) -> i64:
    y * 2
val result = double_it(add_ten(5))
expect(result).to_equal(30)
```

</details>

#### handles array types

- handles array types
   - Expected: sum equals `15`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles array types")
val numbers = [1, 2, 3, 4, 5]
var sum: i64 = 0
for n in numbers:
    sum = sum + n
expect(sum).to_equal(15)
```

</details>

#### infers types in control flow

- infers types in control flow
   - Expected: message equals `yes`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("infers types in control flow")
val condition = 10 > 5
val message = if condition: "yes" else: "no"
expect(message).to_equal("yes")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/unit/compiler_core/type_system_integration_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Type Inference in Variable Declarations, Type Checking in Function Calls, Monomorphization Cache, Complex Type System Features.
- Type Inference in Variable Declarations
- Type Checking in Function Calls
- Monomorphization Cache
- Complex Type System Features

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 17 |
| Active scenarios | 17 |
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

- Canonical SPipe generation for source `0dd50b5094f93fbb0d4afa858a100b45cf38f4e00713cafb8d9c121d263e2e83`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `0dd50b5094f93fbb0d4afa858a100b45cf38f4e00713cafb8d9c121d263e2e83`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `0dd50b5094f93fbb0d4afa858a100b45cf38f4e00713cafb8d9c121d263e2e83`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/unit/compiler_core/type_system_integration_spec.spl
mirror: doc/06_spec/unit/compiler_core/type_system_integration_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/compiler_core/type_system_integration_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/compiler_core/type_system_integration_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/compiler_core/type_system_integration_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 11 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/compiler_core/type_system_integration_spec.spl:14:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'infers i64 from integer literal' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler_core/type_system_integration_spec.spl:20:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'infers f64 from float literal' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler_core/type_system_integration_spec.spl:26:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'infers text from string literal' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
