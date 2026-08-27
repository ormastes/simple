# Compiler Basics

> Tests fundamental compiler functionality including lexing, parsing, and basic code generation. Verifies that core language constructs such as variables, functions, and expressions compile and execute correctly.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 34 | 34 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Compiler Basics

Tests fundamental compiler functionality including lexing, parsing, and basic code generation. Verifies that core language constructs such as variables, functions, and expressions compile and execute correctly.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | In Progress |
| Source | `test/03_system/feature/compiler/compiler_basics_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests fundamental compiler functionality including lexing, parsing, and basic
code generation. Verifies that core language constructs such as variables,
functions, and expressions compile and execute correctly.

## Scenarios

### Integer Literals

#### compiles zero

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- compiles zero


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("compiles zero")
val result = 0
expect result == 0
```

</details>

#### compiles positive integer

- compiles positive integer


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("compiles positive integer")
val result = 42
expect result == 42
```

</details>

#### compiles negative integer

- compiles negative integer


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("compiles negative integer")
val result = -5
expect result == -5
```

</details>

### Arithmetic Operations

#### compiles addition

- compiles addition


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("compiles addition")
val result = 10 + 32
expect result == 42
```

</details>

#### compiles subtraction

- compiles subtraction


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("compiles subtraction")
val result = 50 - 8
expect result == 42
```

</details>

#### compiles multiplication

- compiles multiplication


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("compiles multiplication")
val result = 6 * 7
expect result == 42
```

</details>

#### compiles division

- compiles division


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("compiles division")
val result = 84 / 2
expect result == 42
```

</details>

#### compiles modulo

- compiles modulo


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("compiles modulo")
val result = 47 % 5
expect result == 2
```

</details>

#### compiles nested arithmetic

- compiles nested arithmetic


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("compiles nested arithmetic")
val result = (10 + 20) * 2 - 18
expect result == 42
```

</details>

### Comparison Operations

#### compiles less than - true case

- compiles less than - true case


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("compiles less than - true case")
val result = if 1 < 2: 1 else: 0
expect result == 1
```

</details>

#### compiles less than - false case

- compiles less than - false case


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("compiles less than - false case")
val result = if 2 < 1: 1 else: 0
expect result == 0
```

</details>

#### compiles greater than - true case

- compiles greater than - true case


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("compiles greater than - true case")
val result = if 2 > 1: 1 else: 0
expect result == 1
```

</details>

#### compiles greater than - false case

- compiles greater than - false case


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("compiles greater than - false case")
val result = if 1 > 2: 1 else: 0
expect result == 0
```

</details>

#### compiles less than or equal - equal case

- compiles less than or equal - equal case


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("compiles less than or equal - equal case")
val result = if 1 <= 1: 1 else: 0
expect result == 1
```

</details>

#### compiles less than or equal - false case

- compiles less than or equal - false case


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("compiles less than or equal - false case")
val result = if 2 <= 1: 1 else: 0
expect result == 0
```

</details>

#### compiles greater than or equal - equal case

- compiles greater than or equal - equal case


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("compiles greater than or equal - equal case")
val result = if 2 >= 2: 1 else: 0
expect result == 1
```

</details>

#### compiles greater than or equal - false case

- compiles greater than or equal - false case


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("compiles greater than or equal - false case")
val result = if 1 >= 2: 1 else: 0
expect result == 0
```

</details>

#### compiles equals - true case

- compiles equals - true case


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("compiles equals - true case")
val result = if 42 == 42: 1 else: 0
expect result == 1
```

</details>

#### compiles equals - false case

- compiles equals - false case


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("compiles equals - false case")
val result = if 42 == 43: 1 else: 0
expect result == 0
```

</details>

#### compiles not equals - true case

- compiles not equals - true case


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("compiles not equals - true case")
val result = if 42 != 43: 1 else: 0
expect result == 1
```

</details>

#### compiles not equals - false case

- compiles not equals - false case


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("compiles not equals - false case")
val result = if 42 != 42: 1 else: 0
expect result == 0
```

</details>

### Logical Operations

#### compiles logical and - true case

- compiles logical and - true case


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("compiles logical and - true case")
val result = if true and true: 1 else: 0
expect result == 1
```

</details>

#### compiles logical and - false case

- compiles logical and - false case


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("compiles logical and - false case")
val result = if true and false: 1 else: 0
expect result == 0
```

</details>

#### compiles logical or - true case

- compiles logical or - true case


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("compiles logical or - true case")
val result = if false or true: 1 else: 0
expect result == 1
```

</details>

#### compiles logical or - false case

- compiles logical or - false case


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("compiles logical or - false case")
val result = if false or false: 1 else: 0
expect result == 0
```

</details>

### Boolean Literals

#### compiles true literal

- compiles true literal


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("compiles true literal")
val result = if true: 42 else: 0
expect result == 42
```

</details>

#### compiles false literal

- compiles false literal


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("compiles false literal")
val result = if false: 0 else: 42
expect result == 42
```

</details>

### Variable Bindings

#### compiles single let binding

- compiles single let binding


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("compiles single let binding")
val x = 42
expect x == 42
```

</details>

#### compiles multiple let bindings

- compiles multiple let bindings


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("compiles multiple let bindings")
val a = 10
val b = 32
val result = a + b
expect result == 42
```

</details>

#### compiles binding with expression

- compiles binding with expression


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("compiles binding with expression")
val x = 10 + 32
expect x == 42
```

</details>

### Function Definitions

#### compiles simple function

- compiles simple function


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("compiles simple function")
fn get_value():
    return 42
expect get_value() == 42
```

</details>

#### compiles function with parameters

- compiles function with parameters


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("compiles function with parameters")
fn add(a, b):
    return a + b
expect add(10, 32) == 42
```

</details>

#### compiles function with multiple statements

- compiles function with multiple statements


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("compiles function with multiple statements")
fn calc(x, y):
    val sum = x + y
    return sum
expect calc(10, 32) == 42
```

</details>

#### compiles nested function call

- compiles nested function call


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("compiles nested function call")
fn double(x):
    return x * 2
fn add_doubled(a, b):
    return double(a) + double(b)
expect add_doubled(10, 11) == 42
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 34 |
| Active scenarios | 34 |
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

- Canonical SPipe generation for source `006ec83c0e5df15a27121fa517966ef73d226ccce879f6c17ff15a463b84f51e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `006ec83c0e5df15a27121fa517966ef73d226ccce879f6c17ff15a463b84f51e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `006ec83c0e5df15a27121fa517966ef73d226ccce879f6c17ff15a463b84f51e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/feature/compiler/compiler_basics_spec.spl
mirror: doc/06_spec/03_system/feature/compiler/compiler_basics_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/compiler/compiler_basics_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/compiler/compiler_basics_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/compiler/compiler_basics_spec.spl:77:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'compiles zero' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/compiler/compiler_basics_spec.spl:83:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'compiles positive integer' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/compiler/compiler_basics_spec.spl:89:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'compiles negative integer' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
