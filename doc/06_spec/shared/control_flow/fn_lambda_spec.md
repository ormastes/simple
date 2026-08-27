# Fn Lambda Specification

> Tests covering fn() Lambda Syntax, basic inline lambdas, block lambdas, nested lambdas, compatibility with backslash operator, used in BDD framework.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Fn Lambda Specification

## Scenarios

### fn() Lambda Syntax

### basic inline lambdas

#### supports fn() with no parameters

- supports fn() with no parameters


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("supports fn() with no parameters")
fn call_it(f) -> i64:
    f()

val result = call_it(fn(): 42)
expect result == 42
```

</details>

#### supports fn(x) with single parameter

- supports fn(x) with single parameter


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("supports fn(x) with single parameter")
fn apply(x: i64, f) -> i64:
    f(x)

val result = apply(5, fn(n): n * 2)
expect result == 10
```

</details>

#### supports fn(x, y) with multiple parameters

- supports fn(x, y) with multiple parameters


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("supports fn(x, y) with multiple parameters")
fn apply2(x: i64, y: i64, f) -> i64:
    f(x, y)

val result = apply2(3, 4, fn(a, b): a + b)
expect result == 7
```

</details>

### block lambdas

#### supports fn() with indented block

- supports fn() with indented block


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("supports fn() with indented block")
fn execute(f) -> i64:
    f()

fn sum_xy() -> i64:
    val x = 10
    val y = 20
    x + y

val result = execute(sum_xy)
expect result == 30
```

</details>

#### supports fn(x) with parameter and block

- supports fn(x) with parameter and block


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("supports fn(x) with parameter and block")
fn transform(x: i64, f) -> i64:
    f(x)

fn compute_square(n) -> i64:
    val doubled = n * 2
    val squared = doubled * doubled
    squared

val result = transform(5, compute_square)
expect result == 100
```

</details>

### nested lambdas

#### supports nested fn() lambdas

- supports nested fn() lambdas


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("supports nested fn() lambdas")
fn outer(f):
    f

fn inner(g) -> i64:
    g()

val result = inner(outer(fn(): 99))
expect result == 99
```

</details>

### compatibility with backslash operator

#### fn() and \\ are interchangeable

- fn() and \\ are interchangeable


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("fn() and \\ are interchangeable")
fn test_sum(f1, f2) -> i64:
    f1() + f2()

# Mix both syntaxes
val result = test_sum(fn(): 10, \: 20)
expect result == 30
```

</details>

### used in BDD framework

#### works with context/it blocks

- works with context/it blocks


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("works with context/it blocks")
# Closures capture by value: a callback cannot write back to an
# enclosing function's local var (lint CLOS001). Block execution is
# therefore observed through the block's RETURN value.
fn mock_context(name: text, block) -> bool:
    block()

val executed = mock_context("test", fn(): true)

expect executed == true
```

</details>

#### passes context values into the block result

- passes context values into the block result


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("passes context values into the block result")
fn mock_context(name: text, x: i64, block) -> i64:
    block(x)

val doubled = mock_context("test", 21, fn(n): n * 2)

expect doubled == 42
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/shared/control_flow/fn_lambda_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering fn() Lambda Syntax, basic inline lambdas, block lambdas, nested lambdas, compatibility with backslash operator, used in BDD framework.
- fn() Lambda Syntax
- basic inline lambdas
- block lambdas
- nested lambdas
- compatibility with backslash operator
- used in BDD framework

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

- `REQ-SSPEC-SHARED`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `a4907277fb0f79d77ed48afd3c16f093d112c0730e5845dfed9dc352a5226a2c`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a4907277fb0f79d77ed48afd3c16f093d112c0730e5845dfed9dc352a5226a2c`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a4907277fb0f79d77ed48afd3c16f093d112c0730e5845dfed9dc352a5226a2c`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/shared/control_flow/fn_lambda_spec.spl
mirror: doc/06_spec/shared/control_flow/fn_lambda_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/shared/control_flow/fn_lambda_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/shared/control_flow/fn_lambda_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/shared/control_flow/fn_lambda_spec.spl:27:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'supports fn() with no parameters' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/shared/control_flow/fn_lambda_spec.spl:36:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'supports fn(x) with single parameter' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/shared/control_flow/fn_lambda_spec.spl:45:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'supports fn(x, y) with multiple parameters' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
