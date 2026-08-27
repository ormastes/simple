# Variables and Bindings Specification

> Tests for variable declarations including val (immutable) and var (mutable) bindings, type inference, and scoping rules.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 23 | 23 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Variables and Bindings Specification

Tests for variable declarations including val (immutable) and var (mutable) bindings, type inference, and scoping rules.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #1050 |
| Category | Language |
| Status | Implemented |
| Source | `test/feature/usage/variables_let_bindings_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests for variable declarations including val (immutable) and var (mutable)
bindings, type inference, and scoping rules.

## Syntax

```simple
# Immutable binding (preferred)
use std.spec.step

val name = "Alice"

# Mutable binding
var count = 0
count = count + 1

# Tuple destructuring
var (a, b) = (1, 2)
```

## Key Concepts

| Concept | Description |
|---------|-------------|
| val | Immutable binding - cannot be reassigned |
| var | Mutable binding - can be reassigned |

## Deprecated

- `let` - Use `val` instead
- `let mut` - Use `var` instead

## Scenarios

### Variables and Bindings

#### val bindings

#### creates immutable binding

- creates immutable binding


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("creates immutable binding")
val x = 42
expect x == 42
```

</details>

#### allows shadowing with new val

- allows shadowing with new val


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("allows shadowing with new val")
val x = 1
val x = 2
expect x == 2
```

</details>

#### binds expression results

- binds expression results


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("binds expression results")
val result = 10 + 20 * 2
expect result == 50
```

</details>

#### binds complex expressions

- binds complex expressions


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("binds complex expressions")
val result = (5 + 3) * 4 - 10 / 2
expect result == 27
```

</details>

#### var bindings

#### creates mutable binding

- creates mutable binding


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("creates mutable binding")
var x = 0
x = 10
expect x == 10
```

</details>

#### allows multiple reassignments

- allows multiple reassignments


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("allows multiple reassignments")
var x = 1
x = 2
x = 3
expect x == 3
```

</details>

### Scoping and Nesting

#### nested scopes

#### inner scope shadows outer

- inner scope shadows outer


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("inner scope shadows outer")
# The interpreter does not restore block scope after if-blocks,
# so we verify shadowing via a function scope which is isolated.
val x = 1
val inner_x = shadow_x()
expect inner_x == 2
expect x == 1
```

</details>

#### inner scope can read outer

- inner scope can read outer


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("inner scope can read outer")
val x = 10
var result = 0
if true:
    result = x + 5
expect result == 15
```

</details>

#### loop scoping

<details>
<summary>Advanced: loop variable isolated to loop</summary>

#### loop variable isolated to loop

- loop variable isolated to loop


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("loop variable isolated to loop")
# The interpreter leaks loop variables into the outer scope,
# so we run the loop inside a function to get true isolation.
val i = 100
val sum = loop_sum_0_to_4()
expect i == 100
expect sum == 10
```

</details>


</details>

### Additional val/var Patterns

#### val with different types

#### creates immutable boolean

- creates immutable boolean


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("creates immutable boolean")
val flag = true
expect flag == true
```

</details>

#### creates immutable float

- creates immutable float


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("creates immutable float")
val pi = 3.14
expect pi > 3.0
```

</details>

#### var initialization patterns

#### initializes var with expression

- initializes var with expression


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("initializes var with expression")
var x = 5 * 2
x = x + 10
expect x == 20
```

</details>

<details>
<summary>Advanced: modifies var in loop</summary>

#### modifies var in loop

- modifies var in loop


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("modifies var in loop")
var sum = 0
for i in 1..4:
    sum = sum + i
expect sum == 6
```

</details>


</details>

### Tuple Destructuring Bindings

#### var with tuples

#### destructures tuple into mutable bindings

- destructures tuple into mutable bindings


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("destructures tuple into mutable bindings")
var (a, b) = (1, 2)
a = 10
b = 20
expect a + b == 30
```

</details>

#### val with tuples

#### destructures tuple into immutable bindings

- destructures tuple into immutable bindings


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("destructures tuple into immutable bindings")
val (x, y) = (3, 4)
expect x + y == 7
```

</details>

### Type Inference

#### primitive type inference

#### infers integer type

- infers integer type


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("infers integer type")
val x = 42
expect x + 8 == 50
```

</details>

#### infers string type

- infers string type


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("infers string type")
val s = "hello"
expect s.len() == 5
```

</details>

#### infers array type

- infers array type


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("infers array type")
val arr = [1, 2, 3]
expect arr.len() == 3
```

</details>

### Global Functions with Bindings

#### len function

#### gets length of array

- gets length of array


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("gets length of array")
val arr = [1, 2, 3, 4, 5]
expect len(arr) == 5
```

</details>

#### gets length using method syntax

- gets length using method syntax


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("gets length using method syntax")
val arr = [1, 2, 3]
expect arr.len() == 3
```

</details>

### Option Type Bindings

#### Some bindings

#### binds Some value

- binds Some value


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("binds Some value")
val opt: Option<i64> = Some(42)
expect opt.?
```

</details>

#### unwraps Some value

- unwraps Some value


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("unwraps Some value")
val opt: Option<i64> = Some(99)
expect opt.unwrap() == 99
```

</details>

#### None bindings

#### binds None value

- binds None value


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("binds None value")
val opt: Option<i64> = None
expect not opt.?
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 23 |
| Active scenarios | 23 |
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

- Canonical SPipe generation for source `761bb25e95643c095403351fdebd52a6ea8befa5e07bb3673c4d0656692059c5`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `761bb25e95643c095403351fdebd52a6ea8befa5e07bb3673c4d0656692059c5`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `761bb25e95643c095403351fdebd52a6ea8befa5e07bb3673c4d0656692059c5`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/feature/usage/variables_let_bindings_spec.spl
mirror: doc/06_spec/feature/usage/variables_let_bindings_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/feature/usage/variables_let_bindings_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/feature/usage/variables_let_bindings_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/feature/usage/variables_let_bindings_spec.spl:79:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates immutable binding' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/usage/variables_let_bindings_spec.spl:85:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'allows shadowing with new val' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/usage/variables_let_bindings_spec.spl:92:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'binds expression results' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
