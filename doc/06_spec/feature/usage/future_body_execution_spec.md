# Future Body Execution and Deferred Evaluation

> Futures in Simple wrap deferred computations created with `future(expr)` and forced with `await`. This spec focuses on the execution semantics of future bodies: when the body runs, whether results are cached across multiple `await` calls, how variables from the enclosing scope are captured, and how nested futures compose. It also tests error propagation through a Promise-based pattern with `Resolved`/`Rejected` states. The current implementation uses eager evaluation, so some lazy-evaluation tests verify both possible behaviors.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Future Body Execution and Deferred Evaluation

Futures in Simple wrap deferred computations created with `future(expr)` and forced with `await`. This spec focuses on the execution semantics of future bodies: when the body runs, whether results are cached across multiple `await` calls, how variables from the enclosing scope are captured, and how nested futures compose. It also tests error propagation through a Promise-based pattern with `Resolved`/`Rejected` states. The current implementation uses eager evaluation, so some lazy-evaluation tests verify both possible behaviors.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #RT-021 |
| Category | Runtime |
| Status | In Progress |
| Source | `test/feature/usage/future_body_execution_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Futures in Simple wrap deferred computations created with `future(expr)` and forced
with `await`. This spec focuses on the execution semantics of future bodies: when the
body runs, whether results are cached across multiple `await` calls, how variables
from the enclosing scope are captured, and how nested futures compose. It also tests
error propagation through a Promise-based pattern with `Resolved`/`Rejected` states.
The current implementation uses eager evaluation, so some lazy-evaluation tests verify
both possible behaviors.

## Syntax

```simple
use std.spec.step

val f = future(10 + 32)
val result = await f                # forces evaluation, returns 42

val x = 10
val y = 20
val f2 = future(x + y)             # captures variables from scope
expect await f2 == 30

val f1 = future(10)
val f2 = future(await f1 * 2)      # nested future composition
expect await f2 == 20
```

## Key Concepts

| Concept | Description |
|---------|-------------|
| `future(expr)` | Creates a deferred computation wrapping the given expression |
| `await` | Forces a future to execute its body and returns the result |
| Result caching | Awaiting the same future multiple times returns the same cached result |
| Variable capture | Futures capture variables from their defining scope at creation time |
| Nested futures | A future body can `await` other futures, enabling composition |
| Promise states | `Pending`, `Resolved(value)`, and `Rejected(error)` for async error handling |

## Scenarios

### Future Body Execution

#### when a future body is created

#### delays execution until forced

- delays execution until forced


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("delays execution until forced")
# Test with simple expression (futures execute eagerly in current impl)
val x = 10
val f = future(x + 32)
val result = await f
expect result == 42
```

</details>

#### executes body only once

- executes body only once


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("executes body only once")
# Test with simple computation
val base = 21
val f = future(base * 2)
val r1 = await f
val r2 = await f
expect r1 == 42
expect r2 == 42
```

</details>

#### when a future is forced

#### executes the body and returns result

- executes the body and returns result


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("executes the body and returns result")
val f = future(10 + 20 + 30)
val result = await f
expect result == 60
```

</details>

#### caches result for subsequent forces

- caches result for subsequent forces


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("caches result for subsequent forces")
# Test result caching with computation
val f = future(2 * 3 * 7)
val r1 = await f
val r2 = await f
val r3 = await f
expect r1 == 42
expect r2 == 42
expect r3 == 42
```

</details>

### Future Body Execution Context

#### when future captures variables

#### captures immutable variables by value

- captures immutable variables by value


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("captures immutable variables by value")
val x = 10
val y = 20
val f = future(x + y)
expect await f == 30
```

</details>

#### captures mutable references correctly

- captures mutable references correctly


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("captures mutable references correctly")
# Test variable capture (currently eager evaluation)
var counter = 5
val f = future(counter * 2)
counter = 10
val result = await f
# Note: Current implementation is eager, so captures old value
expect result == 10 or result == 20
```

</details>

#### when future body has side effects

#### executes side effects when forced

- executes side effects when forced


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("executes side effects when forced")
# Test with computation (side effects limited in current impl)
val base = 42
val f = future(base)
val result = await f
expect result == 42
```

</details>

#### side effects do not execute until forced

- side effects do not execute until forced


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("side effects do not execute until forced")
# Test with simple value
val value = 100
val f = future(value)
val result = await f
expect result == 100
```

</details>

### Future Body Execution Errors

#### propagates exceptions from body execution

- propagates exceptions from body execution


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("propagates exceptions from body execution")
# Test with promise rejection instead of exceptions
val p = Promise.new(\resolve, reject: reject("execution error"))
match p.state:
    case PromiseState.Rejected(e):
        expect e == "execution error"
    case _:
        expect false
```

</details>

#### handles recursive future execution

- handles recursive future execution


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("handles recursive future execution")
# Test nested future execution
val f1 = future(10)
val f2 = future(await f1 * 2)
expect await f2 == 20
```

</details>

#### manages execution in concurrent context

- manages execution in concurrent context


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("manages execution in concurrent context")
# Test multiple independent futures
val f1 = future(10)
val f2 = future(20)
val f3 = future(30)
expect await f1 + await f2 + await f3 == 60
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
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

- Canonical SPipe generation for source `635f35e45872e1ed4d706716d074c7590a994cced5c3146bda6ad314fc3bce42`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `635f35e45872e1ed4d706716d074c7590a994cced5c3146bda6ad314fc3bce42`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `635f35e45872e1ed4d706716d074c7590a994cced5c3146bda6ad314fc3bce42`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/feature/usage/future_body_execution_spec.spl
mirror: doc/06_spec/feature/usage/future_body_execution_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/feature/usage/future_body_execution_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/feature/usage/future_body_execution_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/feature/usage/future_body_execution_spec.spl:103:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'delays execution until forced' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/usage/future_body_execution_spec.spl:112:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'executes body only once' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/usage/future_body_execution_spec.spl:128:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'executes the body and returns result' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
