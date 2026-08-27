# Functions with Return Values (Interpreter)

> Tests function return value handling in the interpreter including explicit returns, implicit last-expression returns, and multi-value returns. Verifies that return values are correctly propagated through the call stack.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Functions with Return Values (Interpreter)

Tests function return value handling in the interpreter including explicit returns, implicit last-expression returns, and multi-value returns. Verifies that return values are correctly propagated through the call stack.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Runtime |
| Status | In Progress |
| Source | `test/03_system/feature/interpreter/sample/python_inspired_sample/functions_return_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests function return value handling in the interpreter including explicit returns,
implicit last-expression returns, and multi-value returns. Verifies that return
values are correctly propagated through the call stack.

## Scenarios

### Functions with Return Values

#### implicit return

#### returns last expression

- returns last expression


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("returns last expression")
fn double(x: i64) -> i64:
    x * 2
expect double(5) == 10
```

</details>

#### returns computed value

- returns computed value


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("returns computed value")
fn square(n: i64) -> i64:
    n * n
expect square(4) == 16
```

</details>

#### explicit return

#### returns early from function

- returns early from function


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("returns early from function")
fn classify(x: i64) -> text:
    if x < 0:
        return "negative"
    "non-negative"
expect classify(-5) == "negative"
expect classify(5) == "non-negative"
```

</details>

#### return type inference

#### infers integer return type

- infers integer return type


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("infers integer return type")
fn add(a: i64, b: i64):
    a + b
expect add(3, 4) == 7
```

</details>

#### infers string return type

- infers string return type


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("infers string return type")
fn greet(name: text):
    "Hello, {name}!"
expect greet("World") == "Hello, World!"
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
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

- Canonical SPipe generation for source `4e7bc03ad41be0e0acdf52f3f47a55df066c897df18c6e3ed7e430712b0f96bb`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `4e7bc03ad41be0e0acdf52f3f47a55df066c897df18c6e3ed7e430712b0f96bb`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `4e7bc03ad41be0e0acdf52f3f47a55df066c897df18c6e3ed7e430712b0f96bb`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/feature/interpreter/sample/python_inspired_sample/functions_return_spec.spl
mirror: doc/06_spec/03_system/feature/interpreter/sample/python_inspired_sample/functions_return_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/interpreter/sample/python_inspired_sample/functions_return_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/interpreter/sample/python_inspired_sample/functions_return_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/interpreter/sample/python_inspired_sample/functions_return_spec.spl:41:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns last expression' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/interpreter/sample/python_inspired_sample/functions_return_spec.spl:48:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns computed value' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/interpreter/sample/python_inspired_sample/functions_return_spec.spl:56:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns early from function' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
