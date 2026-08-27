# Mixed Function Patterns (Interpreter)

> Tests mixed function patterns in the interpreter including nested calls, higher-order functions, and recursive definitions. Verifies that complex function composition and calling conventions work correctly in interpreted mode.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Mixed Function Patterns (Interpreter)

Tests mixed function patterns in the interpreter including nested calls, higher-order functions, and recursive definitions. Verifies that complex function composition and calling conventions work correctly in interpreted mode.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Runtime |
| Status | In Progress |
| Source | `test/03_system/feature/interpreter/sample/python_inspired_sample/functions_mixed_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests mixed function patterns in the interpreter including nested calls, higher-order
functions, and recursive definitions. Verifies that complex function composition
and calling conventions work correctly in interpreted mode.

## Scenarios

### Mixed Function Patterns

#### default parameters

#### uses default when argument omitted

- uses default when argument omitted


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("uses default when argument omitted")
fn greet(name: text, greeting: text = "Hello"):
    "{greeting}, {name}!"
expect greet("Alice") == "Hello, Alice!"
```

</details>

#### overrides default when provided

- overrides default when provided


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("overrides default when provided")
fn greet(name: text, greeting: text = "Hello"):
    "{greeting}, {name}!"
expect greet("Bob", "Hi") == "Hi, Bob!"
```

</details>

#### named arguments

#### calls with named arguments

- calls with named arguments


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("calls with named arguments")
fn make_point(x: i64, y: i64) -> (i64, i64):
    (x, y)
val p = make_point(x: 10, y: 20)
expect p == (10, 20)
```

</details>

#### higher-order functions

#### passes function as argument

- passes function as argument


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("passes function as argument")
fn apply(f: fn(i64) -> i64, x: i64) -> i64:
    f(x)
fn double(n: i64) -> i64:
    n * 2
expect apply(double, 5) == 10
```

</details>

#### uses lambda expression

- uses lambda expression


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("uses lambda expression")
val items = [1, 2, 3]
val doubled = items.map(_ * 2)
expect doubled == [2, 4, 6]
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

- Canonical SPipe generation for source `9358e897f2816a47a5ebfd8d71f550c82f69d97f239394cc54fba05d11cc641e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `9358e897f2816a47a5ebfd8d71f550c82f69d97f239394cc54fba05d11cc641e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `9358e897f2816a47a5ebfd8d71f550c82f69d97f239394cc54fba05d11cc641e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/feature/interpreter/sample/python_inspired_sample/functions_mixed_spec.spl
mirror: doc/06_spec/03_system/feature/interpreter/sample/python_inspired_sample/functions_mixed_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/interpreter/sample/python_inspired_sample/functions_mixed_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/interpreter/sample/python_inspired_sample/functions_mixed_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/interpreter/sample/python_inspired_sample/functions_mixed_spec.spl:41:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'uses default when argument omitted' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/interpreter/sample/python_inspired_sample/functions_mixed_spec.spl:48:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'overrides default when provided' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/interpreter/sample/python_inspired_sample/functions_mixed_spec.spl:56:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'calls with named arguments' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
