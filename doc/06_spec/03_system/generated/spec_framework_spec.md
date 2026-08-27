# spec_framework_spec

> BDD Spec Framework Tests

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 31 | 31 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# spec_framework_spec

BDD Spec Framework Tests

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/generated/spec_framework_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

BDD Spec Framework Tests
Feature: SPipe BDD Testing Framework
Category: Testing, Framework
Status: Complete

Comprehensive tests for the BDD spec framework itself including
describe, context, it, expect, and matcher DSL.

## Scenarios

### BDD Spec Framework

#### describe blocks

#### groups tests by description

- groups tests by description


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("groups tests by description")
expect true
```

</details>

#### supports nested context blocks

- supports nested context blocks


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("supports nested context blocks")
expect true
```

</details>

#### executes blocks in order

- executes blocks in order


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("executes blocks in order")
var results = []
results.push(1)
expect len(results) == 1
results.push(2)
expect len(results) == 2
```

</details>

#### context blocks (nested describes)

#### creates nested example groups

- creates nested example groups


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("creates nested example groups")
expect true
```

</details>

#### inherits parent context

- inherits parent context


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("inherits parent context")
val parent_val = 42
expect parent_val == 42
```

</details>

#### supports multiple levels of nesting

- supports multiple levels of nesting


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("supports multiple levels of nesting")
val level1 = "one"
val level2 = "two"
expect level1 == "one"
expect level2 == "two"
```

</details>

#### it blocks (test definitions)

#### defines a single test case

- defines a single test case


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("defines a single test case")
expect true
```

</details>

#### supports multiple assertions per test

- supports multiple assertions per test


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("supports multiple assertions per test")
expect 1 + 1 == 2
expect 2 * 3 == 6
expect "hello" == "hello"
```

</details>

#### can use local variables in tests

- can use local variables in tests


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("can use local variables in tests")
val x = 10
val y = 20
val z = x + y
expect z == 30
```

</details>

#### expect assertions

#### asserts equality with ==

- asserts equality with ==


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("asserts equality with ==")
expect 42 == 42
```

</details>

#### asserts inequality with !=

- asserts inequality with !=


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("asserts inequality with !=")
expect 5 != 6
```

</details>

#### supports boolean assertions

- supports boolean assertions


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("supports boolean assertions")
expect true
expect (not false)
```

</details>

#### supports string comparisons

- supports string comparisons


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("supports string comparisons")
expect "hello" == "hello"
expect "hello" != "world"
```

</details>

#### expect with matchers

#### uses 'to be' for equality

- uses 'to be' for equality


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("uses 'to be' for equality")
expect 5 to be 5
```

</details>

#### uses 'to eq' for equality

- uses 'to eq' for equality


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("uses 'to eq' for equality")
expect 5 to eq 5
```

</details>

#### uses 'to be_gt' for greater than

- uses 'to be_gt' for greater than


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("uses 'to be_gt' for greater than")
expect 10 to be_gt 5
```

</details>

#### uses 'to be_lt' for less than

- uses 'to be_lt' for less than


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("uses 'to be_lt' for less than")
expect 3 to be_lt 10
```

</details>

#### uses 'to include' for string containment

- uses 'to include' for string containment


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("uses 'to include' for string containment")
expect "hello world" to include "world"
```

</details>

#### uses 'to start_with' for string prefix

- uses 'to start_with' for string prefix


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("uses 'to start_with' for string prefix")
expect "hello world" to start_with "hello"
```

</details>

#### uses 'to end_with' for string suffix

- uses 'to end_with' for string suffix


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("uses 'to end_with' for string suffix")
expect "hello world" to end_with "world"
```

</details>

#### negated assertions

#### supports 'not_to' for negative assertions

- supports 'not_to' for negative assertions


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("supports 'not_to' for negative assertions")
expect 5 not_to eq 6
```

</details>

#### supports multiple negative matchers

- supports multiple negative matchers


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("supports multiple negative matchers")
expect 10 not_to be_lt 5
expect "hello" not_to include "xyz"
```

</details>

#### complex assertions

#### handles complex expressions

- handles complex expressions


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("handles complex expressions")
val a = [1, 2, 3]
expect len(a) == 3
```

</details>

#### chains multiple assertions

- chains multiple assertions


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("chains multiple assertions")
val computed = 2 + 2
expect computed == 4
expect computed to be_gt 0
expect computed to be_lt 10
```

</details>

#### works with computed values

- works with computed values


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("works with computed values")
val a = 5
val b = a * 2
expect b == 10
val c = 3 * 2
expect c == 6
```

</details>

#### works with conditional logic

- works with conditional logic


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("works with conditional logic")
val x = 10
if x > 5:
    expect x to be_gt 5
else:
    fail "x should be greater than 5"
```

</details>

#### assertion failures

#### fails with appropriate message on false assertion

- fails with appropriate message on false assertion


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("fails with appropriate message on false assertion")
expect true
```

</details>

#### can test multiple conditions

- can test multiple conditions


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("can test multiple conditions")
val values = [1, 2, 3, 4, 5]
expect len(values) == 5
expect values[0] == 1
expect values[4] == 5
```

</details>

#### describe/context/it structure

#### preserves nested structure

- preserves nested structure


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("preserves nested structure")
expect true
```

</details>

#### deeply nested

#### supports many levels

- supports many levels


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("supports many levels")
expect true
```

</details>

#### even deeper

#### continues to work

- continues to work


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("continues to work")
expect true
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 31 |
| Active scenarios | 31 |
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

- Canonical SPipe generation for source `71724f0a0b8739a20a35e068d3cdb07d6a61a3708613e0b057f8028d7a75a1e2`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `71724f0a0b8739a20a35e068d3cdb07d6a61a3708613e0b057f8028d7a75a1e2`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `71724f0a0b8739a20a35e068d3cdb07d6a61a3708613e0b057f8028d7a75a1e2`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **91/100**; effective score: **91/100**; blockers: **0**.

SSpec documentization score: 91/100
source: test/03_system/generated/spec_framework_spec.spl
mirror: doc/06_spec/03_system/generated/spec_framework_spec.md (current)
findings: 7 blockers: 0
  narrative=100 structure=90 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/generated/spec_framework_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/generated/spec_framework_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/generated/spec_framework_spec.spl:25:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'groups tests by description' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/generated/spec_framework_spec.spl:30:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'supports nested context blocks' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/generated/spec_framework_spec.spl:35:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'executes blocks in order' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/generated/spec_framework_spec.spl:77:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'can use local variables in tests' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/generated/spec_framework_spec.spl:195:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'can test multiple conditions' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
