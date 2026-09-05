# Contracts Specification

> Tests covering Contract System.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Contracts Specification

## Scenarios

### Contract System

#### Preconditions (requires:)

#### validates input constraints

- validates input constraints


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("validates input constraints")
# Functions can specify preconditions that must be true on entry
fn divide(a: i32, b: i32) -> i32:
    requires:
        b != 0
    a / b

# Valid call - precondition satisfied
expect divide(10, 2) == 5
```

</details>

#### supports multiple preconditions

- supports multiple preconditions


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("supports multiple preconditions")
fn transfer(amount: i64, balance: i64) -> i64:
    requires:
        amount > 0
        balance >= amount
    balance - amount

expect transfer(50, 100) == 50
```

</details>

#### Postconditions (ensures:)

#### validates output constraints

- validates output constraints


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("validates output constraints")
# Functions can specify postconditions that must be true on exit
fn abs(x: i32) -> i32:
    ensures:
        result >= 0
    if x < 0: 0 - x else: x

expect abs(-5) == 5
expect abs(5) == 5
```

</details>

#### can reference old values

- can reference old values


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("can reference old values")
# old(expr) captures the value at function entry
fn increment(x: i32) -> i32:
    ensures:
        result == old(x) + 1
    x + 1

expect increment(5) == 6
```

</details>

#### Combined Contracts

#### supports both preconditions and postconditions

- supports both preconditions and postconditions


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("supports both preconditions and postconditions")
fn safe_divide(a: i32, b: i32) -> i32:
    requires:
        b != 0
    ensures:
        result * b == a
    a / b

expect safe_divide(10, 2) == 5
```

</details>

#### Class Invariants

#### enforces class-level constraints

- enforces class-level constraints


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("enforces class-level constraints")
class Counter:
    value: i32

    invariant:
        value >= 0

    static fn new() -> Counter:
        Counter { value: 0 }

    me increment():
        self.value += 1

val counter = Counter.new()
expect counter.value == 0
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/contracts/contracts_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Contract System.
- Contract System

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `ad379b91f6955cc2d9d202288d772e29d77e078bd1b4e91176d46daf1826f908`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ad379b91f6955cc2d9d202288d772e29d77e078bd1b4e91176d46daf1826f908`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ad379b91f6955cc2d9d202288d772e29d77e078bd1b4e91176d46daf1826f908`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **91/100**; effective score: **91/100**; blockers: **0**.

SSpec documentization score: 91/100
source: test/01_unit/lib/common/contracts/contracts_spec.spl
mirror: doc/06_spec/01_unit/lib/common/contracts/contracts_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=95 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/contracts/contracts_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/contracts/contracts_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/contracts/contracts_spec.spl:22:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'validates input constraints' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/contracts/contracts_spec.spl:34:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'supports multiple preconditions' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/contracts/contracts_spec.spl:46:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'validates output constraints' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/contracts/contracts_spec.spl:58:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'can reference old values' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
