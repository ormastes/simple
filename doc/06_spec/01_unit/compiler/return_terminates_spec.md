# A `return` at function-body statement level must terminate the function

> A `return` written at the **statement level of a function body** (not nested inside an `if`/loop/match arm) must end the function. MIR lowering writes the `Return` terminator into the *current* block but never starts a new one, so following statements keep emitting into that same block and a later `return` **overwrites** the terminator. The observable result is that dead code after an unconditional `return` executes, and a value-returning function yields the value of the *last* `return` rather than the first.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# A `return` at function-body statement level must terminate the function

A `return` written at the **statement level of a function body** (not nested inside an `if`/loop/match arm) must end the function. MIR lowering writes the `Return` terminator into the *current* block but never starts a new one, so following statements keep emitting into that same block and a later `return` **overwrites** the terminator. The observable result is that dead code after an unconditional `return` executes, and a value-returning function yields the value of the *last* `return` rather than the first.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Control flow / MIR lowering parity |
| Status | Active |
| Source | `test/01_unit/compiler/return_terminates_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

A `return` written at the **statement level of a function body** (not nested
inside an `if`/loop/match arm) must end the function. MIR lowering writes the
`Return` terminator into the *current* block but never starts a new one, so
following statements keep emitting into that same block and a later `return`
**overwrites** the terminator. The observable result is that dead code after an
unconditional `return` executes, and a value-returning function yields the
value of the *last* `return` rather than the first.

A `return` nested inside an `if` is unaffected — it lands in its own then-block,
which is why the codebase mostly works and why this survived so long.

The tree-walking interpreter honours the return correctly, so this spec passes
there; it is the compiled lanes (JIT / native) that regress. Keeping the spec
means a future MIR fix has an executable statement of the contract.

## Syntax

```simple
use std.spec.step

fn first_wins() -> i64:
    return 1
    return 2          # must never execute; result must be 1
```

## Scenarios

### a statement-level return terminates the function

#### returns the first of two consecutive returns

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
```

</details>

#### returns before later statements and a later return

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
assert_equal(return_then_stmts_then_return(), 4)
```

</details>

#### does not execute statements after an unconditional return

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
dead_ran = false
assert_equal(returns_before_dead_code(), 11)
assert_equal(dead_ran, false)
```

</details>

### nested returns are unaffected

#### returns from inside an if

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
assert_equal(nested_if_return(), 1)
```

</details>

<details>
<summary>Advanced: returns from inside a loop</summary>

#### returns from inside a loop

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
assert_equal(nested_loop_return(), 7)
```

</details>


</details>

#### takes the conditional early return

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
assert_equal(early_return_on_condition(1), 100)
```

</details>

#### falls through to the trailing return

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
assert_equal(early_return_on_condition(-1), 200)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
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

- Canonical SPipe generation for source `72c2108a4805bf515b3c742b0013b13e67d1d5981992a5c4ba0f519b62b601a1`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `72c2108a4805bf515b3c742b0013b13e67d1d5981992a5c4ba0f519b62b601a1`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `72c2108a4805bf515b3c742b0013b13e67d1d5981992a5c4ba0f519b62b601a1`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **89/100**; effective score: **89/100**; blockers: **0**.

SSpec documentization score: 89/100
source: test/01_unit/compiler/return_terminates_spec.spl
mirror: doc/06_spec/01_unit/compiler/return_terminates_spec.md (current)
findings: 7 blockers: 0
  narrative=100 structure=60 oracle=100
  traceability=100 evidence=100 coverage=100 maintainability=55
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/return_terminates_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/return_terminates_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/return_terminates_spec.spl:1:1: advice SSDOC-MNT-001 [maintainability] (-15): multiple scenarios form a flat, unfolded presentation
  why: Long flat dumps obscure the primary workflow.
  improve: Group secondary detail and keep the primary workflow visible.
test/01_unit/compiler/return_terminates_spec.spl:83:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'returns the first of two consecutive returns' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/compiler/return_terminates_spec.spl:88:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'returns before later statements and a later return' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/compiler/return_terminates_spec.spl:91:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'does not execute statements after an unconditional return' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/compiler/return_terminates_spec.spl:97:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'returns from inside an if' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
<!-- sspec-maintain:scorecard:end -->
