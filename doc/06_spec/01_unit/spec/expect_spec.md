# expect_spec

> Unit tests for the BDD Expect module.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 21 | 21 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# expect_spec

Unit tests for the BDD Expect module.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/01_unit/spec/expect_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Unit tests for the BDD Expect module.

This test file verifies the expect assertion API used in BDD-style tests:
- Basic expect function with integers, strings, and booleans
- Positive and negative assertions (equality, comparison, negation)
- Chained and complex expectations with nested structures
- Edge cases including zero values, empty strings, and Option types

The expect function is the primary assertion mechanism in the Simple test framework.

## Scenarios

### BDD Expect

#### expect function

#### works with integers

- works with integers


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SPEC
step("works with integers")
expect 42 == 42
```

</details>

#### works with strings

- works with strings


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SPEC
step("works with strings")
expect "hello" == "hello"
```

</details>

#### works with booleans

- works with booleans


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SPEC
step("works with booleans")
val enabled = true
val disabled = false
expect enabled == not disabled
expect disabled == not enabled
```

</details>

#### positive assertions

#### passes when values are equal

- passes when values are equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SPEC
step("passes when values are equal")
expect 42 == 42
```

</details>

#### passes with greater than

- passes with greater than


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SPEC
step("passes with greater than")
expect 10 > 5
```

</details>

#### passes with less than

- passes with less than


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SPEC
step("passes with less than")
expect 5 < 10
```

</details>

#### passes with true

- passes with true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SPEC
step("passes with true")
expect true
```

</details>

#### negative assertions

#### passes when values are not equal

- passes when values are not equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SPEC
step("passes when values are not equal")
expect 42 != 10
```

</details>

#### passes with negated comparison

- passes with negated comparison


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SPEC
step("passes with negated comparison")
expect not (5 > 10)
```

</details>

#### passes with false negated

- passes with false negated


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SPEC
step("passes with false negated")
expect not false
```

</details>

#### chaining expectations

#### can have multiple expectations

- can have multiple expectations


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SPEC
step("can have multiple expectations")
val value = 42
expect value == 42
expect value > 40
expect value < 50
```

</details>

#### can mix positive and negative

- can mix positive and negative


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SPEC
step("can mix positive and negative")
val value = 42
expect value == 42
expect value != 10
expect value > 40
expect not (value > 100)
```

</details>

#### complex assertions

#### handles nested structures

- handles nested structures


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SPEC
step("handles nested structures")
val name = "Alice"
val age = 30
expect name == "Alice"
expect age > 25
```

</details>

#### handles Option types

- handles Option types


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SPEC
step("handles Option types")
val some_value = Some(42)
expect some_value.is_some()
```

</details>

#### handles comparisons

- handles comparisons


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SPEC
step("handles comparisons")
val a = 10
val b = 20
val c = 10
expect a == c
expect a != b
expect a < b
expect b > a
```

</details>

#### edge cases

#### handles zero values

- handles zero values


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SPEC
step("handles zero values")
expect 0 == 0
expect 0 < 1
expect 0 > -1
```

</details>

#### handles empty strings

- handles empty strings


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SPEC
step("handles empty strings")
expect "" == ""
expect "" != "hello"
```

</details>

#### handles None values

- handles None values


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SPEC
step("handles None values")
expect Some(42).is_some()
```

</details>

#### type safety

#### works with integers

- works with integers


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SPEC
step("works with integers")
expect 42 == 42
expect 42 > 40
```

</details>

#### works with strings

- works with strings


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SPEC
step("works with strings")
expect "hello" == "hello"
expect "hello" != "world"
```

</details>

#### works with booleans

- works with booleans


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SPEC
step("works with booleans")
expect true
expect not false
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 21 |
| Active scenarios | 21 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SPEC`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `2fc411249cd704ceac168955c8b45da68213fa6f7f45fbff9a5bf6aa2acd3c69`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `2fc411249cd704ceac168955c8b45da68213fa6f7f45fbff9a5bf6aa2acd3c69`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `2fc411249cd704ceac168955c8b45da68213fa6f7f45fbff9a5bf6aa2acd3c69`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **91/100**; effective score: **91/100**; blockers: **0**.

SSpec documentization score: 91/100
source: test/01_unit/spec/expect_spec.spl
mirror: doc/06_spec/01_unit/spec/expect_spec.md (current)
findings: 7 blockers: 0
  narrative=100 structure=90 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/spec/expect_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/spec/expect_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/spec/expect_spec.spl:35:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'works with integers' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/spec/expect_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'works with strings' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/spec/expect_spec.spl:45:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'works with booleans' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/spec/expect_spec.spl:91:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'can have multiple expectations' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/spec/expect_spec.spl:99:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'can mix positive and negative' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
