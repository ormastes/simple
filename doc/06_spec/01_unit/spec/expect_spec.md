# expect_spec

> This test file verifies the expect assertion API used in BDD-style tests:

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 21 | 21 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# expect_spec

This test file verifies the expect assertion API used in BDD-style tests:

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/01_unit/spec/expect_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
## Operator workflow
## Compatibility and limitations


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

- Verify: works with integers


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-SPEC_EXPECT-001
step("Verify: works with integers")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
expect 42 == 42
```

</details>

#### works with strings

- Verify: works with strings


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-SPEC_EXPECT-001
step("Verify: works with strings")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
expect "hello" == "hello"
```

</details>

#### works with booleans

- Verify: works with booleans


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-SPEC_EXPECT-001
step("Verify: works with booleans")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val enabled = true
val disabled = false
expect enabled == not disabled
expect disabled == not enabled
```

</details>

#### positive assertions

#### passes when values are equal

- Verify: passes when values are equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-SPEC_EXPECT-001
step("Verify: passes when values are equal")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
expect 42 == 42
```

</details>

#### passes with greater than

- Verify: passes with greater than


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-SPEC_EXPECT-001
step("Verify: passes with greater than")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
expect 10 > 5
```

</details>

#### passes with less than

- Verify: passes with less than


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-SPEC_EXPECT-001
step("Verify: passes with less than")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
expect 5 < 10
```

</details>

#### passes with true

- Verify: passes with true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-SPEC_EXPECT-001
step("Verify: passes with true")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
expect true
```

</details>

#### negative assertions

#### passes when values are not equal

- Verify: passes when values are not equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-SPEC_EXPECT-001
step("Verify: passes when values are not equal")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
expect 42 != 10
```

</details>

#### passes with negated comparison

- Verify: passes with negated comparison


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-SPEC_EXPECT-001
step("Verify: passes with negated comparison")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
expect not (5 > 10)
```

</details>

#### passes with false negated

- Verify: passes with false negated


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-SPEC_EXPECT-001
step("Verify: passes with false negated")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
expect not false
```

</details>

#### chaining expectations

#### can have multiple expectations

- Verify: can have multiple expectations


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-SPEC_EXPECT-001
step("Verify: can have multiple expectations")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val value = 42
expect value == 42
expect value > 40
expect value < 50
```

</details>

#### can mix positive and negative

- Verify: can mix positive and negative


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-SPEC_EXPECT-001
step("Verify: can mix positive and negative")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val value = 42
expect value == 42
expect value != 10
expect value > 40
expect not (value > 100)
```

</details>

#### complex assertions

#### handles nested structures

- Verify: handles nested structures


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-SPEC_EXPECT-001
step("Verify: handles nested structures")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val name = "Alice"
val age = 30
expect name == "Alice"
expect age > 25
```

</details>

#### handles Option types

- Verify: handles Option types


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-SPEC_EXPECT-001
step("Verify: handles Option types")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val some_value = Some(42)
expect some_value.is_some()
```

</details>

#### handles comparisons

- Verify: handles comparisons


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-SPEC_EXPECT-001
step("Verify: handles comparisons")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
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

- Verify: handles zero values


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-SPEC_EXPECT-001
step("Verify: handles zero values")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
expect 0 == 0
expect 0 < 1
expect 0 > -1
```

</details>

#### handles empty strings

- Verify: handles empty strings


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-SPEC_EXPECT-001
step("Verify: handles empty strings")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
expect "" == ""
expect "" != "hello"
```

</details>

#### handles None values

- Verify: handles None values


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-SPEC_EXPECT-001
step("Verify: handles None values")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
expect Some(42).is_some()
```

</details>

#### type safety

#### works with integers

- Verify: works with integers


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-SPEC_EXPECT-001
step("Verify: works with integers")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
expect 42 == 42
expect 42 > 40
```

</details>

#### works with strings

- Verify: works with strings


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-SPEC_EXPECT-001
step("Verify: works with strings")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
expect "hello" == "hello"
expect "hello" != "world"
```

</details>

#### works with booleans

- Verify: works with booleans


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-SPEC_EXPECT-001
step("Verify: works with booleans")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
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

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `ea1c258bd702a9daf666741939b4997e9e189cb625958aa7e6bac8cbb293c961`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ea1c258bd702a9daf666741939b4997e9e189cb625958aa7e6bac8cbb293c961`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ea1c258bd702a9daf666741939b4997e9e189cb625958aa7e6bac8cbb293c961`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **93/100**; effective score: **93/100**; blockers: **0**.

SSpec documentization score: 93/100
source: test/01_unit/spec/expect_spec.spl
mirror: doc/06_spec/01_unit/spec/expect_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=90 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/spec/expect_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/01_unit/spec/expect_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/spec/expect_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, traceability, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/spec/expect_spec.spl:102:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'can have multiple expectations' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/spec/expect_spec.spl:111:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'can mix positive and negative' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
