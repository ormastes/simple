# shrinking_spec

> Property Testing Framework - Shrinking Tests

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 17 | 17 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# shrinking_spec

Property Testing Framework - Shrinking Tests

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/generated/shrinking_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Property Testing Framework - Shrinking Tests
Feature: Automatic input minimization to find minimal failing test cases

## Scenarios

### Shrinking Algorithm

#### Integer Shrinking

#### shrinks positive integers towards zero

- shrinks positive integers towards zero


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("shrinks positive integers towards zero")
val candidates = shrink_i64(100)
# Should include 0
expect candidates.contains(0)
# Should include value/2 = 50
expect candidates.contains(50)
# Should include value-1 = 99
expect candidates.contains(99)
# All candidates should be smaller in absolute value
for c in candidates:
    expect c.abs() <= 100
```

</details>

#### shrinks negative integers towards zero

- shrinks negative integers towards zero


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("shrinks negative integers towards zero")
val candidates = shrink_i64(-100)
# Should include 0
expect candidates.contains(0)
# Should include value/2 = -50
expect candidates.contains(-50)
# Should include value+1 = -99
expect candidates.contains(-99)
# All candidates should be closer to zero
for c in candidates:
    expect c.abs() <= 100
```

</details>

#### cannot shrink zero

- cannot shrink zero


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("cannot shrink zero")
val candidates = shrink_i64(0)
# Zero cannot be shrunk further
expect len(candidates) == 0
```

</details>

#### List Shrinking

#### shrinks to empty list

- shrinks to empty list


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("shrinks to empty list")
val candidates = shrink_list([1, 2, 3, 4, 5])
# Should include empty list as candidate
expect candidates.contains([])
```

</details>

#### shrinks by removing half

- shrinks by removing half


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("shrinks by removing half")
val candidates = shrink_list([1, 2, 3, 4, 5, 6])
# Should include first half [1, 2, 3]
expect candidates.contains([1, 2, 3])
# Should include second half [4, 5, 6]
expect candidates.contains([4, 5, 6])
```

</details>

#### shrinks by removing first element

- shrinks by removing first element


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("shrinks by removing first element")
val candidates = shrink_list([1, 2, 3])
# Should include list with first element removed
expect candidates.contains([2, 3])
```

</details>

#### shrinks by removing last element

- shrinks by removing last element


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("shrinks by removing last element")
val candidates = shrink_list([1, 2, 3])
# Should include list with last element removed
expect candidates.contains([1, 2])
```

</details>

#### cannot shrink empty list

- cannot shrink empty list


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("cannot shrink empty list")
val candidates = shrink_list([])
# Empty list cannot be shrunk
expect len(candidates) == 0
```

</details>

#### text Shrinking

#### shrinks to empty string

- shrinks to empty string


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("shrinks to empty string")
val candidates = shrink_string("hello")
# Should include empty string
expect candidates.contains("")
```

</details>

#### shrinks by removing characters

- shrinks by removing characters


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("shrinks by removing characters")
val candidates = shrink_string("hello")
# Should have multiple candidates
expect len(candidates) > 1
# Should include substring from start
expect candidates.contains("he")
# Should include substring with first char removed
expect candidates.contains("ello")
```

</details>

#### cannot shrink empty string

- cannot shrink empty string


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("cannot shrink empty string")
val candidates = shrink_string("")
# Empty string cannot be shrunk
expect len(candidates) == 0
```

</details>

#### Full Shrinking Process

#### finds minimal failing case for integers

- finds minimal failing case for integers


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("finds minimal failing case for integers")
# Property: value must be < 50
val test_fn = |x| x < 50

# Start with failing value 100
val result = shrink_to_minimal(
    failing_value: 100,
    test_fn: test_fn,
    max_shrinks: 100,
    max_depth: 10
)

# Should shrink to minimal failing value (50)
expect result.result_type == ShrinkResultType.MinimalFailure
expect result.value == 50
expect result.shrinks > 0
```

</details>

#### finds minimal failing case for lists

- finds minimal failing case for lists


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("finds minimal failing case for lists")
# Property: list sum must be < 10
val test_fn = |list| list_sum(list) < 10

# Start with failing list that sums to > 10
val (result_type, value, shrinks) = shrink_list_to_minimal(
    failing_list: [3, 3, 3, 3, 3],
    test_fn: test_fn,
    max_shrinks: 100,
    max_depth: 10
)

# Should shrink to a minimal failing list
expect result_type == ShrinkResultType.MinimalFailure
expect list_sum(value) >= 10
```

</details>

#### handles max_shrinks limit

- handles max_shrinks limit


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("handles max_shrinks limit")
# Property that always fails
val test_fn = |x| false

val result = shrink_to_minimal(
    failing_value: 1000000,
    test_fn: test_fn,
    max_shrinks: 5,
    max_depth: 10
)

# Should hit max_shrinks limit or find minimal
expect result.shrinks <= 5
```

</details>

#### handles max_depth limit

- handles max_depth limit


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("handles max_depth limit")
# Property that always fails
val test_fn = |x| false

val result = shrink_to_minimal(
    failing_value: 100,
    test_fn: test_fn,
    max_shrinks: 1000,
    max_depth: 3
)

# Should terminate due to depth limit
expect result.result_type == ShrinkResultType.MinimalFailure or result.result_type == ShrinkResultType.MaxShrinksExceeded
```

</details>

#### Edge Cases

#### handles no shrink possible

- handles no shrink possible


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("handles no shrink possible")
# Zero cannot be shrunk
val test_fn = |x| x > 0

val result = shrink_to_minimal(
    failing_value: 0,
    test_fn: test_fn,
    max_shrinks: 100,
    max_depth: 10
)

# Should report minimal with 0 value
expect result.value == 0
expect result.shrinks == 0
```

</details>

#### handles all shrinks passing

- handles all shrinks passing


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("handles all shrinks passing")
# Property: value must be exactly 42
val test_fn = |x| x == 42

# Start with failing value 100 (which is != 42)
val result = shrink_to_minimal(
    failing_value: 100,
    test_fn: test_fn,
    max_shrinks: 100,
    max_depth: 10
)

# Shrink candidates (0, 50, 99) all fail since they're not 42
# Eventually we'll find 0 as the minimal value != 42
expect result.value != 42
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 17 |
| Active scenarios | 17 |
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

- Canonical SPipe generation for source `98efed374696a8afea9410f1bdf1a0a7a8b24668c1b34e46c82c3dfd142cc1c3`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `98efed374696a8afea9410f1bdf1a0a7a8b24668c1b34e46c82c3dfd142cc1c3`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `98efed374696a8afea9410f1bdf1a0a7a8b24668c1b34e46c82c3dfd142cc1c3`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/generated/shrinking_spec.spl
mirror: doc/06_spec/03_system/generated/shrinking_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/generated/shrinking_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/generated/shrinking_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/generated/shrinking_spec.spl:169:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'shrinks positive integers towards zero' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/generated/shrinking_spec.spl:183:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'shrinks negative integers towards zero' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/generated/shrinking_spec.spl:197:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'cannot shrink zero' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
