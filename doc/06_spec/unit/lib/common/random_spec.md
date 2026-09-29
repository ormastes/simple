# Random Specification

> Tests covering Random number generation.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Random Specification

## Scenarios

### Random number generation

#### Seeding

#### same seed produces same sequence

- same seed produces same sequence
   - Expected: a1 equals `b1`
   - Expected: a2 equals `b2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("same seed produces same sequence")
rng_seed(42)
val a1 = rng_next()
val a2 = rng_next()
rng_seed(42)
val b1 = rng_next()
val b2 = rng_next()
expect(a1).to_equal(b1)
expect(a2).to_equal(b2)
```

</details>

#### different seeds produce different sequences

- different seeds produce different sequences
   - Expected: different is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("different seeds produce different sequences")
rng_seed(42)
val a1 = rng_next()
rng_seed(99)
val b1 = rng_next()
# Very unlikely to be equal
val different = a1 != b1
expect(different).to_equal(true)
```

</details>

#### Range generation

#### generates value in range

- generates value in range
   - Expected: in_range is true
   - Expected: in_upper is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("generates value in range")
rng_seed(42)
val result = rng_int(1, 10)
val in_range = result >= 1
expect(in_range).to_equal(true)
val in_upper = result <= 10
expect(in_upper).to_equal(true)
```

</details>

#### generates multiple values in range

- generates multiple values in range
   - Expected: all_in_range is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("generates multiple values in range")
rng_seed(123)
var all_in_range = true
for _ in 0..20:
    val v = rng_int(0, 100)
    if v < 0 or v > 100:
        all_in_range = false
expect(all_in_range).to_equal(true)
```

</details>

#### generates different values

- generates different values
   - Expected: some_different is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("generates different values")
rng_seed(42)
val v1 = rng_next()
val v2 = rng_next()
val v3 = rng_next()
# At least two should differ
val some_different = v1 != v2 or v2 != v3
expect(some_different).to_equal(true)
```

</details>

#### Distribution properties

#### generates non-negative values

- generates non-negative values
   - Expected: all_positive is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("generates non-negative values")
rng_seed(42)
var all_positive = true
for _ in 0..50:
    val v = rng_next()
    if v < 0:
        all_positive = false
expect(all_positive).to_equal(true)
```

</details>

#### generates values spread across range

- generates values spread across range


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("generates values spread across range")
rng_seed(42)
var low_count = 0
var high_count = 0
for _ in 0..100:
    val v = rng_int(0, 99)
    if v < 50: low_count = low_count + 1
    if v >= 50: high_count = high_count + 1
# Both halves should have some values
expect(low_count).to_be_greater_than(10)
expect(high_count).to_be_greater_than(10)
```

</details>

#### Sequence operations

#### shuffles array by swapping

- shuffles array by swapping
   - Expected: arr.len() equals `5`
   - Expected: sum equals `15`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("shuffles array by swapping")
rng_seed(42)
var arr = [1, 2, 3, 4, 5]
# Fisher-Yates shuffle
for i in 0..4:
    val j = rng_int(i, 4)
    val tmp = arr[i]
    arr[i] = arr[j]
    arr[j] = tmp
# Should still have same length
expect(arr.len()).to_equal(5)
# Sum should be preserved
var sum = 0
for v in arr:
    sum = sum + v
expect(sum).to_equal(15)
```

</details>

#### picks random element from array

- picks random element from array
   - Expected: valid is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("picks random element from array")
rng_seed(42)
val items = [10, 20, 30, 40, 50]
val idx = rng_int(0, 4)
val picked = items[idx]
val valid = picked == 10 or picked == 20 or picked == 30 or picked == 40 or picked == 50
expect(valid).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/common/random_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Random number generation.
- Random number generation

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
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

- Canonical SPipe generation for source `9c6fdd15c4cc19ac0786a91fe7ae92889104f7feaeab318f3554d27e86b6bebd`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `9c6fdd15c4cc19ac0786a91fe7ae92889104f7feaeab318f3554d27e86b6bebd`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `9c6fdd15c4cc19ac0786a91fe7ae92889104f7feaeab318f3554d27e86b6bebd`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/unit/lib/common/random_spec.spl
mirror: doc/06_spec/unit/lib/common/random_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/common/random_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/common/random_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/common/random_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/lib/common/random_spec.spl:33:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'same seed produces same sequence' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/common/random_spec.spl:45:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'different seeds produce different sequences' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/common/random_spec.spl:57:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'generates value in range' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
