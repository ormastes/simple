# Example Count Regression Specification

> Tests covering group 01, group 02, group 03, group 04, group 05, group 06, group 07, group 08, group 09, group 10, group 11, group 12, group 13, group 14, group 15, group 16.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 51 | 51 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Example Count Regression Specification

## Scenarios

### group 01

#### case 01

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- case 01
   - Expected: 1 + 1 equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("case 01")
expect(1 + 1).to_equal(2)
```

</details>

#### case 02

- case 02
   - Expected: 2 + 2 equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("case 02")
expect(2 + 2).to_equal(4)
```

</details>

#### case 03

- case 03
   - Expected: 3 + 3 equals `6`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("case 03")
expect(3 + 3).to_equal(6)
```

</details>

### group 02

#### case 01

- case 01
   - Expected: 1 equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("case 01")
expect(1).to_equal(1)
```

</details>

#### case 02

- case 02
   - Expected: 2 equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("case 02")
expect(2).to_equal(2)
```

</details>

#### case 03

- case 03
   - Expected: 3 equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("case 03")
expect(3).to_equal(3)
```

</details>

### group 03

#### case 01

- case 01


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("case 01")
expect(true).to_be_true()
```

</details>

#### case 02

- case 02


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("case 02")
expect(false).to_be_false()
```

</details>

#### case 03

- case 03
   - Expected: "a" equals `a`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("case 03")
expect("a").to_equal("a")
```

</details>

### group 04

#### case 01

- case 01
   - Expected: [1, 2, 3].len() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("case 01")
expect([1, 2, 3].len()).to_equal(3)
```

</details>

#### case 02

- case 02
   - Expected: [1, 2].len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("case 02")
expect([1, 2].len()).to_equal(2)
```

</details>

#### case 03

- case 03
   - Expected: [].len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("case 03")
expect([].len()).to_equal(0)
```

</details>

### group 05

#### nested a

#### case 01

- case 01
   - Expected: 10 - 4 equals `6`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("case 01")
expect(10 - 4).to_equal(6)
```

</details>

#### case 02

- case 02
   - Expected: 10 - 5 equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("case 02")
expect(10 - 5).to_equal(5)
```

</details>

#### nested b

#### case 03

- case 03
   - Expected: 10 - 6 equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("case 03")
expect(10 - 6).to_equal(4)
```

</details>

#### case 04

- case 04
   - Expected: 10 - 7 equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("case 04")
expect(10 - 7).to_equal(3)
```

</details>

### group 06

#### case 01

- case 01
   - Expected: 2 * 2 equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("case 01")
expect(2 * 2).to_equal(4)
```

</details>

#### case 02

- case 02
   - Expected: 2 * 3 equals `6`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("case 02")
expect(2 * 3).to_equal(6)
```

</details>

#### case 03

- case 03
   - Expected: 2 * 4 equals `8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("case 03")
expect(2 * 4).to_equal(8)
```

</details>

### group 07

#### case 01

- case 01
   - Expected: 4 / 2 equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("case 01")
expect(4 / 2).to_equal(2)
```

</details>

#### case 02

- case 02
   - Expected: 6 / 2 equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("case 02")
expect(6 / 2).to_equal(3)
```

</details>

#### case 03

- case 03
   - Expected: 8 / 2 equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("case 03")
expect(8 / 2).to_equal(4)
```

</details>

### group 08

#### case 01

- case 01
   - Expected: "abc".len() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("case 01")
expect("abc".len()).to_equal(3)
```

</details>

#### case 02

- case 02


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("case 02")
expect("ab".contains("a")).to_be_true()
```

</details>

#### case 03

- case 03


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("case 03")
expect("ab".contains("z")).to_be_false()
```

</details>

### group 09

#### case 01

- case 01


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("case 01")
expect(1 < 2).to_be_true()
```

</details>

#### case 02

- case 02


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("case 02")
expect(2 < 1).to_be_false()
```

</details>

#### case 03

- case 03


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("case 03")
expect(2 <= 2).to_be_true()
```

</details>

### group 10

#### nested a

#### case 01

- case 01


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("case 01")
expect(1 < 2).to_be_true()
```

</details>

#### case 02

- case 02


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("case 02")
expect(2 > 1).to_be_true()
```

</details>

#### nested b

#### case 03

- case 03


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("case 03")
expect(2 >= 2).to_be_true()
```

</details>

#### case 04

- case 04


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("case 04")
expect(2 <= 2).to_be_true()
```

</details>

### group 11

#### case 01

- case 01
   - Expected: 1 equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("case 01")
expect(1).to_equal(1)
```

</details>

#### case 02

- case 02
   - Expected: 2 equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("case 02")
expect(2).to_equal(2)
```

</details>

#### case 03

- case 03
   - Expected: "" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("case 03")
expect("").to_equal("")
```

</details>

### group 12

#### case 01

- case 01


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("case 01")
expect("hi".starts_with("h")).to_be_true()
```

</details>

#### case 02

- case 02


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("case 02")
expect("hi".ends_with("i")).to_be_true()
```

</details>

#### case 03

- case 03


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("case 03")
expect("hi".contains("h")).to_be_true()
```

</details>

### group 13

#### case 01

- case 01
   - Expected: 1.0 equals `1.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("case 01")
expect(1.0).to_equal(1.0)
```

</details>

#### case 02

- case 02
   - Expected: 1.5 equals `1.5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("case 02")
expect(1.5).to_equal(1.5)
```

</details>

#### case 03

- case 03
   - Expected: 2.0 equals `2.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("case 03")
expect(2.0).to_equal(2.0)
```

</details>

### group 14

#### case 01

- case 01
   - Expected: [1, 2].len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("case 01")
expect([1, 2].len()).to_equal(2)
```

</details>

#### case 02

- case 02
   - Expected: [1, 2, 3].len() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("case 02")
expect([1, 2, 3].len()).to_equal(3)
```

</details>

#### case 03

- case 03
   - Expected: [].len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("case 03")
expect([].len()).to_equal(0)
```

</details>

### group 15

#### case 01

- case 01
   - Expected: "match" equals `match`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("case 01")
expect("match").to_equal("match")
```

</details>

#### case 02

- case 02
   - Expected: 5 equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("case 02")
expect(5).to_equal(5)
```

</details>

#### case 03

- case 03
   - Expected: 6 equals `6`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("case 03")
expect(6).to_equal(6)
```

</details>

### group 16

#### case 01

- case 01
   - Expected: 7 equals `7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("case 01")
expect(7).to_equal(7)
```

</details>

#### case 02

- case 02
   - Expected: 8 equals `8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("case 02")
expect(8).to_equal(8)
```

</details>

#### case 03

- case 03
   - Expected: 9 equals `9`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("case 03")
expect(9).to_equal(9)
```

</details>

#### orphan case (no enclosing describe) still counts toward the total

- orphan case (no enclosing describe) still counts toward the total
   - Expected: 10 equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("orphan case (no enclosing describe) still counts toward the total")
expect(10).to_equal(10)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/test_runner_new/example_count_regression_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering group 01, group 02, group 03, group 04, group 05, group 06, group 07, group 08, group 09, group 10, group 11, group 12, group 13, group 14, group 15, group 16.
- group 01
- group 02
- group 03
- group 04
- group 05
- group 06
- group 07
- group 08
- group 09
- group 10
- group 11
- group 12
- group 13
- group 14
- group 15
- group 16

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 51 |
| Active scenarios | 51 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-APP`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `0d4cbe350f3761c8bda1adf339a798824af2278cf6fe9299cb200b9bc51a862b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `0d4cbe350f3761c8bda1adf339a798824af2278cf6fe9299cb200b9bc51a862b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `0d4cbe350f3761c8bda1adf339a798824af2278cf6fe9299cb200b9bc51a862b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/app/test_runner_new/example_count_regression_spec.spl
mirror: doc/06_spec/01_unit/app/test_runner_new/example_count_regression_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/test_runner_new/example_count_regression_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/test_runner_new/example_count_regression_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/test_runner_new/example_count_regression_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 34 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/app/test_runner_new/example_count_regression_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'case 01' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/test_runner_new/example_count_regression_spec.spl:44:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'case 02' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/test_runner_new/example_count_regression_spec.spl:48:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'case 03' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
