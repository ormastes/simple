# Seq Specification

> Tests covering seq tool.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Seq Specification

## Scenarios

### seq tool

#### single argument

#### generates 1 to N

- generates 1 to N
   - Expected: nums.len() equals `5`
   - Expected: nums[0] equals `1`
   - Expected: nums[4] equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("generates 1 to N")
var nums: [i64] = []
var i: i64 = 1
while i <= 5:
    nums = nums.push(i)
    i = i + 1
expect(nums.len()).to_equal(5)
expect(nums[0]).to_equal(1)
expect(nums[4]).to_equal(5)
```

</details>

#### two arguments

#### generates FIRST to LAST

- generates FIRST to LAST
   - Expected: nums.len() equals `5`
   - Expected: nums[0] equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("generates FIRST to LAST")
var nums: [i64] = []
var i: i64 = 3
while i <= 7:
    nums = nums.push(i)
    i = i + 1
expect(nums.len()).to_equal(5)
expect(nums[0]).to_equal(3)
```

</details>

#### three arguments

#### generates with increment

- generates with increment
   - Expected: nums.len() equals `6`
   - Expected: nums[0] equals `0`
   - Expected: nums[5] equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("generates with increment")
var nums: [i64] = []
var i: i64 = 0
while i <= 10:
    nums = nums.push(i)
    i = i + 2
expect(nums.len()).to_equal(6)
expect(nums[0]).to_equal(0)
expect(nums[5]).to_equal(10)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/unit/tools/shell/seq_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering seq tool.
- seq tool

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
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

- Canonical SPipe generation for source `2588c807367e9df9e26c141a3046548a63b3ce01eb4ddb9116929028e90af3e7`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `2588c807367e9df9e26c141a3046548a63b3ce01eb4ddb9116929028e90af3e7`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `2588c807367e9df9e26c141a3046548a63b3ce01eb4ddb9116929028e90af3e7`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/unit/tools/shell/seq_spec.spl
mirror: doc/06_spec/unit/tools/shell/seq_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/tools/shell/seq_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/tools/shell/seq_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/tools/shell/seq_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 8 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/tools/shell/seq_spec.spl:14:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'generates 1 to N' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/tools/shell/seq_spec.spl:27:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'generates FIRST to LAST' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/tools/shell/seq_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'generates with increment' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
