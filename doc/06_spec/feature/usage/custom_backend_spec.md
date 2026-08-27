# Custom Collection Backends

> Tests custom collection backend implementations including ArrayList and HashMap. Validates that array literals can be typed as ArrayList with push/pop/get operations, and that dictionary literals can be typed as HashMap with key-based access and insertion.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Custom Collection Backends

Tests custom collection backend implementations including ArrayList and HashMap. Validates that array literals can be typed as ArrayList with push/pop/get operations, and that dictionary literals can be typed as HashMap with key-based access and insertion.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #COLL-001 |
| Category | Runtime |
| Status | Active |
| Source | `test/feature/usage/custom_backend_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests custom collection backend implementations including ArrayList and HashMap.
Validates that array literals can be typed as ArrayList with push/pop/get
operations, and that dictionary literals can be typed as HashMap with
key-based access and insertion.

## Syntax

```simple
val arr: ArrayList = [1, 2, 3]
arr.push(3)
val map: HashMap = {"a": 1, "b": 2}
map["b"] = 2
```
Custom Collection Backends - SPipe Tests

## Scenarios

### Custom Collection Backends

#### ArrayList Implementation

#### should create ArrayList from array literal

- should create ArrayList from array literal
- should create ArrayList from array literal
   - Expected: arr.len() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("should create ArrayList from array literal")
step("should create ArrayList from array literal")
# @req: REQ-FEAT-USAGE-CUSTOM-BACKEND-SPEC-001
val arr: ArrayList = [1, 2, 3]
expect(arr.len()).to_equal(3)
```

</details>

#### should support push

- should support push
- should support push
   - Expected: arr.len() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("should support push")
step("should support push")
var arr: ArrayList = [1, 2]
arr.push(3)
expect(arr.len()).to_equal(3)
```

</details>

#### should support pop

- should support pop
- should support pop


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("should support pop")
step("should support pop")
var arr: ArrayList = [1, 2, 3]
val last = arr.pop()
expect last == 3
expect arr.len() == 2
```

</details>

#### should support get

- should support get
- should support get
   - Expected: arr.get(0) equals `10`
   - Expected: arr.get(2) equals `30`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("should support get")
step("should support get")
val arr: ArrayList = [10, 20, 30]
expect(arr.get(0)).to_equal(10)
expect(arr.get(2)).to_equal(30)
```

</details>

#### HashMap Implementation

#### should create HashMap from dict literal

- should create HashMap from dict literal
- should create HashMap from dict literal
   - Expected: map.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("should create HashMap from dict literal")
step("should create HashMap from dict literal")
val map: HashMap = {"a": 1, "b": 2}
expect(map.len()).to_equal(2)
```

</details>

#### should support get

- should support get
- should support get


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("should support get")
step("should support get")
val map: HashMap = {"a": 1, "b": 2}
expect map["a"] == 1
expect map["b"] == 2
```

</details>

#### should support insert

- should support insert
- should support insert


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("should support insert")
step("should support insert")
var map: HashMap = {"a": 1}
map["b"] = 2
expect map["b"] == 2
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

- `REQ-SSPEC-FEATURE`
- `REQ-FEAT-USAGE-CUSTOM-BACKEND-SPEC-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `56134aff0eeee8c055b58ed64b53a8a7b73d8b28abb58e744adf59f15dc0693d`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `56134aff0eeee8c055b58ed64b53a8a7b73d8b28abb58e744adf59f15dc0693d`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `56134aff0eeee8c055b58ed64b53a8a7b73d8b28abb58e744adf59f15dc0693d`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **82/100**; effective score: **82/100**; blockers: **0**.

SSpec documentization score: 82/100
source: test/feature/usage/custom_backend_spec.spl
mirror: doc/06_spec/feature/usage/custom_backend_spec.md (current)
findings: 12 blockers: 0
  narrative=100 structure=70 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/feature/usage/custom_backend_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/feature/usage/custom_backend_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/feature/usage/custom_backend_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 5 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/feature/usage/custom_backend_spec.spl:43:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should create ArrayList from array literal' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/feature/usage/custom_backend_spec.spl:43:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should create ArrayList from array literal' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/usage/custom_backend_spec.spl:51:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should support push' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/feature/usage/custom_backend_spec.spl:51:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should support push' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/usage/custom_backend_spec.spl:59:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should support pop' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/feature/usage/custom_backend_spec.spl:59:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should support pop' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/usage/custom_backend_spec.spl:68:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should support get' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/feature/usage/custom_backend_spec.spl:77:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should create HashMap from dict literal' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/feature/usage/custom_backend_spec.spl:84:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should support get' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
