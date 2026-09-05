# Dataset Specification

> Tests covering Dataset, DataLoader.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Dataset Specification

## Scenarios

### Dataset

#### sequential sampler

#### creates sequential sampler

- creates sequential sampler


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates sequential sampler")
val sampler = MockSequentialSampler.new(100)
expect sampler.dataset_size == 100
```

</details>

#### returns indices in order

- returns indices in order


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns indices in order")
var sampler = MockSequentialSampler.new(10)
val idx1 = sampler.next_index()
val idx2 = sampler.next_index()
expect idx2 == idx1 + 1
expect sampler.is_sequential()
```

</details>

#### handles large datasets

- handles large datasets


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles large datasets")
val sampler = MockSequentialSampler.new(10000)
expect sampler.dataset_size == 10000
```

</details>

### DataLoader

#### sampler

#### creates random sampler

- creates random sampler


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates random sampler")
val sampler = MockRandomSampler.new(50)
expect sampler.dataset_size == 50
```

</details>

#### returns all indices

- returns all indices


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns all indices")
val sampler = MockRandomSampler.new(100)
expect sampler.dataset_size == 100
```

</details>

#### shuffles differently each time

- shuffles differently each time


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("shuffles differently each time")
val sampler = MockRandomSampler.new(20)
expect sampler.shuffle()
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/ml/dataset_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Dataset, DataLoader.
- Dataset
- DataLoader

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

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `2b3cd69ee1eceda2c0c51ade455f8220f2fb7de26ffcea776504224690576a59`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `2b3cd69ee1eceda2c0c51ade455f8220f2fb7de26ffcea776504224690576a59`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `2b3cd69ee1eceda2c0c51ade455f8220f2fb7de26ffcea776504224690576a59`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/lib/ml/dataset_spec.spl
mirror: doc/06_spec/unit/lib/ml/dataset_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/ml/dataset_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/ml/dataset_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/ml/dataset_spec.spl:44:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates sequential sampler' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/ml/dataset_spec.spl:50:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns indices in order' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/ml/dataset_spec.spl:59:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'handles large datasets' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
