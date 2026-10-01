# Object Fit Wpt Specification

> Tests covering WPT-derived CSS object-fit subset.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Object Fit Wpt Specification

## Scenarios

### WPT-derived CSS object-fit subset

#### compute_object_fit pure function

#### fill stretches to box dimensions

- fill stretches to box dimensions
   - Expected: approx(result.dest_width, 200.0) is true
   - Expected: approx(result.dest_height, 200.0) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("fill stretches to box dimensions")
val result = compute_object_fit(100.0, 50.0, 200.0, 200.0, "fill", "50% 50%")
expect(approx(result.dest_width, 200.0)).to_equal(true)
expect(approx(result.dest_height, 200.0)).to_equal(true)
```

</details>

#### contain preserves aspect ratio within box

- contain preserves aspect ratio within box
   - Expected: approx(result.dest_width, 100.0) is true
   - Expected: approx(result.dest_height, 50.0) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("contain preserves aspect ratio within box")
val result = compute_object_fit(200.0, 100.0, 100.0, 100.0, "contain", "50% 50%")
expect(approx(result.dest_width, 100.0)).to_equal(true)
expect(approx(result.dest_height, 50.0)).to_equal(true)
```

</details>

#### cover fills box preserving aspect ratio

- cover fills box preserving aspect ratio
   - Expected: approx(result.dest_width, 200.0) is true
   - Expected: approx(result.dest_height, 100.0) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("cover fills box preserving aspect ratio")
val result = compute_object_fit(200.0, 100.0, 100.0, 100.0, "cover", "50% 50%")
expect(approx(result.dest_width, 200.0)).to_equal(true)
expect(approx(result.dest_height, 100.0)).to_equal(true)
```

</details>

#### none uses natural dimensions

- none uses natural dimensions
   - Expected: approx(result.dest_width, 50.0) is true
   - Expected: approx(result.dest_height, 30.0) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("none uses natural dimensions")
val result = compute_object_fit(50.0, 30.0, 100.0, 100.0, "none", "50% 50%")
expect(approx(result.dest_width, 50.0)).to_equal(true)
expect(approx(result.dest_height, 30.0)).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/feature/web_platform/css/object_fit_wpt_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering WPT-derived CSS object-fit subset.
- WPT-derived CSS object-fit subset

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-FEATURE`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `1488c920bff7bb5e0b74e335940064ac57112da18d38605adb6a8585a71c0f56`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `1488c920bff7bb5e0b74e335940064ac57112da18d38605adb6a8585a71c0f56`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `1488c920bff7bb5e0b74e335940064ac57112da18d38605adb6a8585a71c0f56`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/feature/web_platform/css/object_fit_wpt_spec.spl
mirror: doc/06_spec/feature/web_platform/css/object_fit_wpt_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/feature/web_platform/css/object_fit_wpt_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/feature/web_platform/css/object_fit_wpt_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/feature/web_platform/css/object_fit_wpt_spec.spl:21:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'fill stretches to box dimensions' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/web_platform/css/object_fit_wpt_spec.spl:28:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'contain preserves aspect ratio within box' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/web_platform/css/object_fit_wpt_spec.spl:35:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'cover fills box preserving aspect ratio' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
