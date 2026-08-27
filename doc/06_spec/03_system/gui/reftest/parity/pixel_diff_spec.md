# Pixel Diff Specification

> Tests covering compare_pictures, compare_with_threshold.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Pixel Diff Specification

## Scenarios

### compare_pictures

#### two empty pictures have ratio 0.0

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- two empty pictures have ratio 0.0


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("two empty pictures have ratio 0.0")
val a = _empty_picture()
val b = _empty_picture()
val result = compare_pictures(a, b, _cull_10x10(), 0)
expect result.ratio to_equal 0.0
```

</details>

#### identical pictures (same DrawRect color) have ratio 0.0

- identical pictures (same DrawRect color) have ratio 0.0


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("identical pictures (same DrawRect color) have ratio 0.0")
val a = _picture_with_rect(255, 0, 0)
val b = _picture_with_rect(255, 0, 0)
val result = compare_pictures(a, b, _cull_10x10(), 0)
expect result.ratio to_equal 0.0
```

</details>

#### different pictures (different rect colors) have ratio > 0.0

- different pictures (different rect colors) have ratio > 0.0


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("different pictures (different rect colors) have ratio > 0.0")
val a = _picture_with_rect(255, 0, 0)
val b = _picture_with_rect(0, 0, 255)
val result = compare_pictures(a, b, _cull_10x10(), 0)
expect result.ratio to_be_greater_than 0.0
```

</details>

#### max_delta reports channel difference magnitude for two-color pictures

- max_delta reports channel difference magnitude for two-color pictures


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("max_delta reports channel difference magnitude for two-color pictures")
val a = _picture_with_rect(255, 0, 0)
val b = _picture_with_rect(0, 0, 0)
val result = compare_pictures(a, b, _cull_10x10(), 0)
expect result.max_delta to_be_greater_than 0
```

</details>

### compare_with_threshold

#### passes when ratio <= threshold

- passes when ratio <= threshold


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("passes when ratio <= threshold")
val a = _empty_picture()
val b = _empty_picture()
val result = compare_with_threshold(a, b, _cull_10x10(), 0.01, 0)
expect result.passed to_equal true
```

</details>

#### fails when ratio > threshold

- fails when ratio > threshold


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("fails when ratio > threshold")
val a = _picture_with_rect(255, 0, 0)
val b = _picture_with_rect(0, 0, 255)
val result = compare_with_threshold(a, b, _cull_10x10(), 0.0, 0)
expect result.passed to_equal false
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/gui/reftest/parity/pixel_diff_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering compare_pictures, compare_with_threshold.
- compare_pictures
- compare_with_threshold

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

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `d7435635348c8835c982f28b0a3d26fb1d80baad454db371c9d4aff56efc1868`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `d7435635348c8835c982f28b0a3d26fb1d80baad454db371c9d4aff56efc1868`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `d7435635348c8835c982f28b0a3d26fb1d80baad454db371c9d4aff56efc1868`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/gui/reftest/parity/pixel_diff_spec.spl
mirror: doc/06_spec/03_system/gui/reftest/parity/pixel_diff_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/gui/reftest/parity/pixel_diff_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/gui/reftest/parity/pixel_diff_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/gui/reftest/parity/pixel_diff_spec.spl:50:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'two empty pictures have ratio 0.0' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/gui/reftest/parity/pixel_diff_spec.spl:58:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'identical pictures (same DrawRect color) have ratio 0.0' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/gui/reftest/parity/pixel_diff_spec.spl:66:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'different pictures (different rect colors) have ratio > 0.0' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
