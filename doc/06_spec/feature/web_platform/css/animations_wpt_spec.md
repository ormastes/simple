# Animations Wpt Specification

> Tests covering WPT-derived CSS animations subset.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Animations Wpt Specification

## Scenarios

### WPT-derived CSS animations subset

#### CSS animation pure function coverage

#### interpolate_length at t=0.5 returns midpoint

- interpolate_length at t=0.5 returns midpoint
   - Expected: approx(result, 50.0) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("interpolate_length at t=0.5 returns midpoint")
val result = interpolate_length(0.0, 100.0, 0.5)
expect(approx(result, 50.0)).to_equal(true)
```

</details>

#### ease_value linear returns identity

- ease_value linear returns identity
   - Expected: approx(result, 0.5) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("ease_value linear returns identity")
val result = ease_value(0.5, TimingFunction.Linear)
expect(approx(result, 0.5)).to_equal(true)
```

</details>

#### ease_value ease-in starts slow

- ease_value ease-in starts slow
   - Expected: result < 0.5 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("ease_value ease-in starts slow")
val result = ease_value(0.5, TimingFunction.EaseIn)
expect(result < 0.5).to_equal(true)
```

</details>

#### interpolate Number values at midpoint

- interpolate Number values at midpoint
   - Expected: _interp_number_half() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("interpolate Number values at midpoint")
expect(_interp_number_half()).to_equal(true)
```

</details>

#### extract_keyframes parses @keyframes block

- extract_keyframes parses @keyframes block
   - Expected: registry.entries.len() >= 1 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("extract_keyframes parses @keyframes block")
val css = "@keyframes fade { from { opacity: 0; } to { opacity: 1; } }"
val registry = extract_keyframes(css)
expect(registry.entries.len() >= 1).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/feature/web_platform/css/animations_wpt_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering WPT-derived CSS animations subset.
- WPT-derived CSS animations subset

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
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

- Canonical SPipe generation for source `e9b79e41a4cf934845386605021a47daf3fd7945ac514d1aacf57730c4d97b31`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e9b79e41a4cf934845386605021a47daf3fd7945ac514d1aacf57730c4d97b31`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e9b79e41a4cf934845386605021a47daf3fd7945ac514d1aacf57730c4d97b31`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/feature/web_platform/css/animations_wpt_spec.spl
mirror: doc/06_spec/feature/web_platform/css/animations_wpt_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/feature/web_platform/css/animations_wpt_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/feature/web_platform/css/animations_wpt_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/feature/web_platform/css/animations_wpt_spec.spl:31:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'interpolate_length at t=0.5 returns midpoint' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/web_platform/css/animations_wpt_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'ease_value linear returns identity' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/web_platform/css/animations_wpt_spec.spl:43:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'ease_value ease-in starts slow' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
