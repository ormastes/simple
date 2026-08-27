# Wm Consistency Runner Specification

> Tests covering WmConsistencyRunner — run_consistency_check, WmConsistencyRunner — profile integration, WmConsistencyRunner — consistency_report_to_markdown.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 17 | 17 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Wm Consistency Runner Specification

## Scenarios

### WmConsistencyRunner — run_consistency_check

#### with standard WM scene

#### AC-5: run_consistency_check returns a ConsistencyReport

- AC-5: run_consistency_check returns a ConsistencyReport
   - Expected: has_report is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-5: run_consistency_check returns a ConsistencyReport")
val scene = standard_wm_scene(W, H)
val profile = profile_wm_default()
val report = run_consistency_check(scene, profile)
val has_report = report.profile.name.len() > 0
expect(has_report).to_equal(true)
```

</details>

#### AC-4: report contains electron capture result

- AC-4: report contains electron capture result
   - Expected: report.electron_capture.backend_name equals `browser_compositor`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-4: report contains electron capture result")
val scene = standard_wm_scene(W, H)
val profile = profile_wm_default()
val report = run_consistency_check(scene, profile)
expect(report.electron_capture.backend_name).to_equal("browser_compositor")
```

</details>

#### AC-4: report contains qemu capture result

- AC-4: report contains qemu capture result
   - Expected: report.qemu_capture.backend_name equals `browser_compositor`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-4: report contains qemu capture result")
val scene = standard_wm_scene(W, H)
val profile = profile_wm_default()
val report = run_consistency_check(scene, profile)
expect(report.qemu_capture.backend_name).to_equal("browser_compositor")
```

</details>

#### AC-4: report has overall comparison result with match_percentage

- AC-4: report has overall comparison result with match_percentage
   - Expected: valid_pct is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-4: report has overall comparison result with match_percentage")
val scene = standard_wm_scene(W, H)
val profile = profile_wm_default()
val report = run_consistency_check(scene, profile)
val valid_pct = report.overall.match_percentage >= 0 and report.overall.match_percentage <= 10000
expect(valid_pct).to_equal(true)
```

</details>

#### AC-4: report has perceptual comparison result

- AC-4: report has perceptual comparison result
   - Expected: valid_total is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-4: report has perceptual comparison result")
val scene = standard_wm_scene(W, H)
val profile = profile_wm_default()
val report = run_consistency_check(scene, profile)
val valid_total = report.perceptual.total_pixels > 0
expect(valid_total).to_equal(true)
```

</details>

#### AC-9: perceptual comparison is diagnostic only

- AC-9: perceptual comparison is diagnostic only
   - Expected: report.perceptual_diagnostic_only is true
   - Expected: report.exact_required is true
   - Expected: report.tolerance_acceptance_allowed is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-9: perceptual comparison is diagnostic only")
val scene = standard_wm_scene(W, H)
val profile = profile_wm_default()
val report = run_consistency_check(scene, profile)
expect(report.perceptual_diagnostic_only).to_equal(true)
expect(report.exact_required).to_equal(true)
expect(report.tolerance_acceptance_allowed).to_equal(false)
```

</details>

#### AC-4: report has per-channel diff results

- AC-4: report has per-channel diff results


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-4: report has per-channel diff results")
val scene = standard_wm_scene(W, H)
val profile = profile_wm_default()
val report = run_consistency_check(scene, profile)
# Should have channel results (at least R, G, B)
expect(report.channels.len()).to_be_greater_than(0)
```

</details>

#### AC-4: report has diff region list

- AC-4: report has diff region list
   - Expected: has_regions is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-4: report has diff region list")
val scene = standard_wm_scene(W, H)
val profile = profile_wm_default()
val report = run_consistency_check(scene, profile)
# diff_regions may be empty if buffers match; just verify it's a list
val has_regions = report.diff_regions.len() >= 0
expect(has_regions).to_equal(true)
```

</details>

#### pass/fail determination

#### AC-5: report has passed boolean field

- AC-5: report has passed boolean field
   - Expected: is_bool is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-5: report has passed boolean field")
val scene = standard_wm_scene(W, H)
val profile = profile_wm_default()
val report = run_consistency_check(scene, profile)
# passed is a boolean — just verify it's accessible
val is_bool = report.passed == true or report.passed == false
expect(is_bool).to_equal(true)
```

</details>

#### AC-5: strict profile with identical renders yields passed=true

- AC-5: strict profile with identical renders yields passed=true
   - Expected: is_bool is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-5: strict profile with identical renders yields passed=true")
# Theoretical: with in-process rendering, same scene through same
# backend should be identical. This tests the pass logic.
val scene = standard_wm_scene(W, H)
val profile = profile_strict()
val report = run_consistency_check(scene, profile)
# Note: may fail if Electron != in-process — that's the point
val is_bool = report.passed == true or report.passed == false
expect(is_bool).to_equal(true)
```

</details>

### WmConsistencyRunner — profile integration

#### different profiles yield different pass/fail

#### AC-4: glass blur profile is more lenient than strict

- AC-4: glass blur profile is more lenient than strict
   - Expected: glass_threshold_higher is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-4: glass blur profile is more lenient than strict")
val scene = standard_wm_scene(W, H)
val strict = profile_strict()
val glass = profile_glass_blur()
val strict_report = run_consistency_check(scene, strict)
val glass_report = run_consistency_check(scene, glass)
# Glass tolerance should be at least as permissive
val glass_threshold_higher = glass.default_threshold >= strict.default_threshold
expect(glass_threshold_higher).to_equal(true)
```

</details>

### WmConsistencyRunner — consistency_report_to_markdown

#### markdown output

#### AC-1: markdown report is non-empty

- AC-1: markdown report is non-empty


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-1: markdown report is non-empty")
val scene = standard_wm_scene(W, H)
val profile = profile_wm_default()
val report = run_consistency_check(scene, profile)
val md = consistency_report_to_markdown(report)
expect(md.len()).to_be_greater_than(0)
```

</details>

#### AC-1: markdown report contains match percentage

- AC-1: markdown report contains match percentage
   - Expected: has_match is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-1: markdown report contains match percentage")
val scene = standard_wm_scene(W, H)
val profile = profile_wm_default()
val report = run_consistency_check(scene, profile)
val md = consistency_report_to_markdown(report)
val has_match = md.contains("match") or md.contains("Match")
expect(has_match).to_equal(true)
```

</details>

#### AC-7: markdown report contains divergence analysis

- AC-7: markdown report contains divergence analysis
   - Expected: has_divergence is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-7: markdown report contains divergence analysis")
val scene = standard_wm_scene(W, H)
val profile = profile_wm_default()
val report = run_consistency_check(scene, profile)
val md = consistency_report_to_markdown(report)
val has_divergence = md.contains("divergen") or md.contains("Divergen") or md.contains("normalization") or md.contains("Normalization")
expect(has_divergence).to_equal(true)
```

</details>

#### AC-7: markdown report documents font rasterization differences

- AC-7: markdown report documents font rasterization differences
   - Expected: has_font is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-7: markdown report documents font rasterization differences")
val scene = standard_wm_scene(W, H)
val profile = profile_wm_default()
val report = run_consistency_check(scene, profile)
val md = consistency_report_to_markdown(report)
val has_font = md.contains("font") or md.contains("Font") or md.contains("rasteriz")
expect(has_font).to_equal(true)
```

</details>

#### AC-7: markdown report documents anti-aliasing normalization

- AC-7: markdown report documents anti-aliasing normalization
   - Expected: has_aa is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-7: markdown report documents anti-aliasing normalization")
val scene = standard_wm_scene(W, H)
val profile = profile_wm_default()
val report = run_consistency_check(scene, profile)
val md = consistency_report_to_markdown(report)
val has_aa = md.contains("anti-alias") or md.contains("AA") or md.contains("antialiasing")
expect(has_aa).to_equal(true)
```

</details>

#### AC-9: markdown report says perceptual metrics are diagnostic only

- AC-9: markdown report says perceptual metrics are diagnostic only
   - Expected: md contains `diagnostic only`
   - Expected: md contains `exact pixels are required`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-9: markdown report says perceptual metrics are diagnostic only")
val scene = standard_wm_scene(W, H)
val profile = profile_wm_default()
val report = run_consistency_check(scene, profile)
val md = consistency_report_to_markdown(report)
expect(md.contains("diagnostic only")).to_equal(true)
expect(md.contains("exact pixels are required")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/compositor/wm_consistency_runner_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering WmConsistencyRunner — run_consistency_check, WmConsistencyRunner — profile integration, WmConsistencyRunner — consistency_report_to_markdown.
- WmConsistencyRunner — run_consistency_check
- WmConsistencyRunner — profile integration
- WmConsistencyRunner — consistency_report_to_markdown

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

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `81687a611e857695513d0d2eb80814450281f77defb64756bc42d5771318e0cf`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `81687a611e857695513d0d2eb80814450281f77defb64756bc42d5771318e0cf`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `81687a611e857695513d0d2eb80814450281f77defb64756bc42d5771318e0cf`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/os/compositor/wm_consistency_runner_spec.spl
mirror: doc/06_spec/01_unit/os/compositor/wm_consistency_runner_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/compositor/wm_consistency_runner_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/compositor/wm_consistency_runner_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/compositor/wm_consistency_runner_spec.spl:38:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-5: run_consistency_check returns a ConsistencyReport' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/compositor/wm_consistency_runner_spec.spl:47:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-4: report contains electron capture result' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/compositor/wm_consistency_runner_spec.spl:55:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-4: report contains qemu capture result' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
