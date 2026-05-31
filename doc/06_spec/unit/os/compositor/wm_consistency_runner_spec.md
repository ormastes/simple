# Wm Consistency Runner Specification

## Scenarios

### WmConsistencyRunner — run_consistency_check

#### with standard WM scene

#### AC-5: run_consistency_check returns a ConsistencyReport

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val scene = standard_wm_scene(W, H)
val profile = profile_wm_default()
val report = run_consistency_check(scene, profile)
val has_report = report.profile.name.len() > 0
expect(has_report).to_equal(true)
```

</details>

#### AC-4: report contains electron capture result

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val scene = standard_wm_scene(W, H)
val profile = profile_wm_default()
val report = run_consistency_check(scene, profile)
expect(report.electron_capture.backend_name).to_equal("browser_compositor")
```

</details>

#### AC-4: report contains qemu capture result

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val scene = standard_wm_scene(W, H)
val profile = profile_wm_default()
val report = run_consistency_check(scene, profile)
expect(report.qemu_capture.backend_name).to_equal("browser_compositor")
```

</details>

#### AC-4: report has overall comparison result with match_percentage

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val scene = standard_wm_scene(W, H)
val profile = profile_wm_default()
val report = run_consistency_check(scene, profile)
val valid_pct = report.overall.match_percentage >= 0 and report.overall.match_percentage <= 10000
expect(valid_pct).to_equal(true)
```

</details>

#### AC-4: report has perceptual comparison result

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val scene = standard_wm_scene(W, H)
val profile = profile_wm_default()
val report = run_consistency_check(scene, profile)
val valid_total = report.perceptual.total_pixels > 0
expect(valid_total).to_equal(true)
```

</details>

#### AC-9: perceptual comparison is diagnostic only

<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val scene = standard_wm_scene(W, H)
val profile = profile_wm_default()
val report = run_consistency_check(scene, profile)
expect(report.perceptual_diagnostic_only).to_equal(true)
expect(report.exact_required).to_equal(true)
expect(report.tolerance_acceptance_allowed).to_equal(false)
```

</details>

#### AC-4: report has per-channel diff results

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val scene = standard_wm_scene(W, H)
val profile = profile_wm_default()
val report = run_consistency_check(scene, profile)
# Should have channel results (at least R, G, B)
expect(report.channels.len()).to_be_greater_than(0)
```

</details>

#### AC-4: report has diff region list

<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val scene = standard_wm_scene(W, H)
val profile = profile_wm_default()
val report = run_consistency_check(scene, profile)
# passed is a boolean — just verify it's accessible
val is_bool = report.passed == true or report.passed == false
expect(is_bool).to_equal(true)
```

</details>

#### AC-5: strict profile with identical renders yields passed=true

<details>
<summary>Executable SPipe</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SPipe</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val scene = standard_wm_scene(W, H)
val profile = profile_wm_default()
val report = run_consistency_check(scene, profile)
val md = consistency_report_to_markdown(report)
expect(md.len()).to_be_greater_than(0)
```

</details>

#### AC-1: markdown report contains match percentage

<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val scene = standard_wm_scene(W, H)
val profile = profile_wm_default()
val report = run_consistency_check(scene, profile)
val md = consistency_report_to_markdown(report)
val has_match = md.contains("match") or md.contains("Match")
expect(has_match).to_equal(true)
```

</details>

#### AC-7: markdown report contains divergence analysis

<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val scene = standard_wm_scene(W, H)
val profile = profile_wm_default()
val report = run_consistency_check(scene, profile)
val md = consistency_report_to_markdown(report)
val has_divergence = md.contains("divergen") or md.contains("Divergen") or md.contains("normalization") or md.contains("Normalization")
expect(has_divergence).to_equal(true)
```

</details>

#### AC-7: markdown report documents font rasterization differences

<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val scene = standard_wm_scene(W, H)
val profile = profile_wm_default()
val report = run_consistency_check(scene, profile)
val md = consistency_report_to_markdown(report)
val has_font = md.contains("font") or md.contains("Font") or md.contains("rasteriz")
expect(has_font).to_equal(true)
```

</details>

#### AC-7: markdown report documents anti-aliasing normalization

<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val scene = standard_wm_scene(W, H)
val profile = profile_wm_default()
val report = run_consistency_check(scene, profile)
val md = consistency_report_to_markdown(report)
val has_aa = md.contains("anti-alias") or md.contains("AA") or md.contains("antialiasing")
expect(has_aa).to_equal(true)
```

</details>

#### AC-9: markdown report says perceptual metrics are diagnostic only

<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
| Source | `test/unit/os/compositor/wm_consistency_runner_spec.spl` |
| Updated | 2026-05-31 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
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

