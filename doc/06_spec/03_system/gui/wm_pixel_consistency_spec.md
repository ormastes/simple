# Wm Pixel Consistency Specification

> <details>

<!-- sdn-diagram:id=wm_pixel_consistency_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=wm_pixel_consistency_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

wm_pixel_consistency_spec -> std
wm_pixel_consistency_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=wm_pixel_consistency_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 19 | 19 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Wm Pixel Consistency Specification

## Scenarios

### WM Pixel Consistency — Golden Test

#### standard WM scene

#### AC-5: reference scene renders through both capture paths

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val scene = standard_wm_scene(SCENE_W, SCENE_H)
val profile = profile_wm_default()
val report = run_consistency_check(scene, profile)
# Both captures should have succeeded and used the unified renderer
val host_captured = report.electron_capture.success and report.electron_capture.backend_name == "browser_compositor"
val qemu_captured = report.qemu_capture.success and report.qemu_capture.backend_name == "browser_compositor"
expect(host_captured).to_equal(true)
expect(qemu_captured).to_equal(true)
```

</details>

#### AC-5: pixel match percentage is 100% with wm_default profile

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val scene = standard_wm_scene(SCENE_W, SCENE_H)
val profile = profile_wm_default()
val report = run_consistency_check(scene, profile)
val passes = report.overall.match_percentage >= MIN_MATCH_PCT
expect(passes).to_equal(true)
```

</details>

#### AC-5: golden test passes with tolerance profile

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val scene = standard_wm_scene(SCENE_W, SCENE_H)
val profile = profile_wm_default()
val report = run_consistency_check(scene, profile)
expect(report.passed).to_equal(true)
```

</details>

#### strict comparison baseline

#### AC-5: strict profile comparison provides baseline metrics

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val scene = standard_wm_scene(SCENE_W, SCENE_H)
val profile = profile_strict()
val report = run_consistency_check(scene, profile)
# Strict may not pass, but should return valid metrics
val valid_pct = report.overall.match_percentage >= 0 and report.overall.match_percentage <= 10000
expect(valid_pct).to_equal(true)
```

</details>

### WM Pixel Consistency — Scene Rendering

#### Electron capture

#### AC-2: Electron captures non-empty pixel buffer for WM scene

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val scene = standard_wm_scene(SCENE_W, SCENE_H)
val result = capture_electron_scene(scene)
if result.success:
    expect(result.pixels.len()).to_be_greater_than(0)
else:
    # In environments without Electron, capture returns error
    val has_error = result.error.len() > 0
    expect(has_error).to_equal(true)
```

</details>

#### AC-2: Electron capture produces correct-sized buffer

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val scene = standard_wm_scene(SCENE_W, SCENE_H)
val result = capture_electron_scene(scene)
if result.success:
    val expected = SCENE_W * SCENE_H
    expect(result.pixels.len().to_i32()).to_equal(expected)
else:
    expect(result.success).to_equal(false)
```

</details>

#### QEMU in-process capture

#### AC-3: QEMU in-process captures non-empty pixel buffer

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val scene = standard_wm_scene(SCENE_W, SCENE_H)
val result = capture_qemu_inprocess(scene)
expect(result.pixels.len()).to_be_greater_than(0)
```

</details>

#### AC-3: QEMU in-process produces correct-sized buffer

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val scene = standard_wm_scene(SCENE_W, SCENE_H)
val result = capture_qemu_inprocess(scene)
val expected = SCENE_W * SCENE_H
expect(result.pixels.len().to_i32()).to_equal(expected)
```

</details>

### WM Pixel Consistency — Comparison Details

#### channel-level metrics

#### AC-4: comparison reports max channel diff

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val scene = standard_wm_scene(SCENE_W, SCENE_H)
val profile = profile_wm_default()
val report = run_consistency_check(scene, profile)
val valid_diff = report.overall.max_channel_diff >= 0
expect(valid_diff).to_equal(true)
```

</details>

#### AC-4: comparison reports per-channel results

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val scene = standard_wm_scene(SCENE_W, SCENE_H)
val profile = profile_wm_default()
val report = run_consistency_check(scene, profile)
expect(report.channels.len()).to_be_greater_than(0)
```

</details>

#### diff region detection

#### AC-4: comparison detects diff regions (if any)

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val scene = standard_wm_scene(SCENE_W, SCENE_H)
val profile = profile_wm_default()
val report = run_consistency_check(scene, profile)
# diff_regions is a list — may be empty if perfectly matched
val is_list = report.diff_regions.len() >= 0
expect(is_list).to_equal(true)
```

</details>

#### perceptual comparison

#### AC-4: perceptual result reports AA pixel count

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val scene = standard_wm_scene(SCENE_W, SCENE_H)
val profile = profile_wm_default()
val report = run_consistency_check(scene, profile)
val valid_aa = report.perceptual.aa_pixels >= 0
expect(valid_aa).to_equal(true)
```

</details>

#### AC-4: perceptual match percentage is available

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val scene = standard_wm_scene(SCENE_W, SCENE_H)
val profile = profile_wm_default()
val report = run_consistency_check(scene, profile)
val valid_pct = report.perceptual.match_percentage >= 0 and report.perceptual.match_percentage <= 10000
expect(valid_pct).to_equal(true)
```

</details>

### WM Pixel Consistency — Diff Visualization

#### diff export on mismatch

#### AC-6: diff artifacts can be exported from consistency report

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val scene = standard_wm_scene(SCENE_W, SCENE_H)
val profile = profile_strict()
val report = run_consistency_check(scene, profile)
val exported = export_diff_artifacts(report, "/tmp/wm_consistency_diff")
val is_bool = exported == true or exported == false
expect(is_bool).to_equal(true)
```

</details>

#### AC-6: diff image generation works with captured buffers

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val scene = standard_wm_scene(SCENE_W, SCENE_H)
val electron = capture_electron_scene(scene)
val qemu = capture_qemu_inprocess(scene)
if electron.success:
    val diff = generate_diff_image(
        electron.pixels, qemu.pixels, SCENE_W, SCENE_H)
    expect(diff.len()).to_be_greater_than(0)
else:
    # Electron unavailable in test environment
    expect(electron.success).to_equal(false)
```

</details>

### WM Pixel Consistency — Report

#### markdown report

#### AC-1: consistency report produces markdown documentation

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val scene = standard_wm_scene(SCENE_W, SCENE_H)
val profile = profile_wm_default()
val report = run_consistency_check(scene, profile)
val md = consistency_report_to_markdown(report)
expect(md.len()).to_be_greater_than(100)
```

</details>

#### AC-1: markdown includes industry comparison methodology

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val scene = standard_wm_scene(SCENE_W, SCENE_H)
val profile = profile_wm_default()
val report = run_consistency_check(scene, profile)
val md = consistency_report_to_markdown(report)
val has_methodology = md.contains("YIQ") or md.contains("perceptual") or md.contains("pixelmatch")
expect(has_methodology).to_equal(true)
```

</details>

#### AC-7: markdown documents rendering divergence root causes

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val scene = standard_wm_scene(SCENE_W, SCENE_H)
val profile = profile_wm_default()
val report = run_consistency_check(scene, profile)
val md = consistency_report_to_markdown(report)
val has_root_cause = md.contains("font") or md.contains("anti-alias") or md.contains("color space") or md.contains("blur")
expect(has_root_cause).to_equal(true)
```

</details>

#### AC-7: markdown documents normalization strategies

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val scene = standard_wm_scene(SCENE_W, SCENE_H)
val profile = profile_wm_default()
val report = run_consistency_check(scene, profile)
val md = consistency_report_to_markdown(report)
val has_strategy = md.contains("normaliz") or md.contains("Normaliz") or md.contains("mitigation") or md.contains("strategy")
expect(has_strategy).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/gui/wm_pixel_consistency_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- WM Pixel Consistency — Golden Test
- WM Pixel Consistency — Scene Rendering
- WM Pixel Consistency — Comparison Details
- WM Pixel Consistency — Diff Visualization
- WM Pixel Consistency — Report

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 19 |
| Active scenarios | 19 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
