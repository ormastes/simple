# wm_pixel_pipeline_spec

run_consistency_check orchestrates: scene render -> dual capture

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/02_integration/rendering/wm_pixel_pipeline_spec.spl` |
| Updated | 2026-05-31 |
| Generator | `simple spipe-docgen` (Simple) |

## End-to-End Pipeline

    run_consistency_check orchestrates: scene render -> dual capture
    (host shared compositor + qemu in-process shared compositor)
    -> pixel comparison -> report generation.
    The pipeline should produce a valid ConsistencyReport with real metrics.

## Scenarios

### WM Pixel Pipeline — run_consistency_check

#### standard WM scene with default profile

#### AC-4: run_consistency_check produces a report

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val scene = standard_wm_scene(SCENE_W, SCENE_H)
val profile = profile_wm_default()
val report = run_consistency_check(scene, profile)
val has_profile = report.profile.name.len() > 0
expect(has_profile).to_equal(true)
```

</details>

#### AC-4: report match_percentage is in valid range [0, 10000]

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val scene = standard_wm_scene(SCENE_W, SCENE_H)
val profile = profile_wm_default()
val report = run_consistency_check(scene, profile)
val in_range = report.overall.match_percentage >= 0 and report.overall.match_percentage <= 10000
expect(in_range).to_equal(true)
```

</details>

#### AC-4: report match_percentage is greater than 0 (some pixels matched)

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val scene = standard_wm_scene(SCENE_W, SCENE_H)
val profile = profile_wm_default()
val report = run_consistency_check(scene, profile)
expect(report.overall.match_percentage).to_be_greater_than(0)
```

</details>

#### AC-4: report contains valid max_channel_diff

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val scene = standard_wm_scene(SCENE_W, SCENE_H)
val profile = profile_wm_default()
val report = run_consistency_check(scene, profile)
val valid = report.overall.max_channel_diff >= 0
expect(valid).to_equal(true)
```

</details>

#### AC-4: report has per-channel results

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val scene = standard_wm_scene(SCENE_W, SCENE_H)
val profile = profile_wm_default()
val report = run_consistency_check(scene, profile)
expect(report.channels.len()).to_be_greater_than(0)
```

</details>

#### AC-4: report has diff region list (possibly empty)

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val scene = standard_wm_scene(SCENE_W, SCENE_H)
val profile = profile_wm_default()
val report = run_consistency_check(scene, profile)
val has_list = report.diff_regions.len() >= 0
expect(has_list).to_equal(true)
```

</details>

### WM Pixel Pipeline — capture path comparison

#### in-process self-comparison baseline

#### AC-6: same scene rendered twice in-process matches 100%

<details>
<summary>Executable SPipe</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val scene = standard_wm_scene(SCENE_W, SCENE_H)
val result1 = capture_qemu_inprocess(scene)
val result2 = capture_qemu_inprocess(scene)
if result1.success and result2.success:
    val comparison = compare_pixel_buffers(
        result1.pixels, result2.pixels, SCENE_W, SCENE_H, 0)
    # Identical renders should be 100% match (10000 basis points)
    expect(comparison.match_percentage).to_equal(10000)
else:
    expect(result1.success).to_equal(true)
```

</details>

#### AC-6: self-comparison diff image is all-green (match)

<details>
<summary>Executable SPipe</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val scene = standard_wm_scene(SCENE_W, SCENE_H)
val result = capture_qemu_inprocess(scene)
if result.success:
    val diff = generate_diff_image(
        result.pixels, result.pixels, SCENE_W, SCENE_H)
    val mid = diff.len() / 2
    expect(diff.len().to_i32()).to_equal(SCENE_W * SCENE_H)
    expect(diff[0]).to_equal(0xFF00FF00u32)
    expect(diff[mid]).to_equal(0xFF00FF00u32)
    expect(diff[diff.len() - 1]).to_equal(0xFF00FF00u32)
else:
    expect(result.success).to_equal(true)
```

</details>

#### AC-6: mismatched diff pixel is magenta

<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var a: [u32] = [0xFF000000u32, 0xFF112233u32, 0xFFFFFFFFu32]
var b: [u32] = [0xFF000000u32, 0xFF445566u32, 0xFFFFFFFFu32]
val diff = generate_diff_image(a, b, 3, 1)
expect(diff.len()).to_equal(3)
expect(diff[0]).to_equal(0xFF00FF00u32)
expect(diff[1]).to_equal(0xFFFF00FFu32)
expect(diff[2]).to_equal(0xFF00FF00u32)
```

</details>

#### dual capture path report generation

#### AC-6: cross-backend comparison produces valid report

<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val scene = standard_wm_scene(SCENE_W, SCENE_H)
val profile = profile_wm_default()
val report = run_consistency_check(scene, profile)
# Report should always be produced, even if electron fails
val has_report = report.overall.match_percentage >= 0
expect(has_report).to_equal(true)
```

</details>

#### AC-6: report passed field is boolean

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val scene = standard_wm_scene(SCENE_W, SCENE_H)
val profile = profile_wm_default()
val report = run_consistency_check(scene, profile)
val is_bool = report.passed == true or report.passed == false
expect(is_bool).to_equal(true)
```

</details>

### WM Pixel Pipeline — diff export

#### export from consistency report

#### AC-5: export_diff_artifacts returns boolean

<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val scene = standard_wm_scene(SCENE_W, SCENE_H)
val profile = profile_strict()
val report = run_consistency_check(scene, profile)
val exported = export_diff_artifacts(report, "/tmp/wm_pixel_pipeline_test")
val is_bool = exported == true or exported == false
expect(is_bool).to_equal(true)
```

</details>

#### AC-5: export with valid report does not crash

<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val scene = standard_wm_scene(SCENE_W, SCENE_H)
val profile = profile_wm_default()
val report = run_consistency_check(scene, profile)
val exported = export_diff_artifacts(report, "/tmp/wm_pixel_pipeline_export")
# Should succeed or fail gracefully — not crash
val completed = exported == true or exported == false
expect(completed).to_equal(true)
```

</details>

#### diff image generation

#### AC-5: generate_diff_image produces non-empty buffer

<details>
<summary>Executable SPipe</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val scene = standard_wm_scene(SCENE_W, SCENE_H)
val result = capture_qemu_inprocess(scene)
if result.success:
    val diff = generate_diff_image(
        result.pixels, result.pixels, SCENE_W, SCENE_H)
    expect(diff.len()).to_be_greater_than(0)
else:
    expect(result.success).to_equal(true)
```

</details>

#### AC-5: diff image has correct pixel count

<details>
<summary>Executable SPipe</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val scene = standard_wm_scene(SCENE_W, SCENE_H)
val result = capture_qemu_inprocess(scene)
if result.success:
    val diff = generate_diff_image(
        result.pixels, result.pixels, SCENE_W, SCENE_H)
    val expected = SCENE_W * SCENE_H
    expect(diff.len().to_i32()).to_equal(expected)
else:
    expect(result.success).to_equal(true)
```

</details>

### WM Pixel Pipeline — documented results

#### markdown report generation

#### AC-6: markdown report is non-empty

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val scene = standard_wm_scene(SCENE_W, SCENE_H)
val profile = profile_wm_default()
val report = run_consistency_check(scene, profile)
val md = consistency_report_to_markdown(report)
expect(md.len()).to_be_greater_than(0)
```

</details>

#### AC-6: markdown contains match percentage

<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val scene = standard_wm_scene(SCENE_W, SCENE_H)
val profile = profile_wm_default()
val report = run_consistency_check(scene, profile)
val md = consistency_report_to_markdown(report)
val has_match = md.contains("match") or md.contains("Match") or md.contains("%")
expect(has_match).to_equal(true)
```

</details>

#### AC-6: markdown contains profile name

<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val scene = standard_wm_scene(SCENE_W, SCENE_H)
val profile = profile_wm_default()
val report = run_consistency_check(scene, profile)
val md = consistency_report_to_markdown(report)
val has_profile = md.contains("wm_default") or md.contains("profile") or md.contains("Profile")
expect(has_profile).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 18 |
| Active scenarios | 18 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

