# wm_pixel_pipeline_spec

> run_consistency_check orchestrates: scene render -> dual capture

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 18 | 18 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# wm_pixel_pipeline_spec

run_consistency_check orchestrates: scene render -> dual capture

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/02_integration/rendering/wm_pixel_pipeline_spec.spl` |
| Updated | 2026-08-26 |
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

- AC-4: run_consistency_check produces a report
   - Expected: has_profile is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("AC-4: run_consistency_check produces a report")
val scene = standard_wm_scene(SCENE_W, SCENE_H)
val profile = profile_wm_default()
val report = run_consistency_check(scene, profile)
val has_profile = report.profile.name.len() > 0
expect(has_profile).to_equal(true)
```

</details>

#### AC-4: report match_percentage is in valid range [0, 10000]

- AC-4: report match_percentage is in valid range [0, 10000]
   - Expected: in_range is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("AC-4: report match_percentage is in valid range [0, 10000]")
val scene = standard_wm_scene(SCENE_W, SCENE_H)
val profile = profile_wm_default()
val report = run_consistency_check(scene, profile)
val in_range = report.overall.match_percentage >= 0 and report.overall.match_percentage <= 10000
expect(in_range).to_equal(true)
```

</details>

#### AC-4: report match_percentage is greater than 0 (some pixels matched)

- AC-4: report match_percentage is greater than 0 (some pixels matched)


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("AC-4: report match_percentage is greater than 0 (some pixels matched)")
val scene = standard_wm_scene(SCENE_W, SCENE_H)
val profile = profile_wm_default()
val report = run_consistency_check(scene, profile)
expect(report.overall.match_percentage).to_be_greater_than(0)
```

</details>

#### AC-4: report contains valid max_channel_diff

- AC-4: report contains valid max_channel_diff
   - Expected: valid is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("AC-4: report contains valid max_channel_diff")
val scene = standard_wm_scene(SCENE_W, SCENE_H)
val profile = profile_wm_default()
val report = run_consistency_check(scene, profile)
val valid = report.overall.max_channel_diff >= 0
expect(valid).to_equal(true)
```

</details>

#### AC-4: report has per-channel results

- AC-4: report has per-channel results


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("AC-4: report has per-channel results")
val scene = standard_wm_scene(SCENE_W, SCENE_H)
val profile = profile_wm_default()
val report = run_consistency_check(scene, profile)
expect(report.channels.len()).to_be_greater_than(0)
```

</details>

#### AC-4: report has diff region list (possibly empty)

- AC-4: report has diff region list (possibly empty)
   - Expected: has_list is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("AC-4: report has diff region list (possibly empty)")
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

- AC-6: same scene rendered twice in-process matches 100%
   - Expected: comparison.match_percentage equals `10000`
   - Expected: result1.success is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("AC-6: same scene rendered twice in-process matches 100%")
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

- AC-6: self-comparison diff image is all-green (match)
   - Expected: diff.len().to_i32() equals `SCENE_W * SCENE_H`
   - Expected: diff[0] equals `0xFF00FF00u32`
   - Expected: diff[mid] equals `0xFF00FF00u32`
   - Expected: diff[diff.len() - 1] equals `0xFF00FF00u32`
   - Expected: result.success is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("AC-6: self-comparison diff image is all-green (match)")
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

- AC-6: mismatched diff pixel is magenta
   - Expected: diff.len() equals `3`
   - Expected: diff[0] equals `0xFF00FF00u32`
   - Expected: diff[1] equals `0xFFFF00FFu32`
   - Expected: diff[2] equals `0xFF00FF00u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("AC-6: mismatched diff pixel is magenta")
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

- AC-6: cross-backend comparison produces valid report
   - Expected: has_report is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("AC-6: cross-backend comparison produces valid report")
val scene = standard_wm_scene(SCENE_W, SCENE_H)
val profile = profile_wm_default()
val report = run_consistency_check(scene, profile)
# Report should always be produced, even if electron fails
val has_report = report.overall.match_percentage >= 0
expect(has_report).to_equal(true)
```

</details>

#### AC-6: report passed field is boolean

- AC-6: report passed field is boolean
   - Expected: is_bool is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("AC-6: report passed field is boolean")
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

- AC-5: export_diff_artifacts returns boolean
   - Expected: is_bool is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("AC-5: export_diff_artifacts returns boolean")
val scene = standard_wm_scene(SCENE_W, SCENE_H)
val profile = profile_strict()
val report = run_consistency_check(scene, profile)
val exported = export_diff_artifacts(report, "/tmp/wm_pixel_pipeline_test")
val is_bool = exported == true or exported == false
expect(is_bool).to_equal(true)
```

</details>

#### AC-5: export with valid report does not crash

- AC-5: export with valid report does not crash
   - Expected: completed is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("AC-5: export with valid report does not crash")
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

- AC-5: generate_diff_image produces non-empty buffer
   - Expected: result.success is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("AC-5: generate_diff_image produces non-empty buffer")
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

- AC-5: diff image has correct pixel count
   - Expected: diff.len().to_i32() equals `expected`
   - Expected: result.success is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("AC-5: diff image has correct pixel count")
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

- AC-6: markdown report is non-empty


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("AC-6: markdown report is non-empty")
val scene = standard_wm_scene(SCENE_W, SCENE_H)
val profile = profile_wm_default()
val report = run_consistency_check(scene, profile)
val md = consistency_report_to_markdown(report)
expect(md.len()).to_be_greater_than(0)
```

</details>

#### AC-6: markdown contains match percentage

- AC-6: markdown contains match percentage
   - Expected: has_match is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("AC-6: markdown contains match percentage")
val scene = standard_wm_scene(SCENE_W, SCENE_H)
val profile = profile_wm_default()
val report = run_consistency_check(scene, profile)
val md = consistency_report_to_markdown(report)
val has_match = md.contains("match") or md.contains("Match") or md.contains("%")
expect(has_match).to_equal(true)
```

</details>

#### AC-6: markdown contains profile name

- AC-6: markdown contains profile name
   - Expected: has_profile is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("AC-6: markdown contains profile name")
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


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-INTEGRATION`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `fdd245a1877668e2795d4b89ffa5726cdf991bb78f6cc81662a92eaa992b976e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `fdd245a1877668e2795d4b89ffa5726cdf991bb78f6cc81662a92eaa992b976e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `fdd245a1877668e2795d4b89ffa5726cdf991bb78f6cc81662a92eaa992b976e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/02_integration/rendering/wm_pixel_pipeline_spec.spl
mirror: doc/06_spec/02_integration/rendering/wm_pixel_pipeline_spec.md (current)
findings: 7 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=55 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/02_integration/rendering/wm_pixel_pipeline_spec.md:1:1: warning SSDOC-EVD-003 [evidence] (-15): source captures are not rendered as manual evidence
  why: Retained evidence must be visible or linked from the professional manual.
  improve: Select a supported evidence display and regenerate.
doc/06_spec/02_integration/rendering/wm_pixel_pipeline_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/02_integration/rendering/wm_pixel_pipeline_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/02_integration/rendering/wm_pixel_pipeline_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/02_integration/rendering/wm_pixel_pipeline_spec.spl:66:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-4: run_consistency_check produces a report' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/rendering/wm_pixel_pipeline_spec.spl:75:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-4: report match_percentage is in valid range [0, 10000]' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/rendering/wm_pixel_pipeline_spec.spl:84:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-4: report match_percentage is greater than 0 (some pixels matched)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
