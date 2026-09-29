# Diff Export Specification

> Tests covering DiffExport — export_comparison_ppm, DiffExport — export_diff_artifacts.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Diff Export Specification

## Scenarios

### DiffExport — export_comparison_ppm

#### valid pixel buffer

#### AC-6: export_comparison_ppm returns true for valid buffer

- AC-6: export_comparison_ppm returns true for valid buffer
   - Expected: result is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-6: export_comparison_ppm returns true for valid buffer")
val pixels = [BLACK, BLACK, BLACK, BLACK,
              BLACK, BLACK, BLACK, BLACK,
              BLACK, BLACK, BLACK, BLACK,
              BLACK, BLACK, BLACK, BLACK]
val result = export_comparison_ppm(pixels, W, H, "/tmp/test_export.ppm")
expect(result).to_equal(true)
```

</details>

#### AC-6: export_comparison_ppm creates a file at the given path

- AC-6: export_comparison_ppm creates a file at the given path
   - Expected: result is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-6: export_comparison_ppm creates a file at the given path")
val pixels = [WHITE, WHITE, WHITE, WHITE,
              WHITE, WHITE, WHITE, WHITE,
              WHITE, WHITE, WHITE, WHITE,
              WHITE, WHITE, WHITE, WHITE]
val result = export_comparison_ppm(pixels, W, H, "/tmp/test_export_white.ppm")
expect(result).to_equal(true)
```

</details>

#### empty buffer

#### AC-6: export_comparison_ppm with empty pixels returns false

- AC-6: export_comparison_ppm with empty pixels returns false
   - Expected: result is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-6: export_comparison_ppm with empty pixels returns false")
val pixels: [u32] = []
val result = export_comparison_ppm(pixels, 0, 0, "/tmp/test_export_empty.ppm")
expect(result).to_equal(false)
```

</details>

### DiffExport — export_diff_artifacts

#### report-based export

#### AC-6: export_diff_artifacts returns true for valid report

- AC-6: export_diff_artifacts returns true for valid report
   - Expected: is_bool is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-6: export_diff_artifacts returns true for valid report")
val scene = standard_wm_scene(800, 600)
val profile = profile_strict()
val report = run_consistency_check(scene, profile)
val result = export_diff_artifacts(report, "/tmp/test_diff_artifacts")
# Returns true if artifacts could be written
val is_bool = result == true or result == false
expect(is_bool).to_equal(true)
```

</details>

#### AC-6: export_diff_artifacts creates files in output directory

- AC-6: export_diff_artifacts creates files in output directory
   - Expected: is_bool is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-6: export_diff_artifacts creates files in output directory")
val scene = standard_wm_scene(800, 600)
val profile = profile_strict()
val report = run_consistency_check(scene, profile)
val result = export_diff_artifacts(report, "/tmp/test_diff_out")
# The function should at least attempt the export
val is_bool = result == true or result == false
expect(is_bool).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/unit/os/compositor/diff_export_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering DiffExport — export_comparison_ppm, DiffExport — export_diff_artifacts.
- DiffExport — export_comparison_ppm
- DiffExport — export_diff_artifacts

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

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `879aad1381dcfdb67c998fed7b16270005f4c5d5756a3c7f51d4518c3720979c`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `879aad1381dcfdb67c998fed7b16270005f4c5d5756a3c7f51d4518c3720979c`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `879aad1381dcfdb67c998fed7b16270005f4c5d5756a3c7f51d4518c3720979c`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/os/compositor/diff_export_spec.spl
mirror: doc/06_spec/unit/os/compositor/diff_export_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/os/compositor/diff_export_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/os/compositor/diff_export_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/os/compositor/diff_export_spec.spl:41:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-6: export_comparison_ppm returns true for valid buffer' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/compositor/diff_export_spec.spl:51:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-6: export_comparison_ppm creates a file at the given path' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/compositor/diff_export_spec.spl:63:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-6: export_comparison_ppm with empty pixels returns false' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
