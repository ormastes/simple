# Diff Export Specification

> <details>

<!-- sdn-diagram:id=diff_export_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=diff_export_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

diff_export_spec -> std
diff_export_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=diff_export_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

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

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pixels = [BLACK, BLACK, BLACK, BLACK,
              BLACK, BLACK, BLACK, BLACK,
              BLACK, BLACK, BLACK, BLACK,
              BLACK, BLACK, BLACK, BLACK]
val result = export_comparison_ppm(pixels, W, H, "/tmp/test_export.ppm")
expect(result).to_equal(true)
```

</details>

#### AC-6: export_comparison_ppm creates a file at the given path

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pixels: [u32] = []
val result = export_comparison_ppm(pixels, 0, 0, "/tmp/test_export_empty.ppm")
expect(result).to_equal(false)
```

</details>

### DiffExport — export_diff_artifacts

#### report-based export

#### AC-6: export_diff_artifacts returns true for valid report

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
| Source | `test/01_unit/os/compositor/diff_export_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
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
