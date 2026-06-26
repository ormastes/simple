# Electron Simple Web layout manifest evidence

> Validates the manifest-level wrapper behavior around tracked divergence policies and resumable evidence after bounded runs.

<!-- sdn-diagram:id=electron_simple_web_layout_manifest_evidence_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=electron_simple_web_layout_manifest_evidence_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

electron_simple_web_layout_manifest_evidence_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=electron_simple_web_layout_manifest_evidence_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Electron Simple Web layout manifest evidence

Validates the manifest-level wrapper behavior around tracked divergence policies and resumable evidence after bounded runs.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Requirements | N/A |
| Plan | doc/03_plan/sys_test/html_css_spec_traceability.md |
| Design | doc/07_guide/ui/pixel_comparison_guide.md |
| Source | `test/03_system/check/electron_simple_web_layout_manifest_evidence_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Validates the manifest-level wrapper behavior around tracked divergence policies
and resumable evidence after bounded runs.

**Requirements:** N/A
**Plan:** doc/03_plan/sys_test/html_css_spec_traceability.md
**Design:** doc/07_guide/ui/pixel_comparison_guide.md

## Syntax

```sh
SIMPLE_LIB=src bin/simple test test/03_system/check/electron_simple_web_layout_manifest_evidence_spec.spl --mode=interpreter --clean
```

## Acceptance

- `track-*-divergence` manifest policies are counted as tracked when the case
  emits divergent or pass evidence without blur/tolerance.
- Resumable manifest runs reuse complete case evidence when scene and dimensions
  match, so a bounded rerun can continue without repeating completed captures.

## Scenarios

### Electron Simple Web layout manifest evidence

#### counts declared tracked divergence policies as tracked

<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-electron-simple-web-layout-manifest-tracked-policy"
val command = "rm -rf " + root + " && mkdir -p " + root + "/fixture && " +
    "printf 'tracked_case|fixture-scene|96|64|track-css-flex-column-divergence|tracked fixture\\nexact_case|fixture-exact|96|64|exact|exact fixture\\n' > " + root + "/manifest.txt && " +
    "printf '#!/bin/sh\\nmkdir -p \"$BUILD_DIR\"\\ncase \"$ELECTRON_BITMAP_SCENE\" in\\nfixture-scene) printf \"electron_simple_web_layout_status=divergent\\\\nelectron_simple_web_layout_reason=checksum-mismatch\\\\nelectron_simple_web_layout_scene=$ELECTRON_BITMAP_SCENE\\\\nelectron_simple_web_layout_width=$ELECTRON_BITMAP_WIDTH\\\\nelectron_simple_web_layout_height=$ELECTRON_BITMAP_HEIGHT\\\\nelectron_simple_web_layout_mismatch_count=7\\\\nelectron_simple_web_layout_blur_or_tolerance_used=false\\\\nelectron_simple_web_layout_exit_code=2\\\\n\" > \"$BUILD_DIR/evidence.env\"; exit 1;;\\n*) printf \"electron_simple_web_layout_status=pass\\\\nelectron_simple_web_layout_reason=pass\\\\nelectron_simple_web_layout_scene=$ELECTRON_BITMAP_SCENE\\\\nelectron_simple_web_layout_width=$ELECTRON_BITMAP_WIDTH\\\\nelectron_simple_web_layout_height=$ELECTRON_BITMAP_HEIGHT\\\\nelectron_simple_web_layout_mismatch_count=0\\\\nelectron_simple_web_layout_blur_or_tolerance_used=false\\\\nelectron_simple_web_layout_exit_code=0\\\\n\" > \"$BUILD_DIR/evidence.env\";;\\nesac\\n' > " + root + "/fixture/bitmap.sh && " +
    "MANIFEST_PATH=" + root + "/manifest.txt ELECTRON_LAYOUT_MANIFEST_BITMAP_SCRIPT=" + root + "/fixture/bitmap.sh BUILD_DIR=" + root + "/out REPORT_PATH=" + root + "/report.md sh scripts/check/check-electron-simple-web-layout-manifest-evidence.shs"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val evidence = file_read(root + "/out/evidence.env")
expect(evidence).to_contain("electron_simple_web_layout_manifest_status=pass")
expect(evidence).to_contain("electron_simple_web_layout_manifest_case_count=2")
expect(evidence).to_contain("electron_simple_web_layout_manifest_pass_count=1")
expect(evidence).to_contain("electron_simple_web_layout_manifest_tracked_count=1")
expect(evidence).to_contain("electron_simple_web_layout_manifest_fail_count=0")
expect(evidence).to_contain("electron_simple_web_layout_manifest_tracked_case_policy=track-css-flex-column-divergence")
```

</details>

#### reuses matching case evidence when resume is enabled

<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-electron-simple-web-layout-manifest-resume"
val command = "rm -rf " + root + " && mkdir -p " + root + "/fixture " + root + "/out/first_case && " +
    "printf 'first_case|fixture-first|96|64|exact|first fixture\\nsecond_case|fixture-second|96|64|exact|second fixture\\n' > " + root + "/manifest.txt && " +
    "printf 'electron_simple_web_layout_status=pass\\nelectron_simple_web_layout_reason=pass\\nelectron_simple_web_layout_scene=fixture-first\\nelectron_simple_web_layout_width=96\\nelectron_simple_web_layout_height=64\\nelectron_simple_web_layout_mismatch_count=0\\nelectron_simple_web_layout_blur_or_tolerance_used=false\\nelectron_simple_web_layout_exit_code=0\\n' > " + root + "/out/first_case/evidence.env && " +
    "printf '#!/bin/sh\\nmkdir -p \"$BUILD_DIR\"\\nprintf \"electron_simple_web_layout_status=pass\\\\nelectron_simple_web_layout_reason=pass\\\\nelectron_simple_web_layout_scene=$ELECTRON_BITMAP_SCENE\\\\nelectron_simple_web_layout_width=$ELECTRON_BITMAP_WIDTH\\\\nelectron_simple_web_layout_height=$ELECTRON_BITMAP_HEIGHT\\\\nelectron_simple_web_layout_mismatch_count=0\\\\nelectron_simple_web_layout_blur_or_tolerance_used=false\\\\nelectron_simple_web_layout_exit_code=0\\\\n\" > \"$BUILD_DIR/evidence.env\"\\n' > " + root + "/fixture/bitmap.sh && " +
    "ELECTRON_LAYOUT_MANIFEST_RESUME=1 MANIFEST_PATH=" + root + "/manifest.txt ELECTRON_LAYOUT_MANIFEST_BITMAP_SCRIPT=" + root + "/fixture/bitmap.sh BUILD_DIR=" + root + "/out REPORT_PATH=" + root + "/report.md sh scripts/check/check-electron-simple-web-layout-manifest-evidence.shs"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val evidence = file_read(root + "/out/evidence.env")
expect(evidence).to_contain("electron_simple_web_layout_manifest_status=pass")
expect(evidence).to_contain("electron_simple_web_layout_manifest_case_count=2")
expect(evidence).to_contain("electron_simple_web_layout_manifest_pass_count=2")
expect(evidence).to_contain("electron_simple_web_layout_manifest_fail_count=0")
expect(evidence).to_contain("electron_simple_web_layout_manifest_first_case_reused=true")
expect(evidence).to_contain("electron_simple_web_layout_manifest_second_case_reused=false")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** [doc/03_plan/sys_test/html_css_spec_traceability.md](doc/03_plan/sys_test/html_css_spec_traceability.md)
- **Design:** [doc/07_guide/ui/pixel_comparison_guide.md](doc/07_guide/ui/pixel_comparison_guide.md)


</details>
