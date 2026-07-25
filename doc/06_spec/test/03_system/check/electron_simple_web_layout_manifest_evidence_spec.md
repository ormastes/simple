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
| 6 | 6 | 0 | 0 |

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
| Plan | doc/03_plan/sys_test/simple_web_browser_production_hardening.md |
| Design | doc/07_guide/ui/pixel_comparison_guide.md |
| Research | N/A |
| Source | `test/03_system/check/electron_simple_web_layout_manifest_evidence_spec.spl` |
| Updated | 2026-06-27 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Validates the manifest-level wrapper behavior around tracked divergence policies
and resumable evidence after bounded runs.

**Requirements:** N/A
**Research:** N/A
**Plan:** doc/03_plan/sys_test/simple_web_browser_production_hardening.md
**Design:** doc/07_guide/ui/pixel_comparison_guide.md

## Syntax

```sh
SIMPLE_LIB=src bin/simple test test/03_system/check/electron_simple_web_layout_manifest_evidence_spec.spl --mode=interpreter --clean
```

## Acceptance

- `track-*` manifest policies are counted as tracked when the case
  emits divergent or pass evidence without blur/tolerance.
- Resumable manifest runs reuse complete case evidence when scene and dimensions
  match, so a bounded rerun can continue without repeating completed captures.
- When every manifest case reports a host dependency failure such as missing
  Electron, the manifest is `unavailable` instead of a renderer mismatch
  failure.
- The standalone manifest wrapper resolves and exports a self-hosted Simple
  launcher for nested bitmap cases, and rejects Rust seed drivers explicitly.

## Operator Notes

The fixture bitmap script writes the same `evidence.env` fields produced by the
real Electron bitmap wrapper. The first scenario proves that tracked policy rows
are accepted only when they avoid blur/tolerance and either preserve a clean
pass or record an intentional divergent mismatch. The second scenario proves
that resume mode trusts only matching scene and dimensions before reusing
previous case evidence.

These scenarios do not claim browser pixel parity by themselves. They protect
the manifest aggregator that production parity uses after the expensive
Electron captures have already written per-case evidence.

## Coverage Matrix

Tracked divergent policy row:

- Manifest policy: `track-css-flex-column-divergence`.
- Fixture evidence status: `divergent`.
- Fixture mismatch count: positive.
- Fixture blur/tolerance flag: `false`.
- Expected aggregate result: the row contributes to `tracked_count`, not
  `fail_count`.

Tracked pass policy row:

- Manifest policy: `track-compositor-opacity-rounding`.
- Fixture evidence status: `pass`.
- Fixture mismatch count: `0`.
- Fixture blur/tolerance flag: `false`.
- Expected aggregate result: the row contributes to `tracked_count`, proving
  tracked policies are not limited to names ending in `-divergence`.

Exact pass policy row:

- Manifest policy: `exact`.
- Fixture evidence status: `pass`.
- Fixture mismatch count: `0`.
- Fixture blur/tolerance flag: `false`.
- Expected aggregate result: the row contributes to `pass_count`.

Resume matched row:

- Previous evidence scene matches the manifest scene.
- Previous evidence width matches the manifest width.
- Previous evidence height matches the manifest height.
- Expected aggregate result: `_reused=true` for that case.

Resume new row:

- No previous evidence exists for the case.
- The fixture bitmap wrapper is invoked once for the case.
- Expected aggregate result: `_reused=false` for that case.

## Failure Modes Protected

The manifest wrapper must not demote a deliberate tracked policy to a hard
failure just because the policy name does not end with `-divergence`.

The manifest wrapper must not count a tracked policy as exact parity; tracked
rows are reported separately so the production report can distinguish clean
passes from accepted renderer-difference rows.

The manifest wrapper must not accept rows that used blur or tolerance. Those
rows are intentionally excluded from tracked acceptance because they are not
byte-exact evidence.

The manifest wrapper must not rerun a completed case in resume mode when scene,
width, and height still match. This keeps bounded production runs from losing
useful progress after a timeout.

The manifest wrapper must still run missing cases in resume mode. Reuse is
case-local and does not turn the entire manifest into a stale cached result.

The manifest wrapper must not report a full manifest of missing Electron cases
as renderer failures. That failure class blocks host setup, not Simple Web
layout correctness.

The standalone manifest wrapper must not depend on the production parity wrapper
to select a usable Simple binary. It records the selected binary and exports it
to each nested bitmap case.

## Manual Reproduction

Run the focused spec with:

```sh
SIMPLE_LIB=src bin/simple test test/03_system/check/electron_simple_web_layout_manifest_evidence_spec.spl --mode=interpreter --clean
```

The first scenario creates a temporary manifest with three rows and a fixture
bitmap script that emits deterministic evidence. The expected aggregate is one
exact pass, two tracked rows, and zero failures.

The second scenario seeds one previous evidence file, runs the manifest wrapper
with `ELECTRON_LAYOUT_MANIFEST_RESUME=1`, and expects the first case to be
reused while the second case is freshly captured by the fixture script.

Production parity uses the same manifest wrapper through:

```sh
sh scripts/check/check-production-gui-web-renderer-parity-evidence.shs
```

When production parity fails, read the promoted
`production_gui_web_renderer_parity_layout_manifest_*` fields first. They show
whether the layout manifest failed, timed out, reused cases, or produced partial
counts from completed per-case evidence.

## Scenarios

### Electron Simple Web layout manifest evidence

#### counts declared tracked policies as tracked

<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-electron-simple-web-layout-manifest-tracked-policy"
val command = "rm -rf " + root + " && mkdir -p " + root + "/fixture && " +
    "printf 'tracked_case|fixture-scene|96|64|track-css-flex-column-divergence|tracked fixture\\nopacity_case|fixture-opacity|96|64|track-compositor-opacity-rounding|opacity tracked fixture\\nexact_case|fixture-exact|96|64|exact|exact fixture\\n' > " + root + "/manifest.txt && " +
    "printf '#!/bin/sh\\nmkdir -p \"$BUILD_DIR\"\\ncase \"$ELECTRON_BITMAP_SCENE\" in\\nfixture-scene) printf \"electron_simple_web_layout_status=divergent\\\\nelectron_simple_web_layout_reason=text-raster-mismatch\\\\nelectron_simple_web_layout_scene=$ELECTRON_BITMAP_SCENE\\\\nelectron_simple_web_layout_width=$ELECTRON_BITMAP_WIDTH\\\\nelectron_simple_web_layout_height=$ELECTRON_BITMAP_HEIGHT\\\\nelectron_simple_web_layout_mismatch_count=7\\\\nelectron_simple_web_layout_mismatch_class=text-raster-mismatch\\\\nelectron_simple_web_layout_blur_or_tolerance_used=false\\\\nelectron_simple_web_layout_exit_code=2\\\\n\" > \"$BUILD_DIR/evidence.env\"; exit 1;;\\n*) printf \"electron_simple_web_layout_status=pass\\\\nelectron_simple_web_layout_reason=pass\\\\nelectron_simple_web_layout_scene=$ELECTRON_BITMAP_SCENE\\\\nelectron_simple_web_layout_width=$ELECTRON_BITMAP_WIDTH\\\\nelectron_simple_web_layout_height=$ELECTRON_BITMAP_HEIGHT\\\\nelectron_simple_web_layout_mismatch_count=0\\\\nelectron_simple_web_layout_mismatch_class=\\\\nelectron_simple_web_layout_blur_or_tolerance_used=false\\\\nelectron_simple_web_layout_exit_code=0\\\\n\" > \"$BUILD_DIR/evidence.env\";;\\nesac\\n' > " + root + "/fixture/bitmap.sh && " +
    "MANIFEST_PATH=" + root + "/manifest.txt ELECTRON_LAYOUT_MANIFEST_BITMAP_SCRIPT=" + root + "/fixture/bitmap.sh BUILD_DIR=" + root + "/out REPORT_PATH=" + root + "/report.md sh scripts/check/check-electron-simple-web-layout-manifest-evidence.shs"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val evidence = file_read(root + "/out/evidence.env")
expect(evidence).to_contain("electron_simple_web_layout_manifest_status=pass")
expect(evidence).to_contain("electron_simple_web_layout_manifest_case_count=3")
expect(evidence).to_contain("electron_simple_web_layout_manifest_pass_count=1")
expect(evidence).to_contain("electron_simple_web_layout_manifest_tracked_count=2")
expect(evidence).to_contain("electron_simple_web_layout_manifest_fail_count=0")
expect(evidence).to_contain("electron_simple_web_layout_manifest_tracked_case_policy=track-css-flex-column-divergence")
expect(evidence).to_contain("electron_simple_web_layout_manifest_tracked_case_reason=text-raster-mismatch")
expect(evidence).to_contain("electron_simple_web_layout_manifest_tracked_case_mismatch_class=text-raster-mismatch")
expect(evidence).to_contain("electron_simple_web_layout_manifest_opacity_case_policy=track-compositor-opacity-rounding")
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

#### classifies all-case missing Electron dependency as unavailable

<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-electron-simple-web-layout-manifest-missing-electron"
val command = "rm -rf " + root + " && mkdir -p " + root + "/fixture && " +
    "printf 'first_case|fixture-first|96|64|exact|first fixture\\nsecond_case|fixture-second|96|64|exact|second fixture\\n' > " + root + "/manifest.txt && " +
    "printf '#!/bin/sh\\nmkdir -p \"$BUILD_DIR\"\\nprintf \"electron_simple_web_layout_status=unavailable\\\\nelectron_simple_web_layout_reason=missing-electron-dependency\\\\nelectron_simple_web_layout_scene=$ELECTRON_BITMAP_SCENE\\\\nelectron_simple_web_layout_width=$ELECTRON_BITMAP_WIDTH\\\\nelectron_simple_web_layout_height=$ELECTRON_BITMAP_HEIGHT\\\\nelectron_simple_web_layout_mismatch_count=\\\\nelectron_simple_web_layout_blur_or_tolerance_used=\\\\nelectron_simple_web_layout_exit_code=1\\\\n\" > \"$BUILD_DIR/evidence.env\"\\nexit 1\\n' > " + root + "/fixture/bitmap.sh && " +
    "MANIFEST_PATH=" + root + "/manifest.txt ELECTRON_LAYOUT_MANIFEST_BITMAP_SCRIPT=" + root + "/fixture/bitmap.sh BUILD_DIR=" + root + "/out REPORT_PATH=" + root + "/report.md sh scripts/check/check-electron-simple-web-layout-manifest-evidence.shs || true"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val evidence = file_read(root + "/out/evidence.env")
expect(evidence).to_contain("electron_simple_web_layout_manifest_status=unavailable")
expect(evidence).to_contain("electron_simple_web_layout_manifest_reason=missing-electron-dependency")
expect(evidence).to_contain("electron_simple_web_layout_manifest_dependency_status=missing")
expect(evidence).to_contain("electron_simple_web_layout_manifest_dependency_reason=missing-electron-dependency")
expect(evidence).to_contain("electron_simple_web_layout_manifest_dependency_missing_count=2")
expect(evidence).to_contain("electron_simple_web_layout_manifest_case_count=2")
expect(evidence).to_contain("electron_simple_web_layout_manifest_fail_count=2")
```

</details>

#### selects only self hosted simple launchers by default

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = file_read("scripts/check/check-electron-simple-web-layout-manifest-evidence.shs")
expect(script).to_contain("repo-self-hosted-fallback")
expect(script).to_contain("\"release\"/*/simple")
expect(script).to_contain("\"build/bootstrap/stage3/simple\" \\\n        \"bin/simple\"")
expect(script).to_contain("\"bin/simple\"")
expect(script).to_contain("\"bin/release\"/*/simple")
expect(script).to_contain("is_rust_seed_simple")
expect(script).to_contain("SIMPLE_BIN_STATUS=forbidden")
expect(script).to_contain("export SIMPLE_BIN SIMPLE_BIN_SOURCE SIMPLE_BIN_STATUS")
expect(script).to_contain("electron_simple_web_layout_manifest_simple_bin=$SIMPLE_BIN")
expect(script).to_contain("electron_simple_web_layout_manifest_simple_bin_source=$SIMPLE_BIN_SOURCE")
expect(script).to_contain("electron_simple_web_layout_manifest_simple_bin_status=$SIMPLE_BIN_STATUS")
```

</details>

#### rejects explicit rust seed simple launcher

<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-electron-simple-web-layout-manifest-seed-forbidden"
val command = "rm -rf " + root + " && mkdir -p " + root + " && " +
    "printf 'first_case|fixture-first|96|64|exact|first fixture\\n' > " + root + "/manifest.txt && " +
    "SIMPLE_BIN=src/compiler_rust/target/release/simple MANIFEST_PATH=" + root + "/manifest.txt BUILD_DIR=" + root + "/out REPORT_PATH=" + root + "/report.md sh scripts/check/check-electron-simple-web-layout-manifest-evidence.shs || true"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val evidence = file_read(root + "/out/evidence.env")
expect(evidence).to_contain("electron_simple_web_layout_manifest_status=unavailable")
expect(evidence).to_contain("electron_simple_web_layout_manifest_reason=simple-bin-forbidden")
expect(evidence).to_contain("electron_simple_web_layout_manifest_simple_bin=src/compiler_rust/target/release/simple")
expect(evidence).to_contain("electron_simple_web_layout_manifest_simple_bin_source=explicit-env-rust-seed-forbidden")
expect(evidence).to_contain("electron_simple_web_layout_manifest_simple_bin_status=forbidden")
expect(evidence).to_contain("electron_simple_web_layout_manifest_dependency_reason=simple-bin-forbidden")
```

</details>

#### exports selected simple binary to bitmap cases

<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-electron-simple-web-layout-manifest-simple-bin"
val command = "rm -rf " + root + " && mkdir -p " + root + "/fixture && " +
    "printf 'first_case|fixture-first|96|64|exact|first fixture\\n' > " + root + "/manifest.txt && " +
    "printf '#!/bin/sh\\nexit 0\\n' > " + root + "/fixture/simple-driver && chmod +x " + root + "/fixture/simple-driver && " +
    "printf '#!/bin/sh\\nmkdir -p \"$BUILD_DIR\"\\nprintf \"electron_simple_web_layout_status=pass\\\\nelectron_simple_web_layout_reason=pass\\\\nelectron_simple_web_layout_scene=$ELECTRON_BITMAP_SCENE\\\\nelectron_simple_web_layout_width=$ELECTRON_BITMAP_WIDTH\\\\nelectron_simple_web_layout_height=$ELECTRON_BITMAP_HEIGHT\\\\nelectron_simple_web_layout_mismatch_count=0\\\\nelectron_simple_web_layout_blur_or_tolerance_used=false\\\\nelectron_simple_web_layout_exit_code=0\\\\nelectron_simple_web_layout_simple_bin=$SIMPLE_BIN\\\\nelectron_simple_web_layout_simple_bin_source=$SIMPLE_BIN_SOURCE\\\\n\" > \"$BUILD_DIR/evidence.env\"\\n' > " + root + "/fixture/bitmap.sh && " +
    "SIMPLE_BIN=" + root + "/fixture/simple-driver SIMPLE_BIN_SOURCE=fixture-env MANIFEST_PATH=" + root + "/manifest.txt ELECTRON_LAYOUT_MANIFEST_BITMAP_SCRIPT=" + root + "/fixture/bitmap.sh BUILD_DIR=" + root + "/out REPORT_PATH=" + root + "/report.md sh scripts/check/check-electron-simple-web-layout-manifest-evidence.shs"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val evidence = file_read(root + "/out/evidence.env")
expect(evidence).to_contain("electron_simple_web_layout_manifest_status=pass")
expect(evidence).to_contain("electron_simple_web_layout_manifest_simple_bin=" + root + "/fixture/simple-driver")
expect(evidence).to_contain("electron_simple_web_layout_manifest_simple_bin_source=fixture-env")
expect(evidence).to_contain("electron_simple_web_layout_manifest_simple_bin_status=pass")
expect(evidence).to_contain("case_first_case_electron_simple_web_layout_simple_bin=" + root + "/fixture/simple-driver")
expect(evidence).to_contain("case_first_case_electron_simple_web_layout_simple_bin_source=fixture-env")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** [doc/03_plan/sys_test/simple_web_browser_production_hardening.md](doc/03_plan/sys_test/simple_web_browser_production_hardening.md)
- **Design:** [doc/07_guide/ui/pixel_comparison_guide.md](doc/07_guide/ui/pixel_comparison_guide.md)


</details>
