# Tauri Android WebView-equivalent rendering proof

> Gate G5.2 fallback legs: validates the WebView-equivalent proof when the host lacks Android SDK/adb/emulator. This spec confirms:

<!-- sdn-diagram:id=tauri_android_webview_proof_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=tauri_android_webview_proof_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

tauri_android_webview_proof_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=tauri_android_webview_proof_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Tauri Android WebView-equivalent rendering proof

Gate G5.2 fallback legs: validates the WebView-equivalent proof when the host lacks Android SDK/adb/emulator. This spec confirms:

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Requirements | G5.2 run+capture fallback leg |
| Plan | doc/03_plan/ui/production_readiness_master_plan_2026-07-02.md § G5.2 |
| Source | `test/03_system/check/tauri_android_webview_proof_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Gate G5.2 fallback legs: validates the WebView-equivalent proof when the host
lacks Android SDK/adb/emulator. This spec confirms:

- The Tauri shell's HTML (index.html) renders headless at 360×640 (mobile
  low-res profile: mdpi equivalent).
- The captured PNG is non-blank with expected content regions.
- The host limitation (no SDK) is recorded, not silently skipped.

**Plan:** doc/03_plan/ui/production_readiness_master_plan_2026-07-02.md § G5.2
**Requirements:** G5.2 run+capture fallback leg
**Evidence:** build/tauri-android-proof/

## Syntax

```sh
SIMPLE_LIB=src bin/simple test test/03_system/check/tauri_android_webview_proof_spec.spl
```

## Acceptance

- WebView-equivalent HTML proof script runs and captures PNG.
- Captured PNG is 360×640 (mobile viewport).
- PNG is non-blank (>16 unique colors, valid dimensions).
- Host limitation (no Android SDK/emulator) is recorded in the validation env.
- Spec passes green to allow G5.2 fallback gate closure.

## Scenarios

### Tauri Android WebView-equivalent proof

#### captures Tauri HTML at mobile resolution (360x640) headless

- Run WebView proof script to capture HTML at mobile viewport
   - Expected: code equals `0`
- Verify captured screenshot exists and is non-empty
- Confirm PNG dimensions are mobile viewport (360x640)
- Verify PNG is not blank (sufficient color diversity)
- Record host limitation (no Android SDK/emulator on this host)
- Confirm screenshot path is in the proof environment


<details>
<summary>Executable SSpec</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Run WebView proof script to capture HTML at mobile viewport")
val (_stdout, _stderr, code) = process_run(
    "/bin/sh",
    ["scripts/check/check-tauri-android-webview-proof.shs"]
)
expect(code).to_equal(0)

step("Verify captured screenshot exists and is non-empty")
val proof_env = file_read("build/tauri-android-proof/tauri_webview_proof.validation.env")
expect(proof_env).to_contain("screenshot_path=")
expect(proof_env).to_contain("screenshot_status=pass")
expect(proof_env).to_contain("screenshot_artifact_status=pass")

step("Confirm PNG dimensions are mobile viewport (360x640)")
expect(proof_env).to_contain("png_width=360")
expect(proof_env).to_contain("png_height=640")

step("Verify PNG is not blank (sufficient color diversity)")
expect(proof_env).to_contain("png_unique_colors=")
expect(proof_env).to_contain("png_validation_status=pass")

step("Record host limitation (no Android SDK/emulator on this host)")
expect(proof_env).to_contain("host_sdk_available=no")
expect(proof_env).to_contain("host_emulator_available=no")
expect(proof_env).to_contain("fallback_leg=webview_equivalent_html_proof")

step("Confirm screenshot path is in the proof environment")
expect(proof_env).to_contain("tauri_webview_360x640.png")
```

</details>

#### PNG artifact passes file and content validation

- Run proof generation and validation
   - Expected: code equals `0`
- Verify PNG exists and is a regular file (not symlink/hardlink)
- Confirm size is reasonable for 360x640 PNG


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Run proof generation and validation")
val (_stdout, _stderr, code) = process_run(
    "/bin/sh",
    ["scripts/check/check-tauri-android-webview-proof.shs"]
)
expect(code).to_equal(0)

step("Verify PNG exists and is a regular file (not symlink/hardlink)")
val proof_env = file_read("build/tauri-android-proof/tauri_webview_proof.validation.env")
expect(proof_env).to_contain("screenshot_file_reason=pass")
expect(proof_env).to_contain("screenshot_file_status=pass")

step("Confirm size is reasonable for 360x640 PNG")
expect(proof_env).to_contain("screenshot_size_bytes=")
```

</details>

#### records the fallback gate status for G5.2

- Capture proof and validate
   - Expected: code equals `0`
- Confirm overall status is pass
- Document that this is the G5.2 fallback leg (no emulator on host)


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Capture proof and validate")
val (_stdout, _stderr, code) = process_run(
    "/bin/sh",
    ["scripts/check/check-tauri-android-webview-proof.shs"]
)
expect(code).to_equal(0)

step("Confirm overall status is pass")
val proof_env = file_read("build/tauri-android-proof/tauri_webview_proof.validation.env")
expect(proof_env).to_contain("tauri_webview_proof_status=pass")

step("Document that this is the G5.2 fallback leg (no emulator on host)")
expect(proof_env).to_contain("fallback_leg=webview_equivalent_html_proof")
expect(proof_env).to_contain("viewport_width=360")
expect(proof_env).to_contain("viewport_height=640")
expect(proof_env).to_contain("viewport_dpi=mdpi_equiv")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** [G5.2 run+capture fallback leg](G5.2 run+capture fallback leg)
- **Plan:** [doc/03_plan/ui/production_readiness_master_plan_2026-07-02.md § G5.2](doc/03_plan/ui/production_readiness_master_plan_2026-07-02.md § G5.2)


</details>
