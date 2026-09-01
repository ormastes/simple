# Tauri Android WebView-equivalent rendering proof

> Gate G5.2 fallback legs: validates the WebView-equivalent proof when the host lacks Android SDK/adb/emulator. This spec confirms:

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
| Updated | 2026-08-26 |
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

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- captures Tauri HTML at mobile resolution (360x640) headless
- Run WebView proof script to capture HTML at mobile viewport
   - Expected: code equals `0`
- Verify captured screenshot exists and is non-empty
- Confirm PNG dimensions are mobile viewport (360x640)
- Verify PNG is not blank (sufficient color diversity)
- Record host limitation (no Android SDK/emulator on this host)
- Confirm screenshot path is in the proof environment


<details>
<summary>Executable SSpec</summary>

Runnable source: 30 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("captures Tauri HTML at mobile resolution (360x640) headless")
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

- PNG artifact passes file and content validation
- Run proof generation and validation
   - Expected: code equals `0`
- Verify PNG exists and is a regular file (not symlink/hardlink)
- Confirm size is reasonable for 360x640 PNG


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("PNG artifact passes file and content validation")
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

- records the fallback gate status for G5.2
- Capture proof and validate
   - Expected: code equals `0`
- Confirm overall status is pass
- Document that this is the G5.2 fallback leg (no emulator on host)


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("records the fallback gate status for G5.2")
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

- **Requirements:** `G5.2 run+capture fallback leg`
- **Plan:** `doc/03_plan/ui/production_readiness_master_plan_2026-07-02.md § G5.2`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `7ee02ec019eb15a79034d5c1b16e5bb7809981b3f8a5f23de4498deca8c7cb69`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `7ee02ec019eb15a79034d5c1b16e5bb7809981b3f8a5f23de4498deca8c7cb69`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `7ee02ec019eb15a79034d5c1b16e5bb7809981b3f8a5f23de4498deca8c7cb69`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/03_system/check/tauri_android_webview_proof_spec.spl
mirror: doc/06_spec/03_system/check/tauri_android_webview_proof_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/check/tauri_android_webview_proof_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/check/tauri_android_webview_proof_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/check/tauri_android_webview_proof_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/check/tauri_android_webview_proof_spec.spl:47:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'captures Tauri HTML at mobile resolution (360x640) headless' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/check/tauri_android_webview_proof_spec.spl:79:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'PNG artifact passes file and content validation' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/check/tauri_android_webview_proof_spec.spl:97:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'records the fallback gate status for G5.2' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
