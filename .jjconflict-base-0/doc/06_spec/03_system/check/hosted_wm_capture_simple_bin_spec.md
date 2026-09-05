# Hosted WM Capture Simple Binary Contract

> Hosted WM capture evidence is part of GUI renderer hardening. The wrapper must exercise the self-hosted Simple binary instead of `src/compiler_rust/**` so GUI capture checks do not hide regressions behind the bootstrap seed.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Hosted WM Capture Simple Binary Contract

Hosted WM capture evidence is part of GUI renderer hardening. The wrapper must exercise the self-hosted Simple binary instead of `src/compiler_rust/**` so GUI capture checks do not hide regressions behind the bootstrap seed.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Requirements | N/A |
| Plan | doc/03_plan/os/wm/simple_gui_wm_restart_2026-05-28.md |
| Design | doc/04_architecture/compiler/graphics/accelerated_shared_ui_backend_architecture.md |
| Research | doc/01_research/ui/render_path/gui_web_2d_path_assessment_2026-06-12.md |
| Source | `test/03_system/check/hosted_wm_capture_simple_bin_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Hosted WM capture evidence is part of GUI renderer hardening. The wrapper must
exercise the self-hosted Simple binary instead of `src/compiler_rust/**` so GUI
capture checks do not hide regressions behind the bootstrap seed.

## Requirements

**Requirements:** N/A

- REQ-HOSTED-WM-CAPTURE-BIN-001: Default Simple binary selection is
  self-hosted only.
- REQ-HOSTED-WM-CAPTURE-BIN-002: Explicit Rust seed paths produce
  `simple-bin-forbidden` before capture or validation programs run.
- REQ-HOSTED-WM-CAPTURE-BIN-003: Evidence records selected Simple binary,
  source, and status fields.
- REQ-HOSTED-WM-CAPTURE-BIN-004: The capture producer emits the same
  first-frame pixel diagnostics that the PPM validator independently checks.
- REQ-HOSTED-WM-CAPTURE-BIN-005: A seed runtime, missing package fingerprint,
  or local-raster fallback cannot receive production admission.

## Plan

**Plan:** doc/03_plan/os/wm/simple_gui_wm_restart_2026-05-28.md

1. Inspect the wrapper source for self-hosted candidate selection.
2. Inspect the wrapper source for Rust seed detection and provenance fields.
3. Inspect the capture producer for nonzero pixel diagnostics and checksum
   emission.
4. Run the wrapper with a Rust seed `SIMPLE_BIN` override.
5. Confirm stdout and report show `simple-bin-forbidden`.
6. Confirm capture and validation logs are not created for the forbidden path.

## Design

**Design:** doc/04_architecture/compiler/graphics/accelerated_shared_ui_backend_architecture.md

The wrapper validates `SIMPLE_BIN` before launching hosted WM capture or PPM
validation, making forbidden seed rejection deterministic and cheap.

## Research

**Research:** doc/01_research/ui/render_path/gui_web_2d_path_assessment_2026-06-12.md

## Examples

```sh
SIMPLE_LIB=src bin/simple test test/03_system/check/hosted_wm_capture_simple_bin_spec.spl --mode=interpreter --clean
```

## Scenarios

### Hosted WM capture Simple binary contract

#### selects self hosted Simple and records launcher provenance

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- selects self hosted Simple and records launcher provenance


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("selects self hosted Simple and records launcher provenance")
val script = file_read("scripts/check/check-hosted-wm-capture-evidence.shs")
expect(script).to_contain("SIMPLE_BIN_SOURCE=")
expect(script).to_contain("SIMPLE_BIN_STATUS=pass")
expect(script).to_contain("\"release\"/*/simple")
expect(script).to_contain("\"bin/release\"/*/simple")
expect(script).to_contain("\"build/bootstrap/stage3/simple\"")
expect(script).to_contain("\"bin/simple\"")
expect(script).to_contain("is_rust_seed_simple")
expect(script).to_contain("SIMPLE_BIN_STATUS=forbidden")
expect(script).to_contain("export SIMPLE_BIN SIMPLE_BIN_SOURCE SIMPLE_BIN_STATUS")
expect(script).to_contain("hosted_wm_capture_simple_bin=")
expect(script).to_contain("hosted_wm_capture_simple_bin_source=")
expect(script).to_contain("hosted_wm_capture_simple_bin_status=")
expect(script).to_contain("runtime-rust-seed-forbidden")
expect(script).to_contain("missing-theme-source-manifest")
expect(script).to_contain("invalid-theme-source-manifest")
expect(script).to_contain("local-raster-fallback-forbidden")
expect(script).to_contain("noncanonical-backend-readback")
expect(script).to_contain("hosted_wm_capture_production_admission=")
expect(script).to_contain("- production_admission: $admission_status")
```

</details>

#### keeps producer crop diagnostics aligned with validator evidence

- keeps producer crop diagnostics aligned with validator evidence


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("keeps producer crop diagnostics aligned with validator evidence")
val producer = file_read("src/os/compositor/hosted_wm_capture_evidence.spl")
expect(producer).to_contain("class HostedWmCaptureMetrics")
expect(producer).to_contain("theme_id: text")
expect(producer).to_contain("theme_source_manifest_sha256: text")
expect(producer).to_contain("hosted_wm_capture_theme_id=")
expect(producer).to_contain("hosted_wm_capture_theme_source_manifest_sha256=")
expect(producer).to_contain("hosted_wm_capture_non_background_pixels=\" + metrics.non_background_pixels.to_text()")
expect(producer).to_contain("hosted_wm_capture_bright_pixels=\" + metrics.bright_pixels.to_text()")
expect(producer).to_contain("hosted_wm_capture_accent_pixels=\" + metrics.accent_pixels.to_text()")
expect(producer).to_contain("hosted_wm_capture_sample_checksum=\" + metrics.sample_checksum.to_text()")
expect(producer).to_contain("hosted_wm_capture_theme_id")
expect(producer).to_contain("hosted_wm_capture_theme_source_manifest_sha256")

val validator = file_read("scripts/check/validate_hosted_wm_capture_ppm.spl")
expect(validator).to_contain("LEGACY_EXPECTED_WIDTH")
expect(validator).to_contain("CROPPED_EXPECTED_WIDTH")
expect(validator).to_contain("CROPPED_BACKGROUND_R")
expect(validator).to_contain("r != bg_r")
expect(validator).to_contain("r > 210 and g > 210 and b > 210")
expect(validator).to_contain("max3(r, g, b) - min3(r, g, b) > 65")
expect(validator).to_contain("min_non_bg = if is_crop: 8 else: 16000")
expect(validator).to_contain("(x % 17) == 0 and (y % 13) == 0")
```

</details>

#### rejects explicit Rust seed before capture or validation execution

- rejects explicit Rust seed before capture or validation execution
   - Expected: code equals `0`
   - Expected: capture_code equals `0`
   - Expected: validation_code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("rejects explicit Rust seed before capture or validation execution")
val root = "build/test-hosted-wm-capture-seed-forbidden"
val command = "rm -rf " + root + " && mkdir -p " + root + " && SIMPLE_BIN=src/compiler_rust/target/debug/simple BUILD_DIR=" + root + "/out REPORT_PATH=" + root + "/report.md sh scripts/check/check-hosted-wm-capture-evidence.shs > " + root + "/stdout.txt 2> " + root + "/stderr.txt || true"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val output = file_read(root + "/stdout.txt")
expect(output).to_contain("hosted_wm_capture_status=fail")
expect(output).to_contain("hosted_wm_capture_reason=simple-bin-forbidden")
expect(output).to_contain("hosted_wm_capture_simple_bin=src/compiler_rust/target/debug/simple")
expect(output).to_contain("hosted_wm_capture_simple_bin_source=explicit-env-rust-seed-forbidden")
expect(output).to_contain("hosted_wm_capture_simple_bin_status=forbidden")

val report = file_read(root + "/report.md")
expect(report).to_contain("- reason: simple-bin-forbidden")
val (_capture_out, _capture_err, capture_code) = process_run("/bin/sh", ["-c", "test ! -f " + root + "/out/capture.log"])
expect(capture_code).to_equal(0)
val (_validation_out, _validation_err, validation_code) = process_run("/bin/sh", ["-c", "test ! -f " + root + "/out/validation.env"])
expect(validation_code).to_equal(0)
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

- **Plan:** `doc/03_plan/os/wm/simple_gui_wm_restart_2026-05-28.md`
- **Design:** `doc/04_architecture/compiler/graphics/accelerated_shared_ui_backend_architecture.md`
- **Research:** `doc/01_research/ui/render_path/gui_web_2d_path_assessment_2026-06-12.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
- `REQ-HOSTED-WM-CAPTURE-BIN-001:`
- `REQ-HOSTED-WM-CAPTURE-BIN-002:`
- `REQ-HOSTED-WM-CAPTURE-BIN-003:`
- `REQ-HOSTED-WM-CAPTURE-BIN-004:`
- `REQ-HOSTED-WM-CAPTURE-BIN-005:`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `85e8f879fe800c25d98dc6835da8b46e1436e233de25716b442c10d80686565c`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `85e8f879fe800c25d98dc6835da8b46e1436e233de25716b442c10d80686565c`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `85e8f879fe800c25d98dc6835da8b46e1436e233de25716b442c10d80686565c`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **91/100**; effective score: **91/100**; blockers: **0**.

SSpec documentization score: 91/100
source: test/03_system/check/hosted_wm_capture_simple_bin_spec.spl
mirror: doc/06_spec/03_system/check/hosted_wm_capture_simple_bin_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=100 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/check/hosted_wm_capture_simple_bin_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/check/hosted_wm_capture_simple_bin_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/check/hosted_wm_capture_simple_bin_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
<!-- sspec-maintain:scorecard:end -->
