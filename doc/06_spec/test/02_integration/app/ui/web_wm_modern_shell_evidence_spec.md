# Web WM Modern Shell Evidence Integration

> Runs the modern Web WM preview evidence wrapper and records the preview HTML, ARGB bitmap JSON, PNG bitmap, DOM audit JSON, and report paths when host GUI dependencies are available. Hosts without Electron, display support, or a working Simple runtime must report `environment-unavailable` explicitly. When Electron is available, the wrapper also opens the preview and verifies real browser focus, keyboard, pointer, and click delivery on visible WM controls. The preview generator must use a self-hosted Simple runtime; explicit Rust seed overrides are rejected before preview or Electron artifacts are created.

<!-- sdn-diagram:id=web_wm_modern_shell_evidence_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=web_wm_modern_shell_evidence_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

web_wm_modern_shell_evidence_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=web_wm_modern_shell_evidence_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Web WM Modern Shell Evidence Integration

Runs the modern Web WM preview evidence wrapper and records the preview HTML, ARGB bitmap JSON, PNG bitmap, DOM audit JSON, and report paths when host GUI dependencies are available. Hosts without Electron, display support, or a working Simple runtime must report `environment-unavailable` explicitly. When Electron is available, the wrapper also opens the preview and verifies real browser focus, keyboard, pointer, and click delivery on visible WM controls. The preview generator must use a self-hosted Simple runtime; explicit Rust seed overrides are rejected before preview or Electron artifacts are created.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Requirements | N/A |
| Plan | doc/03_plan/ui/modernization/ui_modernization_plan_2026-06-25.md |
| Design | doc/07_guide/app/ui/web_wm_modern_shell.md |
| Research | doc/01_research/ui/wm/simple_wm_modernization.md |
| Source | `test/02_integration/app/ui/web_wm_modern_shell_evidence_spec.spl` |
| Updated | 2026-06-27 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Runs the modern Web WM preview evidence wrapper and records the preview HTML,
ARGB bitmap JSON, PNG bitmap, DOM audit JSON, and report paths when host GUI
dependencies are available. Hosts without Electron, display support, or a
working Simple runtime must report `environment-unavailable` explicitly.
When Electron is available, the wrapper also opens the preview and verifies
real browser focus, keyboard, pointer, and click delivery on visible WM
controls. The preview generator must use a self-hosted Simple runtime; explicit
Rust seed overrides are rejected before preview or Electron artifacts are
created.

**Requirements:** N/A
**Plan:** doc/03_plan/ui/modernization/ui_modernization_plan_2026-06-25.md
**Design:** doc/07_guide/app/ui/web_wm_modern_shell.md
**Research:** doc/01_research/ui/wm/simple_wm_modernization.md

## Syntax

```bash
sh scripts/check/check-web-wm-modern-shell-evidence.shs
```

## Evidence

- Evidence: build/test-artifacts/02_integration/app/ui/web_wm_modern_shell_evidence/evidence.env
- Report: build/test-artifacts/02_integration/app/ui/web_wm_modern_shell_evidence/report.md
- Preview: build/test-artifacts/02_integration/app/ui/web_wm_modern_shell_evidence/simple_wm_modern_preview.html
- PNG: build/test-artifacts/02_integration/app/ui/web_wm_modern_shell_evidence/simple_wm_modern_preview.png
- Interaction JSON: build/test-artifacts/02_integration/app/ui/web_wm_modern_shell_evidence/simple_wm_modern_preview_interaction.json
- Interaction PNG: build/test-artifacts/02_integration/app/ui/web_wm_modern_shell_evidence/simple_wm_modern_preview_after_interaction.png

## Scenarios

### Web WM modern shell captured evidence gate

#### captures or explicitly classifies the modern shell evidence run

- Run the modern shell evidence wrapper
   - Expected: code equals `0`
- Read the wrapper evidence contract
- Accept only real pass or explicit host-unavailable status
   - Expected: reason equals `pass`
   - Expected: _value_of(evidence, "web_wm_modern_shell_evidence_bitmap_nonblank_status") equals `pass`
   - Expected: _value_of(evidence, "web_wm_modern_shell_evidence_audit_pass") equals `pass`
   - Expected: _value_of(evidence, "web_wm_modern_shell_evidence_unexpected_overlap_count") equals `0`
   - Expected: _value_of(evidence, "web_wm_modern_shell_evidence_clipped_count") equals `0`
   - Expected: _value_of(evidence, "web_wm_modern_shell_evidence_contrast_failures") equals `0`
   - Expected: _value_of(evidence, "web_wm_modern_shell_evidence_touch_failures") equals `0`
   - Expected: _value_of(evidence, "web_wm_modern_shell_evidence_interaction_pass") equals `pass`
   - Expected: _value_of(evidence, "web_wm_modern_shell_evidence_interaction_focus") equals `pass`
   - Expected: _value_of(evidence, "web_wm_modern_shell_evidence_interaction_keyboard") equals `pass`
   - Expected: _value_of(evidence, "web_wm_modern_shell_evidence_interaction_input") equals `pass`
   - Expected: _value_of(evidence, "web_wm_modern_shell_evidence_interaction_pointer") equals `pass`
   - Expected: _value_of(evidence, "web_wm_modern_shell_evidence_interaction_clicks") equals `pass`
   - Expected: status equals `environment-unavailable`
   - Expected: reason == "electron-missing" or reason == "display-missing" or reason == "simple-runtime-unavailable" or reason == "simple-runtime-preview-failed" is true
- Read the operator report


<details>
<summary>Executable SSpec</summary>

Runnable source: 53 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Run the modern shell evidence wrapper")
val command = "rm -rf '" + BUILD_DIR + "' && BUILD_DIR='" + BUILD_DIR + "' EVIDENCE_ENV='" + EVIDENCE_ENV + "' REPORT_PATH='" + REPORT_PATH + "' sh scripts/check/check-web-wm-modern-shell-evidence.shs"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

step("Read the wrapper evidence contract")
val evidence = file_read(EVIDENCE_ENV)
expect(evidence).to_contain("web_wm_modern_shell_evidence_status=")
expect(evidence).to_contain("web_wm_modern_shell_evidence_html=" + BUILD_DIR + "/simple_wm_modern_preview.html")
expect(evidence).to_contain("web_wm_modern_shell_evidence_argb=" + BUILD_DIR + "/simple_wm_modern_preview_argb.json")
expect(evidence).to_contain("web_wm_modern_shell_evidence_png=" + BUILD_DIR + "/simple_wm_modern_preview.png")
expect(evidence).to_contain("web_wm_modern_shell_evidence_audit=" + BUILD_DIR + "/simple_wm_modern_preview_audit.json")
expect(evidence).to_contain("web_wm_modern_shell_evidence_interaction=" + BUILD_DIR + "/simple_wm_modern_preview_interaction.json")
expect(evidence).to_contain("web_wm_modern_shell_evidence_interaction_png=" + BUILD_DIR + "/simple_wm_modern_preview_after_interaction.png")
expect(evidence).to_contain("web_wm_modern_shell_evidence_contrast_min_x100=450")
expect(evidence).to_contain("web_wm_modern_shell_evidence_touch_min_px=44")
expect(evidence).to_contain("web_wm_modern_shell_evidence_media_features=prefers-contrast=more,prefers-reduced-motion=reduce")
expect(evidence).to_contain("web_wm_modern_shell_evidence_simple_runtime=")
expect(evidence).to_contain("web_wm_modern_shell_evidence_simple_runtime_source=")
expect(evidence).to_contain("web_wm_modern_shell_evidence_simple_runtime_status=")

step("Accept only real pass or explicit host-unavailable status")
val status = _value_of(evidence, "web_wm_modern_shell_evidence_status")
val reason = _value_of(evidence, "web_wm_modern_shell_evidence_reason")
if status == "pass":
    expect(reason).to_equal("pass")
    expect(_value_of(evidence, "web_wm_modern_shell_evidence_bitmap_nonblank_status")).to_equal("pass")
    expect(_value_of(evidence, "web_wm_modern_shell_evidence_audit_pass")).to_equal("pass")
    expect(_value_of(evidence, "web_wm_modern_shell_evidence_unexpected_overlap_count")).to_equal("0")
    expect(_value_of(evidence, "web_wm_modern_shell_evidence_clipped_count")).to_equal("0")
    expect(_value_of(evidence, "web_wm_modern_shell_evidence_contrast_failures")).to_equal("0")
    expect(_value_of(evidence, "web_wm_modern_shell_evidence_touch_failures")).to_equal("0")
    expect(_value_of(evidence, "web_wm_modern_shell_evidence_interaction_pass")).to_equal("pass")
    expect(_value_of(evidence, "web_wm_modern_shell_evidence_interaction_focus")).to_equal("pass")
    expect(_value_of(evidence, "web_wm_modern_shell_evidence_interaction_keyboard")).to_equal("pass")
    expect(_value_of(evidence, "web_wm_modern_shell_evidence_interaction_input")).to_equal("pass")
    expect(_value_of(evidence, "web_wm_modern_shell_evidence_interaction_pointer")).to_equal("pass")
    expect(_value_of(evidence, "web_wm_modern_shell_evidence_interaction_clicks")).to_equal("pass")
    expect(evidence).to_contain("web_wm_modern_shell_evidence_interaction_event_count=")
else:
    expect(status).to_equal("environment-unavailable")
    expect(reason == "electron-missing" or reason == "display-missing" or reason == "simple-runtime-unavailable" or reason == "simple-runtime-preview-failed").to_equal(true)

step("Read the operator report")
val report = file_read(REPORT_PATH)
expect(report).to_contain("# Web WM Modern Shell Evidence")
expect(report).to_contain("- preview: `" + BUILD_DIR + "/simple_wm_modern_preview.html`")
expect(report).to_contain("- PNG: `" + BUILD_DIR + "/simple_wm_modern_preview.png`")
expect(report).to_contain("- audit: `" + BUILD_DIR + "/simple_wm_modern_preview_audit.json`")
expect(report).to_contain("- interaction: `" + BUILD_DIR + "/simple_wm_modern_preview_interaction.json`")
expect(report).to_contain("- interaction PNG: `" + BUILD_DIR + "/simple_wm_modern_preview_after_interaction.png`")
expect(report).to_contain("- simple runtime: `")
expect(report).to_contain("- simple runtime source: `")
```

</details>

#### rejects explicit Rust seed runtime before preview generation

- Run the wrapper with an explicit Rust seed runtime
   - Expected: code equals `0`
- Read the forbidden-runtime evidence
- Confirm preview and Electron artifacts were not created
   - Expected: html_code equals `0`
   - Expected: argb_code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Run the wrapper with an explicit Rust seed runtime")
val root = "build/test-web-wm-modern-shell-seed-forbidden"
val evidence_path = root + "/evidence.env"
val report_path = root + "/report.md"
val command = "rm -rf " + root + " && mkdir -p " + root + " && SIMPLE_CMD=src/compiler_rust/target/release/simple BUILD_DIR=" + root + " EVIDENCE_ENV=" + evidence_path + " REPORT_PATH=" + report_path + " sh scripts/check/check-web-wm-modern-shell-evidence.shs > " + root + "/stdout.txt 2> " + root + "/stderr.txt || true"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

step("Read the forbidden-runtime evidence")
val evidence = file_read(evidence_path)
expect(evidence).to_contain("web_wm_modern_shell_evidence_status=fail")
expect(evidence).to_contain("web_wm_modern_shell_evidence_reason=simple-runtime-forbidden")
expect(evidence).to_contain("web_wm_modern_shell_evidence_simple_runtime=src/compiler_rust/target/release/simple")
expect(evidence).to_contain("web_wm_modern_shell_evidence_simple_runtime_source=explicit-env-rust-seed-forbidden")
expect(evidence).to_contain("web_wm_modern_shell_evidence_simple_runtime_status=forbidden")

step("Confirm preview and Electron artifacts were not created")
val report = file_read(report_path)
expect(report).to_contain("- reason: `simple-runtime-forbidden`")
val (_html_out, _html_err, html_code) = process_run("/bin/sh", ["-c", "test ! -f " + root + "/simple_wm_modern_preview.html"])
expect(html_code).to_equal(0)
val (_argb_out, _argb_err, argb_code) = process_run("/bin/sh", ["-c", "test ! -f " + root + "/simple_wm_modern_preview_argb.json"])
expect(argb_code).to_equal(0)
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

- **Plan:** [doc/03_plan/ui/modernization/ui_modernization_plan_2026-06-25.md](doc/03_plan/ui/modernization/ui_modernization_plan_2026-06-25.md)
- **Design:** [doc/07_guide/app/ui/web_wm_modern_shell.md](doc/07_guide/app/ui/web_wm_modern_shell.md)
- **Research:** [doc/01_research/ui/wm/simple_wm_modernization.md](doc/01_research/ui/wm/simple_wm_modernization.md)


</details>
