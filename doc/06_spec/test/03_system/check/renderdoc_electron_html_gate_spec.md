# RenderDoc Electron HTML gate

> Validates the fail-closed gate for Electron Chromium/Vulkan HTML/CSS RenderDoc evidence. The local host may not have RenderDoc installed, but the gate must record a deterministic non-pass state and accept only Electron `.rdc` evidence that also proves the requested Chromium Vulkan/ANGLE launch contract.

<!-- sdn-diagram:id=renderdoc_electron_html_gate_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=renderdoc_electron_html_gate_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

renderdoc_electron_html_gate_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=renderdoc_electron_html_gate_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# RenderDoc Electron HTML gate

Validates the fail-closed gate for Electron Chromium/Vulkan HTML/CSS RenderDoc evidence. The local host may not have RenderDoc installed, but the gate must record a deterministic non-pass state and accept only Electron `.rdc` evidence that also proves the requested Chromium Vulkan/ANGLE launch contract.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Requirements | N/A |
| Plan | doc/03_plan/sys_test/html_css_spec_traceability.md |
| Design | doc/07_guide/tooling/renderdoc_capture_infra.md |
| Research | doc/09_report/electron_vulkan_renderdoc_debug_2026-06-17.md |
| Source | `test/03_system/check/renderdoc_electron_html_gate_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Validates the fail-closed gate for Electron Chromium/Vulkan HTML/CSS RenderDoc
evidence. The local host may not have RenderDoc installed, but the gate must
record a deterministic non-pass state and accept only Electron `.rdc` evidence
that also proves the requested Chromium Vulkan/ANGLE launch contract.

**Plan:** doc/03_plan/sys_test/html_css_spec_traceability.md
**Requirements:** N/A
**Research:** doc/09_report/electron_vulkan_renderdoc_debug_2026-06-17.md
**Design:** doc/07_guide/tooling/renderdoc_capture_infra.md

## Syntax

```sh
RDOC_ELECTRON_HTML_EVIDENCE_ENV=build/renderdoc/canonical-probe/electron-html/evidence.env \
BUILD_DIR=build/test-renderdoc-electron-html-gate \
REPORT_PATH=build/test-renderdoc-electron-html-gate/report.md \
sh scripts/check/check-renderdoc-electron-html-gate.shs || true
```

## Acceptance

- Missing or failed Electron RenderDoc evidence produces typed non-pass gate
  evidence.
- Passing gate evidence requires Electron backend, pass status, `RDOC` magic,
  an existing `.rdc` file, and Vulkan requested API/ANGLE fields.

## Scenarios

### RenderDoc Electron HTML gate

#### writes typed non-pass evidence for missing or failed Electron capture

<details>
<summary>Executable SSpec</summary>

Runnable source: 30 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val command = "rm -rf build/test-renderdoc-electron-html-gate && RDOC_ELECTRON_HTML_EVIDENCE_ENV=build/renderdoc/canonical-probe/electron-html/evidence.env BUILD_DIR=build/test-renderdoc-electron-html-gate REPORT_PATH=build/test-renderdoc-electron-html-gate/report.md sh scripts/check/check-renderdoc-electron-html-gate.shs || true"
val (_stdout, _stderr, code) = rt_process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val evidence = rt_file_read_text("build/test-renderdoc-electron-html-gate/evidence.env") ?? ""
expect(evidence).to_contain("rdoc_electron_html_gate_status=")
expect(evidence).to_contain("rdoc_electron_html_gate_reason=")
expect(evidence).to_contain("rdoc_electron_html_gate_source_env=")
expect(evidence).to_contain("rdoc_electron_html_gate_required_backend=electron")
expect(evidence).to_contain("rdoc_electron_html_gate_required_status=pass")
expect(evidence).to_contain("rdoc_electron_html_gate_required_magic=RDOC")
expect(evidence).to_contain("rdoc_electron_html_gate_required_api=vulkan")
expect(evidence).to_contain("rdoc_electron_html_gate_required_angle=vulkan")

val status = _value_of(evidence, "rdoc_electron_html_gate_status")
val reason = _value_of(evidence, "rdoc_electron_html_gate_reason")
val backend = _value_of(evidence, "rdoc_electron_html_gate_backend")
val capture_status = _value_of(evidence, "rdoc_electron_html_gate_capture_status")
val magic = _value_of(evidence, "rdoc_electron_html_gate_capture_magic")
val api = _value_of(evidence, "rdoc_electron_html_gate_requested_api")
val angle = _value_of(evidence, "rdoc_electron_html_gate_requested_angle")

if status == "pass":
    expect(backend).to_equal("electron")
    expect(capture_status).to_equal("pass")
    expect(magic).to_equal("RDOC")
    expect(api).to_equal("vulkan")
    expect(angle).to_equal("vulkan")
else:
    expect(reason.len()).to_be_greater_than(0)
```

</details>

#### passes with controlled Electron Vulkan RDOC evidence

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val command = "rm -rf build/test-renderdoc-electron-html-gate-pass && mkdir -p build/test-renderdoc-electron-html-gate-pass/source && printf 'RDOCsynthetic electron capture\\n' > build/test-renderdoc-electron-html-gate-pass/source/electron.rdc && printf 'rdoc_backend=electron\\nrdoc_scene=html-css-electron\\nrdoc_capture_status=pass\\nrdoc_capture_reason=pass\\nrdoc_capture_file=build/test-renderdoc-electron-html-gate-pass/source/electron.rdc\\nrdoc_capture_magic=RDOC\\nrdoc_html_path=test/fixtures/html_css/generated_gui_vulkan_renderdoc_fixture.html\\nrdoc_electron=tools/electron-shell/node_modules/electron/dist/Electron.app/Contents/MacOS/Electron\\nrdoc_electron_capture_script=tools/electron-live-bitmap/capture_html_argb.js\\nrdoc_chromium_requested_api=vulkan\\nrdoc_chromium_requested_angle=vulkan\\nrdoc_chromium_requested_features=Vulkan\\nrdoc_chromium_launch_flags=--no-sandbox --disable-gpu-sandbox --enable-features=Vulkan --use-angle=vulkan\\n' > build/test-renderdoc-electron-html-gate-pass/source/evidence.env && RDOC_ELECTRON_HTML_EVIDENCE_ENV=build/test-renderdoc-electron-html-gate-pass/source/evidence.env BUILD_DIR=build/test-renderdoc-electron-html-gate-pass/out REPORT_PATH=build/test-renderdoc-electron-html-gate-pass/report.md sh scripts/check/check-renderdoc-electron-html-gate.shs"
val (_stdout, _stderr, code) = rt_process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val evidence = rt_file_read_text("build/test-renderdoc-electron-html-gate-pass/out/evidence.env") ?? ""
expect(evidence).to_contain("rdoc_electron_html_gate_status=pass")
expect(evidence).to_contain("rdoc_electron_html_gate_reason=pass")
expect(evidence).to_contain("rdoc_electron_html_gate_backend=electron")
expect(evidence).to_contain("rdoc_electron_html_gate_capture_magic=RDOC")
expect(evidence).to_contain("rdoc_electron_html_gate_requested_api=vulkan")
expect(evidence).to_contain("rdoc_electron_html_gate_requested_angle=vulkan")
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
- **Design:** [doc/07_guide/tooling/renderdoc_capture_infra.md](doc/07_guide/tooling/renderdoc_capture_infra.md)
- **Research:** [doc/09_report/electron_vulkan_renderdoc_debug_2026-06-17.md](doc/09_report/electron_vulkan_renderdoc_debug_2026-06-17.md)


</details>
