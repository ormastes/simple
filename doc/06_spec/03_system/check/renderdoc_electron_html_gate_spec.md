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
| 8 | 8 | 0 | 0 |

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
- Passing gate evidence requires Electron backend, `html-css-electron` scene,
  pass status, `RDOC` magic, an existing `.rdc` file, the canonical HTML/CSS
  RenderDoc fixture, the repo Electron shell binary, the live-bitmap capture
  script, and Vulkan requested API/ANGLE/features launch fields.
- Passing gate evidence also requires the Electron live-bitmap ARGB JSON proof
  to have the expected dimensions, `argb-u32` format, the
  `electron-chromium-capture` producer, complete pixel data, and nonblank
  rendered pixels.

## Scenarios

### RenderDoc Electron HTML gate

#### writes typed non-pass evidence for missing or failed Electron capture

<details>
<summary>Executable SSpec</summary>

Runnable source: 59 lines folded for reproduction.
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
expect(evidence).to_contain("rdoc_electron_html_gate_required_scene=html-css-electron")
expect(evidence).to_contain("rdoc_electron_html_gate_required_status=pass")
expect(evidence).to_contain("rdoc_electron_html_gate_required_magic=RDOC")
expect(evidence).to_contain("rdoc_electron_html_gate_required_api=vulkan")
expect(evidence).to_contain("rdoc_electron_html_gate_required_angle=vulkan")
expect(evidence).to_contain("rdoc_electron_html_gate_required_features=Vulkan")
expect(evidence).to_contain("rdoc_electron_html_gate_required_html_path_suffix=test/fixtures/html_css/generated_gui_vulkan_renderdoc_fixture.html")
expect(evidence).to_contain("rdoc_electron_html_gate_required_electron_suffix=tools/electron-shell/node_modules/electron/dist/Electron.app/Contents/MacOS/Electron|tools/electron-shell/node_modules/.bin/electron")
expect(evidence).to_contain("rdoc_electron_html_gate_required_capture_script_suffix=tools/electron-live-bitmap/capture_html_argb.js")
expect(evidence).to_contain("rdoc_electron_html_gate_required_argb_status=pass")
expect(evidence).to_contain("rdoc_electron_html_gate_required_argb_format=argb-u32")
expect(evidence).to_contain("rdoc_electron_html_gate_required_argb_producer=electron-chromium-capture")
expect(evidence).to_contain("rdoc_electron_html_gate_required_argb_nonblank_pixel_count_min=1")
expect(evidence).to_contain("rdoc_electron_html_gate_required_launch_flag_enable_features=--enable-features=Vulkan")
expect(evidence).to_contain("rdoc_electron_html_gate_required_launch_flag_use_angle=--use-angle=vulkan")
expect(evidence).to_contain("rdoc_electron_html_gate_required_vulkan_log_no_angle_failure=1")
expect(evidence).to_contain("rdoc_electron_html_gate_capture_file_magic=")
expect(evidence).to_contain("rdoc_electron_html_gate_log=")
expect(evidence).to_contain("rdoc_electron_html_gate_vulkan_log_status=")
expect(evidence).to_contain("rdoc_electron_html_gate_vulkan_log_reason=")

val status = _value_of(evidence, "rdoc_electron_html_gate_status")
val reason = _value_of(evidence, "rdoc_electron_html_gate_reason")
val backend = _value_of(evidence, "rdoc_electron_html_gate_backend")
val scene = _value_of(evidence, "rdoc_electron_html_gate_scene")
val capture_status = _value_of(evidence, "rdoc_electron_html_gate_capture_status")
val magic = _value_of(evidence, "rdoc_electron_html_gate_capture_magic")
val html_path = _value_of(evidence, "rdoc_electron_html_gate_html_path")
val electron = _value_of(evidence, "rdoc_electron_html_gate_electron")
val capture_script = _value_of(evidence, "rdoc_electron_html_gate_capture_script")
val api = _value_of(evidence, "rdoc_electron_html_gate_requested_api")
val angle = _value_of(evidence, "rdoc_electron_html_gate_requested_angle")
val features = _value_of(evidence, "rdoc_electron_html_gate_requested_features")
val flags = _value_of(evidence, "rdoc_electron_html_gate_launch_flags")

if status == "pass":
    expect(backend).to_equal("electron")
    expect(scene).to_equal("html-css-electron")
    expect(capture_status).to_equal("pass")
    expect(magic).to_equal("RDOC")
    expect(html_path).to_contain("test/fixtures/html_css/generated_gui_vulkan_renderdoc_fixture.html")
    expect(electron).to_contain("tools/electron-shell/node_modules/")
    expect(capture_script).to_contain("tools/electron-live-bitmap/capture_html_argb.js")
    expect(api).to_equal("vulkan")
    expect(angle).to_equal("vulkan")
    expect(features).to_contain("Vulkan")
    expect(flags).to_contain("--enable-features=Vulkan")
    expect(flags).to_contain("--use-angle=vulkan")
else:
    expect(reason.len()).to_be_greater_than(0)
```

</details>

#### passes with controlled Electron Vulkan RDOC evidence

<details>
<summary>Executable SSpec</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val command = "rm -rf build/test-renderdoc-electron-html-gate-pass && mkdir -p build/test-renderdoc-electron-html-gate-pass/source && printf 'RDOCsynthetic electron capture\\n' > build/test-renderdoc-electron-html-gate-pass/source/electron.rdc && printf '{\"width\":2,\"height\":2,\"format\":\"argb-u32\",\"producer\":\"electron-chromium-capture\",\"nativeWidth\":2,\"nativeHeight\":2,\"pixels\":[4294967295,4278190335,4294967295,4294967295]}\\n' > build/test-renderdoc-electron-html-gate-pass/source/electron_argb.json && printf 'rdoc_backend=electron\\nrdoc_scene=html-css-electron\\nrdoc_capture_status=pass\\nrdoc_capture_reason=pass\\nrdoc_capture_file=build/test-renderdoc-electron-html-gate-pass/source/electron.rdc\\nrdoc_capture_magic=RDOC\\nrdoc_html_path=test/fixtures/html_css/generated_gui_vulkan_renderdoc_fixture.html\\nrdoc_electron=tools/electron-shell/node_modules/electron/dist/Electron.app/Contents/MacOS/Electron\\nrdoc_electron_capture_script=tools/electron-live-bitmap/capture_html_argb.js\\nrdoc_electron_argb=build/test-renderdoc-electron-html-gate-pass/source/electron_argb.json\\nrdoc_electron_width=2\\nrdoc_electron_height=2\\nrdoc_chromium_requested_api=vulkan\\nrdoc_chromium_requested_angle=vulkan\\nrdoc_chromium_requested_features=Vulkan\\nrdoc_chromium_launch_flags=--no-sandbox --disable-gpu-sandbox --enable-features=Vulkan --use-angle=vulkan\\n' > build/test-renderdoc-electron-html-gate-pass/source/evidence.env && RDOC_ELECTRON_HTML_EVIDENCE_ENV=build/test-renderdoc-electron-html-gate-pass/source/evidence.env BUILD_DIR=build/test-renderdoc-electron-html-gate-pass/out REPORT_PATH=build/test-renderdoc-electron-html-gate-pass/report.md sh scripts/check/check-renderdoc-electron-html-gate.shs"
val (_stdout, _stderr, code) = rt_process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val evidence = rt_file_read_text("build/test-renderdoc-electron-html-gate-pass/out/evidence.env") ?? ""
expect(evidence).to_contain("rdoc_electron_html_gate_status=pass")
expect(evidence).to_contain("rdoc_electron_html_gate_reason=pass")
expect(evidence).to_contain("rdoc_electron_html_gate_backend=electron")
expect(evidence).to_contain("rdoc_electron_html_gate_scene=html-css-electron")
expect(evidence).to_contain("rdoc_electron_html_gate_html_path=test/fixtures/html_css/generated_gui_vulkan_renderdoc_fixture.html")
expect(evidence).to_contain("rdoc_electron_html_gate_electron=tools/electron-shell/node_modules/electron/dist/Electron.app/Contents/MacOS/Electron")
expect(evidence).to_contain("rdoc_electron_html_gate_required_electron_suffix=tools/electron-shell/node_modules/electron/dist/Electron.app/Contents/MacOS/Electron|tools/electron-shell/node_modules/.bin/electron")
expect(evidence).to_contain("rdoc_electron_html_gate_capture_script=tools/electron-live-bitmap/capture_html_argb.js")
expect(evidence).to_contain("rdoc_electron_html_gate_capture_magic=RDOC")
expect(evidence).to_contain("rdoc_electron_html_gate_capture_file_magic=RDOC")
expect(evidence).to_contain("rdoc_electron_html_gate_requested_api=vulkan")
expect(evidence).to_contain("rdoc_electron_html_gate_requested_angle=vulkan")
expect(evidence).to_contain("rdoc_electron_html_gate_requested_features=Vulkan")
expect(evidence).to_contain("rdoc_electron_html_gate_required_features=Vulkan")
expect(evidence).to_contain("rdoc_electron_html_gate_launch_flags=--no-sandbox --disable-gpu-sandbox --enable-features=Vulkan --use-angle=vulkan")
expect(evidence).to_contain("rdoc_electron_html_gate_argb_status=pass")
expect(evidence).to_contain("rdoc_electron_html_gate_argb_reason=pass")
expect(evidence).to_contain("rdoc_electron_html_gate_argb_format=argb-u32")
expect(evidence).to_contain("rdoc_electron_html_gate_argb_producer=electron-chromium-capture")
expect(evidence).to_contain("rdoc_electron_html_gate_argb_pixel_count=4")
expect(evidence).to_contain("rdoc_electron_html_gate_argb_nonblank_pixel_count=1")
expect(evidence).to_contain("rdoc_electron_html_gate_vulkan_log_status=not-recorded")
expect(evidence).to_contain("rdoc_electron_html_gate_required_vulkan_log_no_angle_failure=1")
```

</details>

#### rejects Electron captures missing live-bitmap ARGB rendered pixels

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val command = "rm -rf build/test-renderdoc-electron-html-gate-missing-argb && mkdir -p build/test-renderdoc-electron-html-gate-missing-argb/source && printf 'RDOCsynthetic electron capture\\n' > build/test-renderdoc-electron-html-gate-missing-argb/source/electron.rdc && printf 'rdoc_backend=electron\\nrdoc_scene=html-css-electron\\nrdoc_capture_status=pass\\nrdoc_capture_reason=pass\\nrdoc_capture_file=build/test-renderdoc-electron-html-gate-missing-argb/source/electron.rdc\\nrdoc_capture_magic=RDOC\\nrdoc_html_path=test/fixtures/html_css/generated_gui_vulkan_renderdoc_fixture.html\\nrdoc_electron=tools/electron-shell/node_modules/electron/dist/Electron.app/Contents/MacOS/Electron\\nrdoc_electron_capture_script=tools/electron-live-bitmap/capture_html_argb.js\\nrdoc_electron_argb=build/test-renderdoc-electron-html-gate-missing-argb/source/electron_argb.json\\nrdoc_electron_width=2\\nrdoc_electron_height=2\\nrdoc_chromium_requested_api=vulkan\\nrdoc_chromium_requested_angle=vulkan\\nrdoc_chromium_requested_features=Vulkan\\nrdoc_chromium_launch_flags=--no-sandbox --disable-gpu-sandbox --enable-features=Vulkan --use-angle=vulkan\\n' > build/test-renderdoc-electron-html-gate-missing-argb/source/evidence.env && RDOC_ELECTRON_HTML_EVIDENCE_ENV=build/test-renderdoc-electron-html-gate-missing-argb/source/evidence.env BUILD_DIR=build/test-renderdoc-electron-html-gate-missing-argb/out REPORT_PATH=build/test-renderdoc-electron-html-gate-missing-argb/report.md sh scripts/check/check-renderdoc-electron-html-gate.shs || true"
val (_stdout, _stderr, code) = rt_process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val evidence = rt_file_read_text("build/test-renderdoc-electron-html-gate-missing-argb/out/evidence.env") ?? ""
expect(evidence).to_contain("rdoc_electron_html_gate_status=fail")
expect(evidence).to_contain("rdoc_electron_html_gate_reason=missing-electron-argb-file")
expect(evidence).to_contain("rdoc_electron_html_gate_argb_status=missing")
expect(evidence).to_contain("rdoc_electron_html_gate_argb_pixel_count=0")
expect(evidence).to_contain("rdoc_electron_html_gate_required_argb_status=pass")
```

</details>

#### rejects Electron captures from an unexpected binary path

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val command = "rm -rf build/test-renderdoc-electron-html-gate-wrong-electron && mkdir -p build/test-renderdoc-electron-html-gate-wrong-electron/source && printf 'RDOCsynthetic electron capture\\n' > build/test-renderdoc-electron-html-gate-wrong-electron/source/electron.rdc && printf '{\"width\":2,\"height\":2,\"format\":\"argb-u32\",\"producer\":\"electron-chromium-capture\",\"nativeWidth\":2,\"nativeHeight\":2,\"pixels\":[4294967295,4278190335,4294967295,4294967295]}\\n' > build/test-renderdoc-electron-html-gate-wrong-electron/source/electron_argb.json && printf 'rdoc_backend=electron\\nrdoc_scene=html-css-electron\\nrdoc_capture_status=pass\\nrdoc_capture_reason=pass\\nrdoc_capture_file=build/test-renderdoc-electron-html-gate-wrong-electron/source/electron.rdc\\nrdoc_capture_magic=RDOC\\nrdoc_html_path=test/fixtures/html_css/generated_gui_vulkan_renderdoc_fixture.html\\nrdoc_electron=/tmp/not-simple-electron\\nrdoc_electron_capture_script=tools/electron-live-bitmap/capture_html_argb.js\\nrdoc_electron_argb=build/test-renderdoc-electron-html-gate-wrong-electron/source/electron_argb.json\\nrdoc_electron_width=2\\nrdoc_electron_height=2\\nrdoc_chromium_requested_api=vulkan\\nrdoc_chromium_requested_angle=vulkan\\nrdoc_chromium_requested_features=Vulkan\\nrdoc_chromium_launch_flags=--no-sandbox --disable-gpu-sandbox --enable-features=Vulkan --use-angle=vulkan\\n' > build/test-renderdoc-electron-html-gate-wrong-electron/source/evidence.env && RDOC_ELECTRON_HTML_EVIDENCE_ENV=build/test-renderdoc-electron-html-gate-wrong-electron/source/evidence.env BUILD_DIR=build/test-renderdoc-electron-html-gate-wrong-electron/out REPORT_PATH=build/test-renderdoc-electron-html-gate-wrong-electron/report.md sh scripts/check/check-renderdoc-electron-html-gate.shs || true"
val (_stdout, _stderr, code) = rt_process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val evidence = rt_file_read_text("build/test-renderdoc-electron-html-gate-wrong-electron/out/evidence.env") ?? ""
expect(evidence).to_contain("rdoc_electron_html_gate_status=fail")
expect(evidence).to_contain("rdoc_electron_html_gate_reason=unexpected-electron-binary")
expect(evidence).to_contain("rdoc_electron_html_gate_electron=/tmp/not-simple-electron")
expect(evidence).to_contain("rdoc_electron_html_gate_required_electron_suffix=tools/electron-shell/node_modules/electron/dist/Electron.app/Contents/MacOS/Electron|tools/electron-shell/node_modules/.bin/electron")
```

</details>

#### rejects Electron captures whose file header is not RDOC

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val command = "rm -rf build/test-renderdoc-electron-html-gate-bad-file-magic && mkdir -p build/test-renderdoc-electron-html-gate-bad-file-magic/source && printf 'NOPEsynthetic electron capture\\n' > build/test-renderdoc-electron-html-gate-bad-file-magic/source/electron.rdc && printf 'rdoc_backend=electron\\nrdoc_scene=html-css-electron\\nrdoc_capture_status=pass\\nrdoc_capture_reason=pass\\nrdoc_capture_file=build/test-renderdoc-electron-html-gate-bad-file-magic/source/electron.rdc\\nrdoc_capture_magic=RDOC\\nrdoc_html_path=test/fixtures/html_css/generated_gui_vulkan_renderdoc_fixture.html\\nrdoc_electron=tools/electron-shell/node_modules/electron/dist/Electron.app/Contents/MacOS/Electron\\nrdoc_electron_capture_script=tools/electron-live-bitmap/capture_html_argb.js\\nrdoc_chromium_requested_api=vulkan\\nrdoc_chromium_requested_angle=vulkan\\nrdoc_chromium_requested_features=Vulkan\\nrdoc_chromium_launch_flags=--no-sandbox --disable-gpu-sandbox --enable-features=Vulkan --use-angle=vulkan\\n' > build/test-renderdoc-electron-html-gate-bad-file-magic/source/evidence.env && RDOC_ELECTRON_HTML_EVIDENCE_ENV=build/test-renderdoc-electron-html-gate-bad-file-magic/source/evidence.env BUILD_DIR=build/test-renderdoc-electron-html-gate-bad-file-magic/out REPORT_PATH=build/test-renderdoc-electron-html-gate-bad-file-magic/report.md sh scripts/check/check-renderdoc-electron-html-gate.shs || true"
val (_stdout, _stderr, code) = rt_process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val evidence = rt_file_read_text("build/test-renderdoc-electron-html-gate-bad-file-magic/out/evidence.env") ?? ""
expect(evidence).to_contain("rdoc_electron_html_gate_status=fail")
expect(evidence).to_contain("rdoc_electron_html_gate_reason=missing-rdoc-file-magic")
expect(evidence).to_contain("rdoc_electron_html_gate_capture_magic=RDOC")
expect(evidence).to_contain("rdoc_electron_html_gate_capture_file_magic=NOPE")
```

</details>

#### rejects Electron captures whose log proves Vulkan ANGLE was unavailable

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val command = "rm -rf build/test-renderdoc-electron-html-gate-vulkan-log-fail && mkdir -p build/test-renderdoc-electron-html-gate-vulkan-log-fail/source && printf 'RDOCsynthetic electron capture\\n' > build/test-renderdoc-electron-html-gate-vulkan-log-fail/source/electron.rdc && printf '{\"width\":2,\"height\":2,\"format\":\"argb-u32\",\"producer\":\"electron-chromium-capture\",\"nativeWidth\":2,\"nativeHeight\":2,\"pixels\":[4294967295,4278190335,4294967295,4294967295]}\\n' > build/test-renderdoc-electron-html-gate-vulkan-log-fail/source/electron_argb.json && printf '[1:1:ERROR:gl_factory.cc(102)] Requested GL implementation (gl=egl-angle,angle=vulkan) not found in allowed implementations: [(gl=egl-angle,angle=metal)]\\n[1:1:ERROR:viz_main_impl.cc(181)] Exiting GPU process due to errors during initialization\\n' > build/test-renderdoc-electron-html-gate-vulkan-log-fail/source/renderdoc-electron-html.log && printf 'rdoc_backend=electron\\nrdoc_scene=html-css-electron\\nrdoc_capture_status=pass\\nrdoc_capture_reason=pass\\nrdoc_capture_file=build/test-renderdoc-electron-html-gate-vulkan-log-fail/source/electron.rdc\\nrdoc_capture_magic=RDOC\\nrdoc_html_path=test/fixtures/html_css/generated_gui_vulkan_renderdoc_fixture.html\\nrdoc_electron=tools/electron-shell/node_modules/electron/dist/Electron.app/Contents/MacOS/Electron\\nrdoc_electron_capture_script=tools/electron-live-bitmap/capture_html_argb.js\\nrdoc_electron_argb=build/test-renderdoc-electron-html-gate-vulkan-log-fail/source/electron_argb.json\\nrdoc_electron_width=2\\nrdoc_electron_height=2\\nrdoc_chromium_requested_api=vulkan\\nrdoc_chromium_requested_angle=vulkan\\nrdoc_chromium_requested_features=Vulkan\\nrdoc_chromium_launch_flags=--no-sandbox --disable-gpu-sandbox --enable-features=Vulkan --use-angle=vulkan\\nrdoc_log=build/test-renderdoc-electron-html-gate-vulkan-log-fail/source/renderdoc-electron-html.log\\n' > build/test-renderdoc-electron-html-gate-vulkan-log-fail/source/evidence.env && RDOC_ELECTRON_HTML_EVIDENCE_ENV=build/test-renderdoc-electron-html-gate-vulkan-log-fail/source/evidence.env BUILD_DIR=build/test-renderdoc-electron-html-gate-vulkan-log-fail/out REPORT_PATH=build/test-renderdoc-electron-html-gate-vulkan-log-fail/report.md sh scripts/check/check-renderdoc-electron-html-gate.shs || true"
val (_stdout, _stderr, code) = rt_process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val evidence = rt_file_read_text("build/test-renderdoc-electron-html-gate-vulkan-log-fail/out/evidence.env") ?? ""
expect(evidence).to_contain("rdoc_electron_html_gate_status=fail")
expect(evidence).to_contain("rdoc_electron_html_gate_reason=vulkan-angle-unavailable")
expect(evidence).to_contain("rdoc_electron_html_gate_vulkan_log_status=fail")
expect(evidence).to_contain("rdoc_electron_html_gate_vulkan_log_reason=vulkan-angle-unavailable")
expect(evidence).to_contain("rdoc_electron_html_gate_log=build/test-renderdoc-electron-html-gate-vulkan-log-fail/source/renderdoc-electron-html.log")
```

</details>

#### rejects Electron captures missing the Vulkan ANGLE launch flag

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val command = "rm -rf build/test-renderdoc-electron-html-gate-missing-angle && mkdir -p build/test-renderdoc-electron-html-gate-missing-angle/source && printf 'RDOCsynthetic electron capture\\n' > build/test-renderdoc-electron-html-gate-missing-angle/source/electron.rdc && printf 'rdoc_backend=electron\\nrdoc_scene=html-css-electron\\nrdoc_capture_status=pass\\nrdoc_capture_reason=pass\\nrdoc_capture_file=build/test-renderdoc-electron-html-gate-missing-angle/source/electron.rdc\\nrdoc_capture_magic=RDOC\\nrdoc_html_path=test/fixtures/html_css/generated_gui_vulkan_renderdoc_fixture.html\\nrdoc_electron=tools/electron-shell/node_modules/electron/dist/Electron.app/Contents/MacOS/Electron\\nrdoc_electron_capture_script=tools/electron-live-bitmap/capture_html_argb.js\\nrdoc_chromium_requested_api=vulkan\\nrdoc_chromium_requested_angle=vulkan\\nrdoc_chromium_requested_features=Vulkan\\nrdoc_chromium_launch_flags=--no-sandbox --disable-gpu-sandbox --enable-features=Vulkan\\n' > build/test-renderdoc-electron-html-gate-missing-angle/source/evidence.env && RDOC_ELECTRON_HTML_EVIDENCE_ENV=build/test-renderdoc-electron-html-gate-missing-angle/source/evidence.env BUILD_DIR=build/test-renderdoc-electron-html-gate-missing-angle/out REPORT_PATH=build/test-renderdoc-electron-html-gate-missing-angle/report.md sh scripts/check/check-renderdoc-electron-html-gate.shs || true"
val (_stdout, _stderr, code) = rt_process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val evidence = rt_file_read_text("build/test-renderdoc-electron-html-gate-missing-angle/out/evidence.env") ?? ""
expect(evidence).to_contain("rdoc_electron_html_gate_status=fail")
expect(evidence).to_contain("rdoc_electron_html_gate_reason=missing-vulkan-angle-flag")
```

</details>

#### rejects Electron captures missing the Vulkan requested feature field

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val command = "rm -rf build/test-renderdoc-electron-html-gate-missing-feature && mkdir -p build/test-renderdoc-electron-html-gate-missing-feature/source && printf 'RDOCsynthetic electron capture\\n' > build/test-renderdoc-electron-html-gate-missing-feature/source/electron.rdc && printf 'rdoc_backend=electron\\nrdoc_scene=html-css-electron\\nrdoc_capture_status=pass\\nrdoc_capture_reason=pass\\nrdoc_capture_file=build/test-renderdoc-electron-html-gate-missing-feature/source/electron.rdc\\nrdoc_capture_magic=RDOC\\nrdoc_html_path=test/fixtures/html_css/generated_gui_vulkan_renderdoc_fixture.html\\nrdoc_electron=tools/electron-shell/node_modules/electron/dist/Electron.app/Contents/MacOS/Electron\\nrdoc_electron_capture_script=tools/electron-live-bitmap/capture_html_argb.js\\nrdoc_chromium_requested_api=vulkan\\nrdoc_chromium_requested_angle=vulkan\\nrdoc_chromium_requested_features=\\nrdoc_chromium_launch_flags=--no-sandbox --disable-gpu-sandbox --enable-features=Vulkan --use-angle=vulkan\\n' > build/test-renderdoc-electron-html-gate-missing-feature/source/evidence.env && RDOC_ELECTRON_HTML_EVIDENCE_ENV=build/test-renderdoc-electron-html-gate-missing-feature/source/evidence.env BUILD_DIR=build/test-renderdoc-electron-html-gate-missing-feature/out REPORT_PATH=build/test-renderdoc-electron-html-gate-missing-feature/report.md sh scripts/check/check-renderdoc-electron-html-gate.shs || true"
val (_stdout, _stderr, code) = rt_process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val evidence = rt_file_read_text("build/test-renderdoc-electron-html-gate-missing-feature/out/evidence.env") ?? ""
expect(evidence).to_contain("rdoc_electron_html_gate_status=fail")
expect(evidence).to_contain("rdoc_electron_html_gate_reason=missing-vulkan-requested-feature")
expect(evidence).to_contain("rdoc_electron_html_gate_requested_features=")
expect(evidence).to_contain("rdoc_electron_html_gate_required_features=Vulkan")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** [doc/03_plan/sys_test/html_css_spec_traceability.md](doc/03_plan/sys_test/html_css_spec_traceability.md)
- **Design:** [doc/07_guide/tooling/renderdoc_capture_infra.md](doc/07_guide/tooling/renderdoc_capture_infra.md)
- **Research:** [doc/09_report/electron_vulkan_renderdoc_debug_2026-06-17.md](doc/09_report/electron_vulkan_renderdoc_debug_2026-06-17.md)


</details>
