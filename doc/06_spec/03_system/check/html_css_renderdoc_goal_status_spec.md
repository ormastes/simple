# HTML/CSS RenderDoc goal status gate

> Validates the aggregate status gate for the full HTML/CSS traceability and RenderDoc objective. The local host may or may not have durable Simple RenderDoc `.rdc` evidence in `build/`, so the spec checks the current-state failure contract and separately proves the aggregate pass path with controlled fixture evidence.

<!-- sdn-diagram:id=html_css_renderdoc_goal_status_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=html_css_renderdoc_goal_status_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

html_css_renderdoc_goal_status_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=html_css_renderdoc_goal_status_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# HTML/CSS RenderDoc goal status gate

Validates the aggregate status gate for the full HTML/CSS traceability and RenderDoc objective. The local host may or may not have durable Simple RenderDoc `.rdc` evidence in `build/`, so the spec checks the current-state failure contract and separately proves the aggregate pass path with controlled fixture evidence.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Requirements | N/A |
| Plan | doc/03_plan/agent_tasks/vulkan_backed_web_gui_renderdoc_parallel_plan.md |
| Design | doc/07_guide/tooling/renderdoc_capture_infra.md |
| Research | doc/09_report/gui_renderdoc_feature_coverage_status_2026-06-25.md |
| Source | `test/03_system/check/html_css_renderdoc_goal_status_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Validates the aggregate status gate for the full HTML/CSS traceability and
RenderDoc objective. The local host may or may not have durable Simple
RenderDoc `.rdc` evidence in `build/`, so the spec checks the current-state
failure contract and separately proves the aggregate pass path with controlled
fixture evidence.

**Plan:** doc/03_plan/agent_tasks/vulkan_backed_web_gui_renderdoc_parallel_plan.md
**Requirements:** N/A
**Research:** doc/09_report/gui_renderdoc_feature_coverage_status_2026-06-25.md
**Design:** doc/07_guide/tooling/renderdoc_capture_infra.md

## Syntax

```sh
BUILD_DIR=build/test-html-css-renderdoc-goal-status \
REPORT_PATH=build/test-html-css-renderdoc-goal-status/report.md \
sh scripts/check/check-html-css-renderdoc-goal-status.shs || true
```

## Acceptance

- The gate writes stable `html_css_*`, `simple_renderdoc_*`,
  `external_renderdoc_*`, `electron_renderdoc_*`, and
  `macos_portability_*` evidence keys.
- The gate requires typed HTML/CSS SSpec traceability evidence to pass.
- The gate includes the rendering manifest traceability proof for the 50-case
  Electron/Simple layout fixture matrix.
- Simple RenderDoc evidence is accepted only when `.rdc` magic is `RDOC`.
- Simple RenderDoc evidence must pass the dedicated Simple Vulkan gate.
- Simple RenderDoc evidence must include Vulkan runtime backend, RenderDoc API
  start/availability, capture count, and pixel-count proof from the probe log.
- The full goal remains failed until the original external RenderDoc gate
  passes.
- The full goal remains failed until the Electron Chromium/Vulkan RenderDoc
  gate also proves `.rdc` magic and nonblank ARGB rendered pixels.
- The gate reports every unsatisfied RenderDoc goal completion lane through
  `renderdoc_goal_blocked_gate*` evidence fields.
- Controlled Simple and external-host fixtures can drive the aggregate gate to
  `pass` without depending on stale local build artifacts.
- The controlled pass path reuses fresh traceability and rendering-manifest
  evidence from the current-state path instead of rerunning those nested checks.
- Configured traceability evidence paths fail closed when the evidence file is
  missing.

## Scenarios

### HTML/CSS RenderDoc goal status gate

#### reports the current evidence state without assuming stale local captures

- Run the aggregate RenderDoc goal-status gate in an isolated build directory
   - Expected: code equals `0`
- Read the current evidence contract emitted by the gate
- Assert that missing local captures fail closed instead of passing by assumption
   - Expected: traceability_status equals `pass`
   - Expected: traceability_html_count equals `105`
   - Expected: simple_status equals `pass`
   - Expected: simple_gate_status equals `pass`
   - Expected: external_status equals `pass`
   - Expected: electron_gate_status equals `pass`
   - Expected: blocked_gate equals ``
   - Expected: blocked_gate_count equals `0`
   - Expected: blocked_gates equals ``
   - Expected: goal_status equals `fail`
   - Expected: goal_reason equals `simple_reason`
   - Expected: simple_status equals `fail`
   - Expected: simple_reason equals `missing-simple-rdoc`
   - Expected: goal_reason equals `original-renderdoc-evidence-missing`
   - Expected: external_status equals `unavailable`
   - Expected: goal_reason equals `electron_gate_reason`
   - Expected: electron_gate_status == "pass" is false
- Verify the operator report was written


<details>
<summary>Executable SSpec</summary>

Runnable source: 162 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Run the aggregate RenderDoc goal-status gate in an isolated build directory")
val command = "rm -rf build/test-html-css-renderdoc-goal-status && BUILD_DIR=build/test-html-css-renderdoc-goal-status REPORT_PATH=build/test-html-css-renderdoc-goal-status/report.md sh scripts/check/check-html-css-renderdoc-goal-status.shs || true"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

step("Read the current evidence contract emitted by the gate")
val evidence = file_read("build/test-html-css-renderdoc-goal-status/evidence.env")
expect(evidence).to_contain("html_css_renderdoc_goal_status=")
expect(evidence).to_contain("html_css_traceability_status=pass")
expect(evidence).to_contain("html_css_traceability_reason=pass")
expect(evidence).to_contain("html_css_traceability_command=sh scripts/check/check-html-css-sspec-traceability.shs")
expect(evidence).to_contain("html_css_traceability_evidence_env=build/test-html-css-renderdoc-goal-status/sspec-traceability/evidence.env")
expect(evidence).to_contain("html_css_traceability_required_html_tag_count=105")
expect(evidence).to_contain("html_css_traceability_required_css_property_min_count=390")
expect(evidence).to_contain("html_css_traceability_implemented_css_property_count=63")
expect(evidence).to_contain("html_css_rendering_manifest_traceability_status=pass")
expect(evidence).to_contain("html_css_rendering_manifest_traceability_command=sh scripts/check/check-html-css-rendering-manifest-traceability.shs")
expect(evidence).to_contain("simple_renderdoc_status=")
expect(evidence).to_contain("simple_renderdoc_gate_status=")
expect(evidence).to_contain("simple_renderdoc_gate_reason=")
expect(evidence).to_contain("simple_renderdoc_gate_required_backend=simple")
expect(evidence).to_contain("simple_renderdoc_gate_required_scene=vulkan-engine2d")
expect(evidence).to_contain("simple_renderdoc_gate_required_program=src/app/test/renderdoc_vulkan_capture.spl")
expect(evidence).to_contain("simple_renderdoc_gate_required_status=pass")
expect(evidence).to_contain("simple_renderdoc_gate_required_magic=RDOC")
expect(evidence).to_contain("simple_renderdoc_gate_required_runtime_backend=vulkan")
expect(evidence).to_contain("simple_renderdoc_gate_required_renderdoc_available=1")
expect(evidence).to_contain("simple_renderdoc_gate_required_renderdoc_start=1")
expect(evidence).to_contain("simple_renderdoc_gate_required_renderdoc_end_recorded=1")
expect(evidence).to_contain("simple_renderdoc_gate_required_num_captures_min=1")
expect(evidence).to_contain("simple_renderdoc_gate_required_pixel_count_min=1")
expect(evidence).to_contain("simple_renderdoc_capture_file_magic=")
expect(evidence).to_contain("simple_renderdoc_gate_capture_file_magic=")
expect(evidence).to_contain("simple_renderdoc_gate_runtime_backend=")
expect(evidence).to_contain("simple_renderdoc_gate_renderdoc_available=")
expect(evidence).to_contain("simple_renderdoc_gate_renderdoc_start=")
expect(evidence).to_contain("simple_renderdoc_gate_renderdoc_end=")
expect(evidence).to_contain("simple_renderdoc_gate_renderdoc_num_captures=")
expect(evidence).to_contain("simple_renderdoc_gate_pixel_count=")
expect(evidence).to_contain("simple_renderdoc_gate_runtime_metadata_status=")
expect(evidence).to_contain("simple_renderdoc_gate_missing_runtime_metadata=")
expect(evidence).to_contain("external_renderdoc_status=")
expect(evidence).to_contain("external_renderdoc_capture_env=")
expect(evidence).to_contain("external_renderdoc_capture_status=")
expect(evidence).to_contain("external_renderdoc_capture_reason=")
expect(evidence).to_contain("external_renderdoc_capture_file=")
expect(evidence).to_contain("external_renderdoc_capture_magic=")
expect(evidence).to_contain("external_renderdoc_capture_file_magic=")
expect(evidence).to_contain("external_renderdoc_capture_html_path=")
expect(evidence).to_contain("external_renderdoc_gate_status=")
expect(evidence).to_contain("external_renderdoc_gate_reason=")
expect(evidence).to_contain("external_renderdoc_gate_capture_file_magic=")
expect(evidence).to_contain("external_renderdoc_gate_requested_api=")
expect(evidence).to_contain("external_renderdoc_gate_requested_angle=")
expect(evidence).to_contain("external_renderdoc_gate_requested_features=")
expect(evidence).to_contain("external_renderdoc_gate_launch_flags=")
expect(evidence).to_contain("electron_renderdoc_gate_status=")
expect(evidence).to_contain("electron_renderdoc_gate_reason=")
expect(evidence).to_contain("electron_renderdoc_gate_required_backend=electron")
expect(evidence).to_contain("electron_renderdoc_gate_required_scene=html-css-electron")
expect(evidence).to_contain("electron_renderdoc_gate_required_status=pass")
expect(evidence).to_contain("electron_renderdoc_gate_required_magic=RDOC")
expect(evidence).to_contain("electron_renderdoc_gate_required_api=vulkan")
expect(evidence).to_contain("electron_renderdoc_gate_required_angle=vulkan")
expect(evidence).to_contain("electron_renderdoc_gate_required_features=Vulkan")
expect(evidence).to_contain("electron_renderdoc_gate_required_electron_suffix=tools/electron-shell/node_modules/electron/dist/Electron.app/Contents/MacOS/Electron|tools/electron-shell/node_modules/.bin/electron")
expect(evidence).to_contain("electron_renderdoc_gate_required_argb_status=pass")
expect(evidence).to_contain("electron_renderdoc_gate_required_argb_format=argb-u32")
expect(evidence).to_contain("electron_renderdoc_gate_required_argb_producer=electron-chromium-capture")
expect(evidence).to_contain("electron_renderdoc_gate_required_argb_nonblank_pixel_count_min=1")
expect(evidence).to_contain("electron_renderdoc_gate_argb_status=")
expect(evidence).to_contain("electron_renderdoc_gate_argb_pixel_count=")
expect(evidence).to_contain("electron_renderdoc_gate_argb_nonblank_pixel_count=")
expect(evidence).to_contain("electron_renderdoc_gate_log=")
expect(evidence).to_contain("electron_renderdoc_gate_vulkan_log_status=")
expect(evidence).to_contain("electron_renderdoc_gate_vulkan_log_reason=")
expect(evidence).to_contain("macos_portability_status=")
expect(evidence).to_contain("macos_portability_reason=")
expect(evidence).to_contain("macos_portability_evidence_env=")
expect(evidence).to_contain("macos_portability_uname_s=")
expect(evidence).to_contain("macos_portability_uname_m=")
expect(evidence).to_contain("macos_portability_version=")
expect(evidence).to_contain("macos_portability_gpu_summary=")
expect(evidence).to_contain("macos_portability_vulkan_status=")
expect(evidence).to_contain("macos_portability_vulkan_device=")
expect(evidence).to_contain("macos_portability_vulkan_driver=")
expect(evidence).to_contain("macos_portability_renderdoc_status=")
expect(evidence).to_contain("macos_portability_run_captures=")
expect(evidence).to_contain("macos_portability_capture_simple_status=")
expect(evidence).to_contain("macos_portability_capture_html_status=")
expect(evidence).to_contain("macos_portability_html_gate_status=")
expect(evidence).to_contain("macos_portability_capture_electron_status=")
expect(evidence).to_contain("macos_portability_electron_gate_status=")
expect(evidence).to_contain("required_external_backend=original")
expect(evidence).to_contain("required_external_scene=html-css-chrome")
expect(evidence).to_contain("required_external_status=pass")
expect(evidence).to_contain("required_external_magic=RDOC")
expect(evidence).to_contain("required_external_api=vulkan")
expect(evidence).to_contain("required_external_angle=vulkan")
expect(evidence).to_contain("required_external_features=Vulkan")
expect(evidence).to_contain("required_external_html_path_suffix=test/fixtures/html_css/generated_gui_vulkan_renderdoc_fixture.html")
expect(evidence).to_contain("required_external_launch_flag_enable_features=--enable-features=Vulkan")
expect(evidence).to_contain("required_external_launch_flag_use_angle=--use-angle=vulkan")
expect(evidence).to_contain("renderdoc_goal_blocked_gate=")
expect(evidence).to_contain("renderdoc_goal_blocked_gate_count=")
expect(evidence).to_contain("renderdoc_goal_blocked_gates=")

val goal_status = _value_of(evidence, "html_css_renderdoc_goal_status")
val goal_reason = _value_of(evidence, "html_css_renderdoc_goal_reason")
val traceability_status = _value_of(evidence, "html_css_traceability_status")
val traceability_html_count = _value_of(evidence, "html_css_traceability_html_tag_count")
val traceability_css_count = _value_of(evidence, "html_css_traceability_css_property_count")
val simple_status = _value_of(evidence, "simple_renderdoc_status")
val simple_reason = _value_of(evidence, "simple_renderdoc_reason")
val simple_gate_status = _value_of(evidence, "simple_renderdoc_gate_status")
val external_status = _value_of(evidence, "external_renderdoc_status")
val electron_gate_status = _value_of(evidence, "electron_renderdoc_gate_status")
val electron_gate_reason = _value_of(evidence, "electron_renderdoc_gate_reason")
val macos_host = _value_of(evidence, "macos_portability_uname_s")
val macos_vulkan_status = _value_of(evidence, "macos_portability_vulkan_status")
val macos_renderdoc_status = _value_of(evidence, "macos_portability_renderdoc_status")
val blocked_gate = _value_of(evidence, "renderdoc_goal_blocked_gate")
val blocked_gate_count = _value_of(evidence, "renderdoc_goal_blocked_gate_count")
val blocked_gates = _value_of(evidence, "renderdoc_goal_blocked_gates")

step("Assert that missing local captures fail closed instead of passing by assumption")
expect(traceability_status).to_equal("pass")
expect(traceability_html_count).to_equal("105")
expect(traceability_css_count.to_i64()).to_be_greater_than(389)
if macos_host == "Darwin":
    expect(macos_vulkan_status.len()).to_be_greater_than(0)
    expect(macos_renderdoc_status.len()).to_be_greater_than(0)
if goal_status == "pass":
    expect(simple_status).to_equal("pass")
    expect(simple_gate_status).to_equal("pass")
    expect(external_status).to_equal("pass")
    expect(electron_gate_status).to_equal("pass")
    expect(blocked_gate).to_equal("")
    expect(blocked_gate_count).to_equal("0")
    expect(blocked_gates).to_equal("")
else:
    expect(goal_status).to_equal("fail")
    expect(blocked_gate.len()).to_be_greater_than(0)
    expect(blocked_gate_count.to_i64()).to_be_greater_than(0)
    expect(blocked_gates).to_contain(blocked_gate)
    if simple_status != "pass":
        expect(goal_reason).to_equal(simple_reason)
        expect(simple_status).to_equal("fail")
        expect(simple_reason).to_equal("missing-simple-rdoc")
    else if external_status != "pass":
        expect(goal_reason).to_equal("original-renderdoc-evidence-missing")
        expect(external_status).to_equal("unavailable")
    else:
        expect(goal_reason).to_equal(electron_gate_reason)
        expect(electron_gate_status == "pass").to_equal(false)

step("Verify the operator report was written")
val report = file_read("build/test-html-css-renderdoc-goal-status/report.md")
expect(report).to_contain("# HTML/CSS RenderDoc Goal Status")
expect(report).to_contain("- HTML/CSS traceability: pass (pass)")
expect(report).to_contain("- HTML/CSS rendering manifest traceability: pass (pass)")
expect(report).to_contain("- blocked completion gates:")
```

</details>

#### passes with controlled Simple RDOC, original external-host, and Electron evidence

- Create controlled Simple, external-host, and Electron RenderDoc evidence fixtures
   - Expected: code equals `0`
- Assert the aggregate gate accepts only the complete controlled evidence set


<details>
<summary>Executable SSpec</summary>

Runnable source: 71 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Create controlled Simple, external-host, and Electron RenderDoc evidence fixtures")
val command = "rm -rf build/test-html-css-renderdoc-goal-status-pass && mkdir -p build/test-html-css-renderdoc-goal-status-pass/simple build/test-html-css-renderdoc-goal-status-pass/external/capture/html build/test-html-css-renderdoc-goal-status-pass/electron && printf 'RDOCsynthetic simple capture\\n' > build/test-html-css-renderdoc-goal-status-pass/simple/simple.rdc && printf 'RDOCsynthetic external capture\\n' > build/test-html-css-renderdoc-goal-status-pass/external/capture/html/html.rdc && printf 'RDOCsynthetic electron capture\\n' > build/test-html-css-renderdoc-goal-status-pass/electron/electron.rdc && printf '{\"width\":2,\"height\":2,\"format\":\"argb-u32\",\"producer\":\"electron-chromium-capture\",\"nativeWidth\":2,\"nativeHeight\":2,\"pixels\":[4294967295,4278190335,4294967295,4294967295]}\\n' > build/test-html-css-renderdoc-goal-status-pass/electron/electron_argb.json && printf 'rdoc_backend=simple\\nrdoc_scene=vulkan-engine2d\\nrdoc_program=src/app/test/renderdoc_vulkan_capture.spl\\nrdoc_capture_status=pass\\nrdoc_capture_reason=pass\\nrdoc_capture_file=build/test-html-css-renderdoc-goal-status-pass/simple/simple.rdc\\nrdoc_capture_magic=RDOC\\nrdoc_simple_runtime_backend=vulkan\\nrdoc_simple_renderdoc_available=1\\nrdoc_simple_renderdoc_start=1\\nrdoc_simple_renderdoc_end=1\\nrdoc_simple_renderdoc_num_captures=1\\nrdoc_simple_pixel_count=3072\\n' > build/test-html-css-renderdoc-goal-status-pass/simple/evidence.env && printf 'rdoc_external_host_capture_status=pass\\nrdoc_external_host_capture_reason=pass\\nrdoc_external_host_capture_env=build/test-html-css-renderdoc-goal-status-pass/external/capture/html/evidence.env\\nrdoc_external_host_capture_status_raw=pass\\nrdoc_external_host_capture_reason_raw=pass\\nrdoc_external_host_capture_file=build/test-html-css-renderdoc-goal-status-pass/external/capture/html/html.rdc\\nrdoc_external_host_capture_magic=RDOC\\nrdoc_external_host_capture_html_path=test/fixtures/html_css/generated_gui_vulkan_renderdoc_fixture.html\\nrdoc_external_host_gate_status=pass\\nrdoc_external_host_gate_reason=pass\\nrdoc_external_host_gate_scene=html-css-chrome\\nrdoc_external_host_gate_html_path=test/fixtures/html_css/generated_gui_vulkan_renderdoc_fixture.html\\nrdoc_external_host_gate_requested_api=vulkan\\nrdoc_external_host_gate_requested_angle=vulkan\\nrdoc_external_host_gate_requested_features=Vulkan\\nrdoc_external_host_gate_launch_flags=--no-sandbox --disable-gpu-sandbox --disable-dev-shm-usage --enable-features=Vulkan --use-angle=vulkan\\nrdoc_external_host_required_backend=original\\nrdoc_external_host_required_scene=html-css-chrome\\nrdoc_external_host_required_status=pass\\nrdoc_external_host_required_magic=RDOC\\nrdoc_external_host_required_api=vulkan\\nrdoc_external_host_required_angle=vulkan\\nrdoc_external_host_required_features=Vulkan\\nrdoc_external_host_required_html_path_suffix=test/fixtures/html_css/generated_gui_vulkan_renderdoc_fixture.html\\nrdoc_external_host_required_launch_flag_enable_features=--enable-features=Vulkan\\nrdoc_external_host_required_launch_flag_use_angle=--use-angle=vulkan\\n' > build/test-html-css-renderdoc-goal-status-pass/external/evidence.env && printf 'rdoc_backend=electron\\nrdoc_scene=html-css-electron\\nrdoc_capture_status=pass\\nrdoc_capture_reason=pass\\nrdoc_capture_file=build/test-html-css-renderdoc-goal-status-pass/electron/electron.rdc\\nrdoc_capture_magic=RDOC\\nrdoc_html_path=test/fixtures/html_css/generated_gui_vulkan_renderdoc_fixture.html\\nrdoc_electron=tools/electron-shell/node_modules/.bin/electron\\nrdoc_electron_capture_script=tools/electron-live-bitmap/capture_html_argb.js\\nrdoc_electron_argb=build/test-html-css-renderdoc-goal-status-pass/electron/electron_argb.json\\nrdoc_electron_width=2\\nrdoc_electron_height=2\\nrdoc_chromium_requested_api=vulkan\\nrdoc_chromium_requested_angle=vulkan\\nrdoc_chromium_requested_features=Vulkan\\nrdoc_chromium_launch_flags=--enable-features=Vulkan --use-angle=vulkan\\n' > build/test-html-css-renderdoc-goal-status-pass/electron/evidence.env && HTML_CSS_TRACEABILITY_EVIDENCE_ENV=build/test-html-css-renderdoc-goal-status/sspec-traceability/evidence.env HTML_CSS_RENDERING_MANIFEST_TRACEABILITY_ENV=build/test-html-css-renderdoc-goal-status/rendering-manifest/evidence.env RDOC_SIMPLE_EVIDENCE_ENV=build/test-html-css-renderdoc-goal-status-pass/simple/evidence.env RDOC_EXTERNAL_CAPTURE_EVIDENCE_ENV=build/test-html-css-renderdoc-goal-status-pass/external/evidence.env RDOC_ELECTRON_EVIDENCE_ENV=build/test-html-css-renderdoc-goal-status-pass/electron/evidence.env BUILD_DIR=build/test-html-css-renderdoc-goal-status-pass/out REPORT_PATH=build/test-html-css-renderdoc-goal-status-pass/report.md sh scripts/check/check-html-css-renderdoc-goal-status.shs"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

step("Assert the aggregate gate accepts only the complete controlled evidence set")
val evidence = file_read("build/test-html-css-renderdoc-goal-status-pass/out/evidence.env")
expect(evidence).to_contain("html_css_renderdoc_goal_status=pass")
expect(evidence).to_contain("html_css_renderdoc_goal_reason=pass")
expect(evidence).to_contain("html_css_traceability_status=pass")
expect(evidence).to_contain("html_css_rendering_manifest_traceability_status=pass")
expect(evidence).to_contain("simple_renderdoc_status=pass")
expect(evidence).to_contain("simple_renderdoc_capture_file_magic=RDOC")
expect(evidence).to_contain("simple_renderdoc_gate_status=pass")
expect(evidence).to_contain("simple_renderdoc_gate_capture_file_magic=RDOC")
expect(evidence).to_contain("simple_renderdoc_gate_runtime_backend=vulkan")
expect(evidence).to_contain("simple_renderdoc_gate_renderdoc_available=1")
expect(evidence).to_contain("simple_renderdoc_gate_renderdoc_start=1")
expect(evidence).to_contain("simple_renderdoc_gate_renderdoc_end=1")
expect(evidence).to_contain("simple_renderdoc_gate_renderdoc_num_captures=1")
expect(evidence).to_contain("simple_renderdoc_gate_pixel_count=3072")
expect(evidence).to_contain("simple_renderdoc_gate_runtime_metadata_status=pass")
expect(evidence).to_contain("simple_renderdoc_gate_missing_runtime_metadata=")
expect(evidence).to_contain("external_renderdoc_status=pass")
expect(evidence).to_contain("external_renderdoc_capture_status=pass")
expect(evidence).to_contain("external_renderdoc_capture_magic=RDOC")
expect(evidence).to_contain("external_renderdoc_capture_file_magic=RDOC")
expect(evidence).to_contain("external_renderdoc_capture_file=build/test-html-css-renderdoc-goal-status-pass/external/capture/html/html.rdc")
expect(evidence).to_contain("external_renderdoc_capture_html_path=test/fixtures/html_css/generated_gui_vulkan_renderdoc_fixture.html")
expect(evidence).to_contain("external_renderdoc_gate_status=pass")
expect(evidence).to_contain("external_renderdoc_gate_scene=html-css-chrome")
expect(evidence).to_contain("external_renderdoc_gate_html_path=test/fixtures/html_css/generated_gui_vulkan_renderdoc_fixture.html")
expect(evidence).to_contain("external_renderdoc_gate_capture_file_magic=RDOC")
expect(evidence).to_contain("external_renderdoc_gate_requested_api=vulkan")
expect(evidence).to_contain("external_renderdoc_gate_requested_angle=vulkan")
expect(evidence).to_contain("external_renderdoc_gate_requested_features=Vulkan")
expect(evidence).to_contain("external_renderdoc_gate_launch_flags=--no-sandbox --disable-gpu-sandbox --disable-dev-shm-usage --enable-features=Vulkan --use-angle=vulkan")
expect(evidence).to_contain("electron_renderdoc_gate_status=pass")
expect(evidence).to_contain("electron_renderdoc_gate_reason=pass")
expect(evidence).to_contain("electron_renderdoc_gate_backend=electron")
expect(evidence).to_contain("electron_renderdoc_gate_scene=html-css-electron")
expect(evidence).to_contain("electron_renderdoc_gate_capture_status=pass")
expect(evidence).to_contain("electron_renderdoc_gate_capture_magic=RDOC")
expect(evidence).to_contain("electron_renderdoc_gate_capture_file_magic=RDOC")
expect(evidence).to_contain("electron_renderdoc_gate_argb_status=pass")
expect(evidence).to_contain("electron_renderdoc_gate_argb_format=argb-u32")
expect(evidence).to_contain("electron_renderdoc_gate_argb_producer=electron-chromium-capture")
expect(evidence).to_contain("electron_renderdoc_gate_argb_pixel_count=4")
expect(evidence).to_contain("electron_renderdoc_gate_argb_nonblank_pixel_count=1")
expect(evidence).to_contain("electron_renderdoc_gate_requested_api=vulkan")
expect(evidence).to_contain("electron_renderdoc_gate_requested_angle=vulkan")
expect(evidence).to_contain("electron_renderdoc_gate_requested_features=Vulkan")
expect(evidence).to_contain("electron_renderdoc_gate_required_electron_suffix=tools/electron-shell/node_modules/electron/dist/Electron.app/Contents/MacOS/Electron|tools/electron-shell/node_modules/.bin/electron")
expect(evidence).to_contain("electron_renderdoc_gate_required_argb_status=pass")
expect(evidence).to_contain("electron_renderdoc_gate_required_argb_format=argb-u32")
expect(evidence).to_contain("electron_renderdoc_gate_required_argb_producer=electron-chromium-capture")
expect(evidence).to_contain("electron_renderdoc_gate_required_argb_nonblank_pixel_count_min=1")
expect(evidence).to_contain("electron_renderdoc_gate_required_vulkan_log_no_angle_failure=1")
expect(evidence).to_contain("required_external_backend=original")
expect(evidence).to_contain("required_external_scene=html-css-chrome")
expect(evidence).to_contain("required_external_status=pass")
expect(evidence).to_contain("required_external_magic=RDOC")
expect(evidence).to_contain("required_external_api=vulkan")
expect(evidence).to_contain("required_external_angle=vulkan")
expect(evidence).to_contain("required_external_features=Vulkan")
expect(evidence).to_contain("required_external_html_path_suffix=test/fixtures/html_css/generated_gui_vulkan_renderdoc_fixture.html")
expect(evidence).to_contain("required_external_launch_flag_enable_features=--enable-features=Vulkan")
expect(evidence).to_contain("required_external_launch_flag_use_angle=--use-angle=vulkan")
expect(evidence).to_contain("renderdoc_goal_blocked_gate=")
expect(evidence).to_contain("renderdoc_goal_blocked_gate_count=0")
expect(evidence).to_contain("renderdoc_goal_blocked_gates=")
```

</details>

#### fails closed for missing configured traceability evidence files

- Run the aggregate gate with configured but missing reusable evidence
   - Expected: code equals `0`
- Assert configured missing files do not fall back to stale generated evidence


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Run the aggregate gate with configured but missing reusable evidence")
val command = "rm -rf build/test-html-css-renderdoc-goal-status-missing-configured && HTML_CSS_TRACEABILITY_EVIDENCE_ENV=build/test-html-css-renderdoc-goal-status-missing-configured/missing-traceability.env HTML_CSS_RENDERING_MANIFEST_TRACEABILITY_ENV=build/test-html-css-renderdoc-goal-status-missing-configured/missing-rendering-manifest.env BUILD_DIR=build/test-html-css-renderdoc-goal-status-missing-configured REPORT_PATH=build/test-html-css-renderdoc-goal-status-missing-configured/report.md sh scripts/check/check-html-css-renderdoc-goal-status.shs || true"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

step("Assert configured missing files do not fall back to stale generated evidence")
val evidence = file_read("build/test-html-css-renderdoc-goal-status-missing-configured/evidence.env")
expect(evidence).to_contain("html_css_renderdoc_goal_status=fail")
expect(evidence).to_contain("html_css_traceability_status=fail")
expect(evidence).to_contain("html_css_traceability_reason=missing-configured-html-css-traceability-evidence")
expect(evidence).to_contain("html_css_traceability_evidence_env=build/test-html-css-renderdoc-goal-status-missing-configured/missing-traceability.env")
expect(evidence).to_contain("html_css_rendering_manifest_traceability_status=fail")
expect(evidence).to_contain("html_css_rendering_manifest_traceability_reason=missing-configured-html-css-rendering-manifest-traceability-evidence")
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

- **Plan:** [doc/03_plan/agent_tasks/vulkan_backed_web_gui_renderdoc_parallel_plan.md](doc/03_plan/agent_tasks/vulkan_backed_web_gui_renderdoc_parallel_plan.md)
- **Design:** [doc/07_guide/tooling/renderdoc_capture_infra.md](doc/07_guide/tooling/renderdoc_capture_infra.md)
- **Research:** [doc/09_report/gui_renderdoc_feature_coverage_status_2026-06-25.md](doc/09_report/gui_renderdoc_feature_coverage_status_2026-06-25.md)


</details>
