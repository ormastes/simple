# GUI Widget RenderDoc Goal Status Gate

> Validates the status wrapper that ties all GUI widget fixture witnesses to the Mac RenderDoc/Vulkan proof lanes. The wrapper is intentionally non-launching: it composes the widget fixture coverage gate with existing Simple Engine2D RenderDoc and Electron Chromium/Vulkan RenderDoc gates.

<!-- sdn-diagram:id=gui_widget_renderdoc_goal_status_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=gui_widget_renderdoc_goal_status_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

gui_widget_renderdoc_goal_status_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=gui_widget_renderdoc_goal_status_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# GUI Widget RenderDoc Goal Status Gate

Validates the status wrapper that ties all GUI widget fixture witnesses to the Mac RenderDoc/Vulkan proof lanes. The wrapper is intentionally non-launching: it composes the widget fixture coverage gate with existing Simple Engine2D RenderDoc and Electron Chromium/Vulkan RenderDoc gates.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Requirements | N/A |
| Plan | N/A |
| Design | doc/07_guide/tooling/renderdoc_capture_infra.md |
| Research | N/A |
| Source | `test/03_system/check/gui_widget_renderdoc_goal_status_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Validates the status wrapper that ties all GUI widget fixture witnesses to the
Mac RenderDoc/Vulkan proof lanes. The wrapper is intentionally non-launching:
it composes the widget fixture coverage gate with existing Simple Engine2D
RenderDoc and Electron Chromium/Vulkan RenderDoc gates.

**Plan:** N/A
**Requirements:** N/A
**Research:** N/A
**Architecture:** doc/04_architecture/ui/simple_gui_stack.md
**Design:** doc/07_guide/tooling/renderdoc_capture_infra.md

## Syntax

```sh
BUILD_DIR=build/test-gui-widget-renderdoc-goal-status \
REPORT_PATH=build/test-gui-widget-renderdoc-goal-status/report.md \
sh scripts/check/check-gui-widget-renderdoc-goal-status.shs
```

## Acceptance

- The wrapper reports 43/43 GUI widget RenderDoc HTML fixture feature
  witnesses from `generated_gui_vulkan_renderdoc_fixture.html`.
- Without live macOS RenderDoc evidence, the wrapper remains `incomplete` and
  names the blocked Simple and Electron widget RenderDoc gates.
- With valid synthetic child gate evidence, the wrapper reports `pass`, zero
  blocked gates, Simple Vulkan runtime proof, and Electron Chromium/Vulkan ARGB
  nonblank proof for the widget fixture.
- Simple child gate evidence must include the generated widget fixture path and
  a positive `rdoc_simple_widget_html_bytes` value; a generic Simple Vulkan
  `.rdc` row is not enough to satisfy the widget-specific gate.
- Synthetic `.rdc` and Electron ARGB artifact rows must name regular files,
  not symlinks, before the aggregate widget RenderDoc goal can pass.
- When Electron produces a nonblank ARGB proof but no `.rdc`, GPU process exit
  diagnostics from the Electron RenderDoc log are preserved in parent evidence.

## Evidence Flow

The wrapper is a composition gate. It does not launch RenderDoc directly during
normal status checks; it reads the child evidence paths and runs the child
validators against them. The widget fixture validator proves the generated HTML
fixture contains every expected widget feature witness. The Simple child gate
proves the widget fixture was captured by the Simple Vulkan Engine2D path and
that the capture file starts with `RDOC`. The Electron child gate proves the
same widget fixture was rendered by Electron Chromium with Vulkan/ANGLE launch
fields, a nonblank ARGB bitmap, and a real `.rdc` capture.

The parent status remains `incomplete` when the fixture and one child gate pass
but another child gate is missing. That distinction is important: `fail` is for
bad or contradictory fixture evidence, while `incomplete` is for host/platform
capture evidence that still needs to be collected on a prepared machine.

## Operator Checks

Start with `gui_widget_renderdoc_goal_status`. A pass requires
`gui_widget_renderdoc_goal_blocked_gate_count=0`,
`gui_widget_renderdoc_goal_simple_gate_status=pass`, and
`gui_widget_renderdoc_goal_electron_gate_status=pass`.

For Simple evidence, check `gui_widget_renderdoc_goal_simple_gate_capture_file_status`,
`gui_widget_renderdoc_goal_simple_gate_capture_file_magic`, and
`gui_widget_renderdoc_goal_simple_gate_runtime_backend`. They must prove a
regular `RDOC` file and Vulkan runtime backend for
`src/app/test/renderdoc_vulkan_widget_capture.spl`.

For Electron evidence, check `gui_widget_renderdoc_goal_electron_gate_capture_file_status`,
`gui_widget_renderdoc_goal_electron_gate_capture_file_magic`,
`gui_widget_renderdoc_goal_electron_gate_argb_status`, and
`gui_widget_renderdoc_goal_electron_gate_requested_angle`. A nonblank ARGB file
with missing `.rdc` still blocks completion because bitmap proof is not native
RenderDoc proof.

## Failure Triage

If `gui_widget_renderdoc_goal_electron_gate_failure_class` is
`electron-gate-missing-rdc`, inspect the forwarded GPU process exit fields.
`gui_widget_renderdoc_goal_electron_gate_gpu_process_exit_status=fail` with
`gui_widget_renderdoc_goal_electron_gate_gpu_process_exit_codes=139` means the
Electron GPU process crashed while RenderDoc/Vulkan was configured. Preserve
that as a platform capture blocker until a prepared Electron/RenderDoc host
produces a regular `.rdc` whose first bytes are `RDOC`.

If the ARGB fields fail, fix the Electron live bitmap path first; there is no
useful RenderDoc comparison without a nonblank widget render. If the widget
feature count is not 43, fix the generated fixture coverage before spending time
on platform capture.

## Non-Goals

This wrapper does not claim pixel equivalence, browser backend parity, or full
platform completion. Those are handled by the broader GUI RenderDoc aggregate,
Linux Vulkan render-log comparison, macOS Metal comparison, Windows D3D12
comparison, and production GUI/Web renderer parity gates.

## Completion Checklist

Before marking the widget RenderDoc lane complete, save the report path, confirm
the blocked gate count is zero, confirm both child capture files are regular
files with `RDOC` magic, and confirm the widget feature list still contains all
43 expected entries. If any one of those checks is missing, keep the lane open.

## Scenarios

### GUI widget RenderDoc goal status gate

#### reports current widget coverage and live RenderDoc lanes

- Run the GUI widget RenderDoc goal status wrapper
   - Expected: code equals `0`
- Read the emitted evidence contract
- Assert representative widget RenderDoc feature witnesses
   - Expected: features.split(",").len() equals `43`
   - Expected: blocked_gates equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 60 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Run the GUI widget RenderDoc goal status wrapper")
val command = "rm -rf build/test-gui-widget-renderdoc-goal-status-current && BUILD_DIR=build/test-gui-widget-renderdoc-goal-status-current REPORT_PATH=build/test-gui-widget-renderdoc-goal-status-current/report.md sh scripts/check/check-gui-widget-renderdoc-goal-status.shs"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

step("Read the emitted evidence contract")
val evidence = file_read("build/test-gui-widget-renderdoc-goal-status-current/evidence.env")
expect(evidence).to_contain("gui_widget_renderdoc_goal_status=")
expect(evidence).to_contain("gui_widget_renderdoc_goal_widget_fixture_status=pass")
expect(evidence).to_contain("gui_widget_renderdoc_goal_widget_count=43")
expect(evidence).to_contain("gui_widget_renderdoc_goal_widget_feature_covered_count=43")
expect(evidence).to_contain("gui_widget_renderdoc_goal_missing_widget_features=")
expect(evidence).to_contain("gui_widget_renderdoc_goal_simple_gate_status=")
expect(evidence).to_contain("gui_widget_renderdoc_goal_simple_gate_capture_command=RDOC_OUTPUT_DIR=build/renderdoc/widget-probe-small RDOC_SIMPLE_PROG=\"$PWD/src/app/test/renderdoc_vulkan_widget_capture.spl\" RDOC_HTML_PATH=\"$PWD/test/fixtures/html_css/generated_gui_vulkan_renderdoc_fixture.html\" scripts/tool/renderdoc-evidence.shs capture-simple")
expect(evidence).to_contain("gui_widget_renderdoc_goal_simple_gate_source_env_file_status=")
expect(evidence).to_contain("gui_widget_renderdoc_goal_simple_gate_capture_file_status=")
expect(evidence).to_contain("gui_widget_renderdoc_goal_electron_gate_status=")
expect(evidence).to_contain("gui_widget_renderdoc_goal_electron_gate_capture_command=RDOC_OUTPUT_DIR=build/renderdoc/electron-implicit-layer-default-autocapture RDOC_HTML_PATH=\"$PWD/test/fixtures/html_css/generated_gui_vulkan_renderdoc_fixture.html\" scripts/tool/renderdoc-evidence.shs capture-electron-html")
expect(evidence).to_contain("gui_widget_renderdoc_goal_electron_gate_source_env_file_status=")
expect(evidence).to_contain("gui_widget_renderdoc_goal_electron_gate_capture_file_status=")
expect(evidence).to_contain("gui_widget_renderdoc_goal_electron_gate_argb_file_status=")
expect(evidence).to_contain("gui_widget_renderdoc_goal_electron_gate_failure_class=")
expect(evidence).to_contain("gui_widget_renderdoc_goal_blocked_gate_count=")

step("Assert representative widget RenderDoc feature witnesses")
val features = _value_of(evidence, "gui_widget_renderdoc_goal_widget_features")
expect(features.split(",").len()).to_equal(43)
expect(features).to_contain("button:command-action")
expect(features).to_contain("search_bar:search-input")
expect(features).to_contain("glass_title_bar:window-titlebar")
expect(features).to_contain("command_palette:command-search")
expect(features).to_contain("empty_state:empty-feedback")

val blocked_gates = _value_of(evidence, "gui_widget_renderdoc_goal_blocked_gates")
val simple_status = _value_of(evidence, "gui_widget_renderdoc_goal_simple_gate_status")
val electron_argb_file_status = _value_of(evidence, "gui_widget_renderdoc_goal_electron_gate_argb_file_status")
val electron_argb_status = _value_of(evidence, "gui_widget_renderdoc_goal_electron_gate_argb_status")
if simple_status != "pass":
    expect(blocked_gates).to_contain("Simple GUI widget RenderDoc .rdc on Vulkan Engine2D")
val widget_status = _value_of(evidence, "gui_widget_renderdoc_goal_status")
if widget_status == "pass":
    expect(blocked_gates).to_equal("")
else:
    expect(blocked_gates).to_contain("Electron Chromium-on-Vulkan widget RenderDoc .rdc")
    if electron_argb_file_status == "pass" && electron_argb_status == "pass":
        expect(blocked_gates).to_contain("Electron Chromium-on-Vulkan widget RenderDoc .rdc capture (ARGB proof already present)")
    else:
        expect(blocked_gates).to_contain("Electron Chromium-on-Vulkan widget RenderDoc .rdc with nonblank ARGB proof")

val report = file_read("build/test-gui-widget-renderdoc-goal-status-current/report.md")
expect(report).to_contain("# GUI Widget RenderDoc Goal Status")
expect(report).to_contain("- widgets with RenderDoc fixture features: 43 / 43")
expect(report).to_contain("- Simple source evidence file:")
expect(report).to_contain("- Simple capture artifact:")
expect(report).to_contain("- Simple widget fixture:")
expect(report).to_contain("- Simple runtime backend:")
expect(report).to_contain("- Electron source evidence file:")
expect(report).to_contain("- Electron capture artifact:")
expect(report).to_contain("- Electron ARGB artifact:")
expect(report).to_contain("- Electron requested Vulkan:")
```

</details>

#### passes when Simple and Electron widget RenderDoc evidence is present

- Create synthetic Simple and Electron RenderDoc gate inputs
   - Expected: code equals `0`
- Assert the pass contract joins widget, Simple, and Electron proof


<details>
<summary>Executable SSpec</summary>

Runnable source: 47 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Create synthetic Simple and Electron RenderDoc gate inputs")
val command = "rm -rf build/test-gui-widget-renderdoc-goal-status-pass && mkdir -p build/test-gui-widget-renderdoc-goal-status-pass/simple build/test-gui-widget-renderdoc-goal-status-pass/electron && printf 'RDOCsynthetic simple capture\\n' > build/test-gui-widget-renderdoc-goal-status-pass/simple/simple.rdc && printf 'RDOCsynthetic electron capture\\n' > build/test-gui-widget-renderdoc-goal-status-pass/electron/electron.rdc && printf '{\"width\":2,\"height\":2,\"format\":\"argb-u32\",\"producer\":\"electron-chromium-capture\",\"nativeWidth\":2,\"nativeHeight\":2,\"pixels\":[4294967295,4278190335,4294967295,4294967295]}\\n' > build/test-gui-widget-renderdoc-goal-status-pass/electron/electron_argb.json && printf 'rdoc_backend=simple\\nrdoc_scene=vulkan-engine2d\\nrdoc_program=src/app/test/renderdoc_vulkan_widget_capture.spl\\nrdoc_capture_status=pass\\nrdoc_capture_reason=pass\\nrdoc_capture_file=build/test-gui-widget-renderdoc-goal-status-pass/simple/simple.rdc\\nrdoc_capture_magic=RDOC\\nrdoc_simple_runtime_backend=vulkan\\nrdoc_simple_renderdoc_available=1\\nrdoc_simple_renderdoc_start=1\\nrdoc_simple_renderdoc_end=1\\nrdoc_simple_renderdoc_num_captures=1\\nrdoc_simple_pixel_count=3072\\nrdoc_simple_widget_html_path=test/fixtures/html_css/generated_gui_vulkan_renderdoc_fixture.html\\nrdoc_simple_widget_html_bytes=4096\\n' > build/test-gui-widget-renderdoc-goal-status-pass/simple/evidence.env && printf 'rdoc_backend=electron\\nrdoc_scene=html-css-electron\\nrdoc_capture_status=pass\\nrdoc_capture_reason=pass\\nrdoc_capture_file=build/test-gui-widget-renderdoc-goal-status-pass/electron/electron.rdc\\nrdoc_capture_magic=RDOC\\nrdoc_html_path=test/fixtures/html_css/generated_gui_vulkan_renderdoc_fixture.html\\nrdoc_electron=tools/electron-shell/node_modules/electron/dist/Electron.app/Contents/MacOS/Electron\\nrdoc_electron_capture_script=tools/electron-live-bitmap/capture_html_argb.js\\nrdoc_electron_argb=build/test-gui-widget-renderdoc-goal-status-pass/electron/electron_argb.json\\nrdoc_electron_width=2\\nrdoc_electron_height=2\\nrdoc_chromium_requested_api=vulkan\\nrdoc_chromium_requested_angle=vulkan\\nrdoc_chromium_requested_features=Vulkan\\nrdoc_chromium_launch_flags=--no-sandbox --disable-gpu-sandbox --enable-features=Vulkan --use-angle=vulkan\\n' > build/test-gui-widget-renderdoc-goal-status-pass/electron/evidence.env && RDOC_SIMPLE_EVIDENCE_ENV=build/test-gui-widget-renderdoc-goal-status-pass/simple/evidence.env RDOC_ELECTRON_HTML_EVIDENCE_ENV=build/test-gui-widget-renderdoc-goal-status-pass/electron/evidence.env BUILD_DIR=build/test-gui-widget-renderdoc-goal-status-pass/out REPORT_PATH=build/test-gui-widget-renderdoc-goal-status-pass/report.md sh scripts/check/check-gui-widget-renderdoc-goal-status.shs --strict"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

step("Assert the pass contract joins widget, Simple, and Electron proof")
val evidence = file_read("build/test-gui-widget-renderdoc-goal-status-pass/out/evidence.env")
expect(evidence).to_contain("gui_widget_renderdoc_goal_status=pass")
expect(evidence).to_contain("gui_widget_renderdoc_goal_reason=pass")
expect(evidence).to_contain("gui_widget_renderdoc_goal_widget_fixture_status=pass")
expect(evidence).to_contain("gui_widget_renderdoc_goal_widget_count=43")
expect(evidence).to_contain("gui_widget_renderdoc_goal_widget_feature_covered_count=43")
expect(evidence).to_contain("gui_widget_renderdoc_goal_simple_gate_status=pass")
expect(evidence).to_contain("gui_widget_renderdoc_goal_simple_gate_capture_command=RDOC_OUTPUT_DIR=build/renderdoc/widget-probe-small RDOC_SIMPLE_PROG=\"$PWD/src/app/test/renderdoc_vulkan_widget_capture.spl\" RDOC_HTML_PATH=\"$PWD/test/fixtures/html_css/generated_gui_vulkan_renderdoc_fixture.html\" scripts/tool/renderdoc-evidence.shs capture-simple")
expect(evidence).to_contain("gui_widget_renderdoc_goal_simple_gate_source_env_file_status=pass")
expect(evidence).to_contain("gui_widget_renderdoc_goal_simple_gate_capture_file_status=pass")
expect(evidence).to_contain("gui_widget_renderdoc_goal_simple_gate_capture_file_magic=RDOC")
expect(evidence).to_contain("gui_widget_renderdoc_goal_simple_gate_runtime_backend=vulkan")
expect(evidence).to_contain("gui_widget_renderdoc_goal_simple_gate_widget_html_bytes=4096")
expect(evidence).to_contain("gui_widget_renderdoc_goal_simple_gate_widget_html_bytes_status=pass")
expect(evidence).to_contain("gui_widget_renderdoc_goal_electron_gate_status=pass")
expect(evidence).to_contain("gui_widget_renderdoc_goal_electron_gate_capture_command=RDOC_OUTPUT_DIR=build/renderdoc/electron-implicit-layer-default-autocapture RDOC_HTML_PATH=\"$PWD/test/fixtures/html_css/generated_gui_vulkan_renderdoc_fixture.html\" scripts/tool/renderdoc-evidence.shs capture-electron-html")
expect(evidence).to_contain("gui_widget_renderdoc_goal_electron_gate_failure_class=pass")
expect(evidence).to_contain("gui_widget_renderdoc_goal_electron_gate_source_env_file_status=pass")
expect(evidence).to_contain("gui_widget_renderdoc_goal_electron_gate_fixture_path_status=pass")
expect(evidence).to_contain("gui_widget_renderdoc_goal_electron_gate_capture_file_status=pass")
expect(evidence).to_contain("gui_widget_renderdoc_goal_electron_gate_capture_file_magic=RDOC")
expect(evidence).to_contain("gui_widget_renderdoc_goal_electron_gate_argb_file_status=pass")
expect(evidence).to_contain("gui_widget_renderdoc_goal_electron_gate_argb_status=pass")
expect(evidence).to_contain("gui_widget_renderdoc_goal_electron_gate_argb_nonblank_pixel_count=1")
expect(evidence).to_contain("gui_widget_renderdoc_goal_electron_gate_requested_api=vulkan")
expect(evidence).to_contain("gui_widget_renderdoc_goal_electron_gate_requested_angle=vulkan")
expect(evidence).to_contain("gui_widget_renderdoc_goal_electron_gate_requested_features=Vulkan")
expect(evidence).to_contain("gui_widget_renderdoc_goal_blocked_gate_count=0")
expect(evidence).to_contain("gui_widget_renderdoc_goal_blocked_gates=")

val report = file_read("build/test-gui-widget-renderdoc-goal-status-pass/report.md")
expect(report).to_contain("- status: pass")
expect(report).to_contain("- Simple source evidence file: pass")
expect(report).to_contain("- Simple capture artifact: pass / RDOC")
expect(report).to_contain("- Simple widget fixture: pass; html bytes 4096 (pass)")
expect(report).to_contain("- Simple runtime backend: vulkan; required vulkan")
expect(report).to_contain("- Electron source evidence file: pass")
expect(report).to_contain("- Electron capture artifact: pass / RDOC")
expect(report).to_contain("- Electron ARGB artifact: pass / pass; nonblank 1")
expect(report).to_contain("- Electron requested Vulkan: api=vulkan angle=vulkan features=Vulkan")
expect(report).to_contain("- blocked gates: 0")
```

</details>

#### rejects symlinked widget RenderDoc artifacts

- Create otherwise-valid child evidence with symlinked RDOC and ARGB artifacts
   - Expected: code equals `0`
- Assert aggregate evidence rejects the symlinked artifacts


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Create otherwise-valid child evidence with symlinked RDOC and ARGB artifacts")
val command = "rm -rf build/test-gui-widget-renderdoc-goal-status-symlink-artifacts && mkdir -p build/test-gui-widget-renderdoc-goal-status-symlink-artifacts/simple build/test-gui-widget-renderdoc-goal-status-symlink-artifacts/electron && printf 'RDOCsynthetic simple capture\\n' > build/test-gui-widget-renderdoc-goal-status-symlink-artifacts/simple/simple-real.rdc && ln -s simple-real.rdc build/test-gui-widget-renderdoc-goal-status-symlink-artifacts/simple/simple.rdc && printf 'RDOCsynthetic electron capture\\n' > build/test-gui-widget-renderdoc-goal-status-symlink-artifacts/electron/electron-real.rdc && ln -s electron-real.rdc build/test-gui-widget-renderdoc-goal-status-symlink-artifacts/electron/electron.rdc && printf '{\"width\":2,\"height\":2,\"format\":\"argb-u32\",\"producer\":\"electron-chromium-capture\",\"nativeWidth\":2,\"nativeHeight\":2,\"pixels\":[4294967295,4278190335,4294967295,4294967295]}\\n' > build/test-gui-widget-renderdoc-goal-status-symlink-artifacts/electron/electron_argb-real.json && ln -s electron_argb-real.json build/test-gui-widget-renderdoc-goal-status-symlink-artifacts/electron/electron_argb.json && printf 'rdoc_backend=simple\\nrdoc_scene=vulkan-engine2d\\nrdoc_program=src/app/test/renderdoc_vulkan_widget_capture.spl\\nrdoc_capture_status=pass\\nrdoc_capture_reason=pass\\nrdoc_capture_file=build/test-gui-widget-renderdoc-goal-status-symlink-artifacts/simple/simple.rdc\\nrdoc_capture_magic=RDOC\\nrdoc_simple_runtime_backend=vulkan\\nrdoc_simple_renderdoc_available=1\\nrdoc_simple_renderdoc_start=1\\nrdoc_simple_renderdoc_end=1\\nrdoc_simple_renderdoc_num_captures=1\\nrdoc_simple_pixel_count=3072\\nrdoc_simple_widget_html_path=test/fixtures/html_css/generated_gui_vulkan_renderdoc_fixture.html\\nrdoc_simple_widget_html_bytes=4096\\n' > build/test-gui-widget-renderdoc-goal-status-symlink-artifacts/simple/evidence.env && printf 'rdoc_backend=electron\\nrdoc_scene=html-css-electron\\nrdoc_capture_status=pass\\nrdoc_capture_reason=pass\\nrdoc_capture_file=build/test-gui-widget-renderdoc-goal-status-symlink-artifacts/electron/electron.rdc\\nrdoc_capture_magic=RDOC\\nrdoc_html_path=test/fixtures/html_css/generated_gui_vulkan_renderdoc_fixture.html\\nrdoc_electron=tools/electron-shell/node_modules/electron/dist/Electron.app/Contents/MacOS/Electron\\nrdoc_electron_capture_script=tools/electron-live-bitmap/capture_html_argb.js\\nrdoc_electron_argb=build/test-gui-widget-renderdoc-goal-status-symlink-artifacts/electron/electron_argb.json\\nrdoc_electron_width=2\\nrdoc_electron_height=2\\nrdoc_chromium_requested_api=vulkan\\nrdoc_chromium_requested_angle=vulkan\\nrdoc_chromium_requested_features=Vulkan\\nrdoc_chromium_launch_flags=--no-sandbox --disable-gpu-sandbox --enable-features=Vulkan --use-angle=vulkan\\n' > build/test-gui-widget-renderdoc-goal-status-symlink-artifacts/electron/evidence.env && RDOC_SIMPLE_EVIDENCE_ENV=build/test-gui-widget-renderdoc-goal-status-symlink-artifacts/simple/evidence.env RDOC_ELECTRON_HTML_EVIDENCE_ENV=build/test-gui-widget-renderdoc-goal-status-symlink-artifacts/electron/evidence.env BUILD_DIR=build/test-gui-widget-renderdoc-goal-status-symlink-artifacts/out REPORT_PATH=build/test-gui-widget-renderdoc-goal-status-symlink-artifacts/report.md sh scripts/check/check-gui-widget-renderdoc-goal-status.shs"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

step("Assert aggregate evidence rejects the symlinked artifacts")
val evidence = file_read("build/test-gui-widget-renderdoc-goal-status-symlink-artifacts/out/evidence.env")
expect(evidence).to_contain("gui_widget_renderdoc_goal_status=incomplete")
expect(evidence).to_contain("gui_widget_renderdoc_goal_reason=missing-simple-widget-renderdoc")
expect(evidence).to_contain("gui_widget_renderdoc_goal_simple_gate_status=fail")
expect(evidence).to_contain("gui_widget_renderdoc_goal_simple_gate_reason=rdc-file-symlink")
expect(evidence).to_contain("gui_widget_renderdoc_goal_simple_gate_capture_file_status=symlink")
expect(evidence).to_contain("gui_widget_renderdoc_goal_electron_gate_status=fail")
expect(evidence).to_contain("gui_widget_renderdoc_goal_electron_gate_reason=rdc-file-symlink")
expect(evidence).to_contain("gui_widget_renderdoc_goal_electron_gate_failure_class=electron-gate-rdc-file-symlink")
expect(evidence).to_contain("gui_widget_renderdoc_goal_electron_gate_capture_file_status=symlink")
expect(evidence).to_contain("gui_widget_renderdoc_goal_electron_gate_argb_file_status=symlink")
expect(evidence).to_contain("gui_widget_renderdoc_goal_electron_gate_argb_status=fail")
expect(evidence).to_contain("gui_widget_renderdoc_goal_blocked_gate_count=2")
expect(evidence).to_contain("Simple GUI widget RenderDoc .rdc on Vulkan Engine2D")
expect(evidence).to_contain("Electron Chromium-on-Vulkan widget RenderDoc .rdc capture (ARGB proof already present)")
```

</details>

#### forwards the Electron child gate failure class for missing ARGB proof

- Create controlled Electron evidence without ARGB proof
   - Expected: code equals `0`
- Assert parent evidence carries the child gate root cause


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Create controlled Electron evidence without ARGB proof")
val command = "rm -rf build/test-gui-widget-renderdoc-goal-status-missing-argb && mkdir -p build/test-gui-widget-renderdoc-goal-status-missing-argb/simple build/test-gui-widget-renderdoc-goal-status-missing-argb/electron && printf 'RDOCsynthetic simple capture\\n' > build/test-gui-widget-renderdoc-goal-status-missing-argb/simple/simple.rdc && printf 'RDOCsynthetic electron capture\\n' > build/test-gui-widget-renderdoc-goal-status-missing-argb/electron/electron.rdc && printf 'rdoc_backend=simple\\nrdoc_scene=vulkan-engine2d\\nrdoc_program=src/app/test/renderdoc_vulkan_widget_capture.spl\\nrdoc_capture_status=pass\\nrdoc_capture_reason=pass\\nrdoc_capture_file=build/test-gui-widget-renderdoc-goal-status-missing-argb/simple/simple.rdc\\nrdoc_capture_magic=RDOC\\nrdoc_simple_runtime_backend=vulkan\\nrdoc_simple_renderdoc_available=1\\nrdoc_simple_renderdoc_start=1\\nrdoc_simple_renderdoc_end=1\\nrdoc_simple_renderdoc_num_captures=1\\nrdoc_simple_pixel_count=3072\\nrdoc_simple_widget_html_path=test/fixtures/html_css/generated_gui_vulkan_renderdoc_fixture.html\\nrdoc_simple_widget_html_bytes=4096\\n' > build/test-gui-widget-renderdoc-goal-status-missing-argb/simple/evidence.env && printf 'rdoc_backend=electron\\nrdoc_scene=html-css-electron\\nrdoc_capture_status=pass\\nrdoc_capture_reason=pass\\nrdoc_capture_file=build/test-gui-widget-renderdoc-goal-status-missing-argb/electron/electron.rdc\\nrdoc_capture_magic=RDOC\\nrdoc_html_path=test/fixtures/html_css/generated_gui_vulkan_renderdoc_fixture.html\\nrdoc_electron=tools/electron-shell/node_modules/electron/dist/Electron.app/Contents/MacOS/Electron\\nrdoc_electron_capture_script=tools/electron-live-bitmap/capture_html_argb.js\\nrdoc_electron_argb=build/test-gui-widget-renderdoc-goal-status-missing-argb/electron/missing_argb.json\\nrdoc_electron_width=2\\nrdoc_electron_height=2\\nrdoc_chromium_requested_api=vulkan\\nrdoc_chromium_requested_angle=vulkan\\nrdoc_chromium_requested_features=Vulkan\\nrdoc_chromium_launch_flags=--no-sandbox --disable-gpu-sandbox --enable-features=Vulkan --use-angle=vulkan\\n' > build/test-gui-widget-renderdoc-goal-status-missing-argb/electron/evidence.env && RDOC_SIMPLE_EVIDENCE_ENV=build/test-gui-widget-renderdoc-goal-status-missing-argb/simple/evidence.env RDOC_ELECTRON_HTML_EVIDENCE_ENV=build/test-gui-widget-renderdoc-goal-status-missing-argb/electron/evidence.env BUILD_DIR=build/test-gui-widget-renderdoc-goal-status-missing-argb/out REPORT_PATH=build/test-gui-widget-renderdoc-goal-status-missing-argb/report.md sh scripts/check/check-gui-widget-renderdoc-goal-status.shs"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

step("Assert parent evidence carries the child gate root cause")
val evidence = file_read("build/test-gui-widget-renderdoc-goal-status-missing-argb/out/evidence.env")
expect(evidence).to_contain("gui_widget_renderdoc_goal_status=incomplete")
expect(evidence).to_contain("gui_widget_renderdoc_goal_reason=missing-electron-widget-renderdoc")
expect(evidence).to_contain("gui_widget_renderdoc_goal_simple_gate_status=pass")
expect(evidence).to_contain("gui_widget_renderdoc_goal_electron_gate_status=fail")
expect(evidence).to_contain("gui_widget_renderdoc_goal_electron_gate_reason=missing-electron-argb-file")
expect(evidence).to_contain("gui_widget_renderdoc_goal_electron_gate_failure_class=electron-gate-missing-electron-argb-file")
expect(evidence).to_contain("gui_widget_renderdoc_goal_electron_gate_argb_file_status=missing")
expect(evidence).to_contain("gui_widget_renderdoc_goal_blocked_gate_count=1")
```

</details>

#### rejects Simple widget RDOC evidence without widget HTML byte proof

- Create Simple widget RDOC evidence with a fixture path but no byte count
   - Expected: code equals `0`
- Assert missing widget HTML bytes keeps the Simple widget gate incomplete


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Create Simple widget RDOC evidence with a fixture path but no byte count")
val command = "rm -rf build/test-gui-widget-renderdoc-goal-status-missing-widget-bytes && mkdir -p build/test-gui-widget-renderdoc-goal-status-missing-widget-bytes/simple build/test-gui-widget-renderdoc-goal-status-missing-widget-bytes/electron && printf 'RDOCsynthetic simple capture\\n' > build/test-gui-widget-renderdoc-goal-status-missing-widget-bytes/simple/simple.rdc && printf 'RDOCsynthetic electron capture\\n' > build/test-gui-widget-renderdoc-goal-status-missing-widget-bytes/electron/electron.rdc && printf '{\"width\":2,\"height\":2,\"format\":\"argb-u32\",\"producer\":\"electron-chromium-capture\",\"nativeWidth\":2,\"nativeHeight\":2,\"pixels\":[4294967295,4278190335,4294967295,4294967295]}\\n' > build/test-gui-widget-renderdoc-goal-status-missing-widget-bytes/electron/electron_argb.json && printf 'rdoc_backend=simple\\nrdoc_scene=vulkan-engine2d\\nrdoc_program=src/app/test/renderdoc_vulkan_widget_capture.spl\\nrdoc_capture_status=pass\\nrdoc_capture_reason=pass\\nrdoc_capture_file=build/test-gui-widget-renderdoc-goal-status-missing-widget-bytes/simple/simple.rdc\\nrdoc_capture_magic=RDOC\\nrdoc_simple_runtime_backend=vulkan\\nrdoc_simple_renderdoc_available=1\\nrdoc_simple_renderdoc_start=1\\nrdoc_simple_renderdoc_end=1\\nrdoc_simple_renderdoc_num_captures=1\\nrdoc_simple_pixel_count=3072\\nrdoc_simple_widget_html_path=test/fixtures/html_css/generated_gui_vulkan_renderdoc_fixture.html\\n' > build/test-gui-widget-renderdoc-goal-status-missing-widget-bytes/simple/evidence.env && printf 'rdoc_backend=electron\\nrdoc_scene=html-css-electron\\nrdoc_capture_status=pass\\nrdoc_capture_reason=pass\\nrdoc_capture_file=build/test-gui-widget-renderdoc-goal-status-missing-widget-bytes/electron/electron.rdc\\nrdoc_capture_magic=RDOC\\nrdoc_html_path=test/fixtures/html_css/generated_gui_vulkan_renderdoc_fixture.html\\nrdoc_electron=tools/electron-shell/node_modules/electron/dist/Electron.app/Contents/MacOS/Electron\\nrdoc_electron_capture_script=tools/electron-live-bitmap/capture_html_argb.js\\nrdoc_electron_argb=build/test-gui-widget-renderdoc-goal-status-missing-widget-bytes/electron/electron_argb.json\\nrdoc_electron_width=2\\nrdoc_electron_height=2\\nrdoc_chromium_requested_api=vulkan\\nrdoc_chromium_requested_angle=vulkan\\nrdoc_chromium_requested_features=Vulkan\\nrdoc_chromium_launch_flags=--no-sandbox --disable-gpu-sandbox --enable-features=Vulkan --use-angle=vulkan\\n' > build/test-gui-widget-renderdoc-goal-status-missing-widget-bytes/electron/evidence.env && RDOC_SIMPLE_EVIDENCE_ENV=build/test-gui-widget-renderdoc-goal-status-missing-widget-bytes/simple/evidence.env RDOC_ELECTRON_HTML_EVIDENCE_ENV=build/test-gui-widget-renderdoc-goal-status-missing-widget-bytes/electron/evidence.env BUILD_DIR=build/test-gui-widget-renderdoc-goal-status-missing-widget-bytes/out REPORT_PATH=build/test-gui-widget-renderdoc-goal-status-missing-widget-bytes/report.md sh scripts/check/check-gui-widget-renderdoc-goal-status.shs"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

step("Assert missing widget HTML bytes keeps the Simple widget gate incomplete")
val evidence = file_read("build/test-gui-widget-renderdoc-goal-status-missing-widget-bytes/out/evidence.env")
expect(evidence).to_contain("gui_widget_renderdoc_goal_status=incomplete")
expect(evidence).to_contain("gui_widget_renderdoc_goal_reason=missing-simple-widget-renderdoc")
expect(evidence).to_contain("gui_widget_renderdoc_goal_simple_gate_status=pass")
expect(evidence).to_contain("gui_widget_renderdoc_goal_simple_gate_fixture_path_status=pass")
expect(evidence).to_contain("gui_widget_renderdoc_goal_simple_gate_widget_html_bytes=")
expect(evidence).to_contain("gui_widget_renderdoc_goal_simple_gate_widget_html_bytes_status=fail")
expect(evidence).to_contain("gui_widget_renderdoc_goal_electron_gate_status=pass")
expect(evidence).to_contain("gui_widget_renderdoc_goal_blocked_gate_count=1")
expect(evidence).to_contain("gui_widget_renderdoc_goal_blocked_gates=Simple GUI widget RenderDoc .rdc on Vulkan Engine2D")
```

</details>

#### forwards missing Electron RDOC while preserving ARGB proof status

- Create controlled Electron evidence with ARGB proof but no RDOC capture
   - Expected: code equals `0`
- Assert parent evidence keeps the RDOC and ARGB states separate


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Create controlled Electron evidence with ARGB proof but no RDOC capture")
val command = "rm -rf build/test-gui-widget-renderdoc-goal-status-missing-rdc-with-argb && mkdir -p build/test-gui-widget-renderdoc-goal-status-missing-rdc-with-argb/simple build/test-gui-widget-renderdoc-goal-status-missing-rdc-with-argb/electron && printf 'RDOCsynthetic simple capture\\n' > build/test-gui-widget-renderdoc-goal-status-missing-rdc-with-argb/simple/simple.rdc && printf '{\"width\":2,\"height\":2,\"format\":\"argb-u32\",\"producer\":\"electron-chromium-capture\",\"nativeWidth\":2,\"nativeHeight\":2,\"pixels\":[4294967295,4278190335,4294967295,4294967295]}\\n' > build/test-gui-widget-renderdoc-goal-status-missing-rdc-with-argb/electron/electron_argb.json && printf '[1:1:ERROR:content/browser/gpu/gpu_process_host.cc:998] GPU process exited unexpectedly: exit_code=139\\n[1:1:ERROR:content/browser/gpu/gpu_process_host.cc:998] GPU process exited unexpectedly: exit_code=139\\n' > build/test-gui-widget-renderdoc-goal-status-missing-rdc-with-argb/electron/renderdoc-electron-html.log && printf 'rdoc_backend=simple\\nrdoc_scene=vulkan-engine2d\\nrdoc_program=src/app/test/renderdoc_vulkan_widget_capture.spl\\nrdoc_capture_status=pass\\nrdoc_capture_reason=pass\\nrdoc_capture_file=build/test-gui-widget-renderdoc-goal-status-missing-rdc-with-argb/simple/simple.rdc\\nrdoc_capture_magic=RDOC\\nrdoc_simple_runtime_backend=vulkan\\nrdoc_simple_renderdoc_available=1\\nrdoc_simple_renderdoc_start=1\\nrdoc_simple_renderdoc_end=1\\nrdoc_simple_renderdoc_num_captures=1\\nrdoc_simple_pixel_count=3072\\nrdoc_simple_widget_html_path=test/fixtures/html_css/generated_gui_vulkan_renderdoc_fixture.html\\nrdoc_simple_widget_html_bytes=4096\\n' > build/test-gui-widget-renderdoc-goal-status-missing-rdc-with-argb/simple/evidence.env && printf 'rdoc_backend=electron\\nrdoc_scene=html-css-electron\\nrdoc_capture_status=fail\\nrdoc_capture_reason=missing-rdc\\nrdoc_capture_file=\\nrdoc_capture_magic=\\nrdoc_html_path=test/fixtures/html_css/generated_gui_vulkan_renderdoc_fixture.html\\nrdoc_electron=tools/electron-shell/node_modules/electron/dist/Electron.app/Contents/MacOS/Electron\\nrdoc_electron_capture_script=tools/electron-live-bitmap/capture_html_argb.js\\nrdoc_electron_argb=build/test-gui-widget-renderdoc-goal-status-missing-rdc-with-argb/electron/electron_argb.json\\nrdoc_electron_width=2\\nrdoc_electron_height=2\\nrdoc_chromium_requested_api=vulkan\\nrdoc_chromium_requested_angle=vulkan\\nrdoc_chromium_requested_features=Vulkan\\nrdoc_chromium_launch_flags=--no-sandbox --disable-gpu-sandbox --no-zygote --ozone-platform=x11 --enable-features=Vulkan,DefaultANGLEVulkan,VulkanFromANGLE --ignore-gpu-blocklist --enable-gpu-rasterization --use-angle=vulkan\\nrdoc_log=build/test-gui-widget-renderdoc-goal-status-missing-rdc-with-argb/electron/renderdoc-electron-html.log\\n' > build/test-gui-widget-renderdoc-goal-status-missing-rdc-with-argb/electron/evidence.env && RDOC_SIMPLE_EVIDENCE_ENV=build/test-gui-widget-renderdoc-goal-status-missing-rdc-with-argb/simple/evidence.env RDOC_ELECTRON_HTML_EVIDENCE_ENV=build/test-gui-widget-renderdoc-goal-status-missing-rdc-with-argb/electron/evidence.env BUILD_DIR=build/test-gui-widget-renderdoc-goal-status-missing-rdc-with-argb/out REPORT_PATH=build/test-gui-widget-renderdoc-goal-status-missing-rdc-with-argb/report.md sh scripts/check/check-gui-widget-renderdoc-goal-status.shs"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

step("Assert parent evidence keeps the RDOC and ARGB states separate")
val evidence = file_read("build/test-gui-widget-renderdoc-goal-status-missing-rdc-with-argb/out/evidence.env")
expect(evidence).to_contain("gui_widget_renderdoc_goal_status=incomplete")
expect(evidence).to_contain("gui_widget_renderdoc_goal_reason=electron-widget-renderdoc-gpu-process-crashed-under-renderdoc")
expect(evidence).to_contain("gui_widget_renderdoc_goal_simple_gate_status=pass")
expect(evidence).to_contain("gui_widget_renderdoc_goal_electron_gate_status=fail")
expect(evidence).to_contain("gui_widget_renderdoc_goal_electron_gate_reason=chromium-gpu-process-crashed-under-renderdoc")
expect(evidence).to_contain("gui_widget_renderdoc_goal_electron_gate_failure_class=electron-gate-chromium-gpu-process-crashed-under-renderdoc")
expect(evidence).to_contain("gui_widget_renderdoc_goal_electron_gate_capture_file_status=missing")
expect(evidence).to_contain("gui_widget_renderdoc_goal_electron_gate_argb_file_status=pass")
expect(evidence).to_contain("gui_widget_renderdoc_goal_electron_gate_argb_status=pass")
expect(evidence).to_contain("gui_widget_renderdoc_goal_electron_gate_argb_nonblank_pixel_count=1")
expect(evidence).to_contain("gui_widget_renderdoc_goal_electron_gate_gpu_process_exit_status=fail")
expect(evidence).to_contain("gui_widget_renderdoc_goal_electron_gate_gpu_process_exit_count=2")
expect(evidence).to_contain("gui_widget_renderdoc_goal_electron_gate_gpu_process_exit_codes=139")
expect(evidence).to_contain("gui_widget_renderdoc_goal_electron_gate_gpu_process_exit_reason=gpu-process-exited-unexpectedly")
expect(evidence).to_contain("gui_widget_renderdoc_goal_blocked_gate_count=1")
expect(evidence).to_contain("gui_widget_renderdoc_goal_blocked_gates=Electron Chromium-on-Vulkan GPU process exits under RenderDoc before .rdc capture")
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

- **Design:** [doc/07_guide/tooling/renderdoc_capture_infra.md](doc/07_guide/tooling/renderdoc_capture_infra.md)


</details>
