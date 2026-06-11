# UI SSPEC Evidence Audit

> Audits the UI-facing SPipe system-test lane so critical app UI specs keep executable SSPEC coverage, mirrored generated manuals, and concrete visible state evidence markers.

<!-- sdn-diagram:id=ui_sspec_evidence_audit_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=ui_sspec_evidence_audit_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

ui_sspec_evidence_audit_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=ui_sspec_evidence_audit_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# UI SSPEC Evidence Audit

Audits the UI-facing SPipe system-test lane so critical app UI specs keep executable SSPEC coverage, mirrored generated manuals, and concrete visible state evidence markers.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Requirements | doc/03_plan/sys_test/ui_sspec_evidence_audit.md |
| Plan | doc/03_plan/sys_test/ui_sspec_evidence_audit.md |
| Design | doc/05_design/app/testing/ui_sspec_evidence_audit.md |
| Research | N/A |
| Source | `test/03_system/app/testing/feature/ui_sspec_evidence_audit_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Audits the UI-facing SPipe system-test lane so critical app UI specs keep
executable SSPEC coverage, mirrored generated manuals, and concrete visible
state evidence markers.

**Requirements:** doc/03_plan/sys_test/ui_sspec_evidence_audit.md
**Plan:** doc/03_plan/sys_test/ui_sspec_evidence_audit.md
**Design:** doc/05_design/app/testing/ui_sspec_evidence_audit.md
**Research:** N/A
**TUI Captures:** build/test-artifacts/03_system/app/testing/feature/ui_sspec_evidence_audit/ui_evidence_audit.txt

## Syntax

The spec reads source and generated manual files directly. It is an audit of the
SPipe evidence contract, not a replacement for the behavior specs it references.

## Evidence

Display policy: `embed_tui`

| Category | Count |
|----------|------:|
| TUI Captures | 1 |

### TUI Captures

| Item | Kind | Path |
|------|------|------|
| `ui_evidence_audit.txt` | TUI capture | `build/test-artifacts/03_system/app/testing/feature/ui_sspec_evidence_audit/ui_evidence_audit.txt` |

#### Embedded TUI Text Captures

<details>
<summary>ui_evidence_audit.txt</summary>

```text
UI SSPEC Evidence Audit
manuals: mirrored
step-manual: enabled
tui-captures: embedded
```

</details>

## Scenarios

### UI SSPEC evidence audit

#### keeps UI-facing app specs mirrored into generated manuals

1. Confirm the browser session UI access controls manual mirrors its executable SSpec
2. Confirm the WebGPU JavaScript/WASM Simple manual mirrors its executable SSpec
3. Confirm the graphics 3D managed backend manual mirrors its executable SSpec
4. Confirm the IDE office plugin suite manual mirrors its executable SSpec
5. Confirm the OS UI access protocol manual mirrors its executable SSpec
6. Confirm the test runner debug TUI SGTTI manual mirrors its executable SSpec
7. Confirm the HTML/CSS binary caching manual mirrors its executable SSpec
8. Confirm the shared WM renderer manual mirrors its executable SSpec
9. Confirm the Draw IR inspection manual mirrors its executable SSpec
10. Confirm the Draw IR protocol evidence manual mirrors its executable SSpec
11. Confirm the SGTTI shared surface manual mirrors its executable SSpec
12. Confirm the VS Code math editor panel manual mirrors its executable SSpec
13. Confirm the VS Code rich editor manual mirrors its executable SSpec
14. Confirm the WM text access MCP manual mirrors its executable SSpec


<details>
<summary>Executable SSpec</summary>

Runnable source: 70 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Confirm the browser session UI access controls manual mirrors its executable SSpec")
expect(_manual_pair_state(
    "test/03_system/app/browser/feature/browser_session_ui_access_controls_spec.spl",
    "doc/06_spec/test/03_system/app/browser/feature/browser_session_ui_access_controls_spec.md"
)).to_equal("complete")
step("Confirm the WebGPU JavaScript/WASM Simple manual mirrors its executable SSpec")
expect(_manual_pair_state(
    "test/03_system/app/browser/feature/webgpu_js_wasm_simple_spec.spl",
    "doc/06_spec/test/03_system/app/browser/feature/webgpu_js_wasm_simple_spec.md"
)).to_equal("complete")
step("Confirm the graphics 3D managed backend manual mirrors its executable SSpec")
expect(_manual_pair_state(
    "test/03_system/app/graphics_backend/feature/graphics_3d_session_managed_backend_spec.spl",
    "doc/06_spec/test/03_system/app/graphics_backend/feature/graphics_3d_session_managed_backend_spec.md"
)).to_equal("complete")
step("Confirm the IDE office plugin suite manual mirrors its executable SSpec")
expect(_manual_pair_state(
    "test/03_system/app/ide/feature/ide_office_plugin_suite_spec.spl",
    "doc/06_spec/test/03_system/app/ide/feature/ide_office_plugin_suite_spec.md"
)).to_equal("complete")
step("Confirm the OS UI access protocol manual mirrors its executable SSpec")
expect(_manual_pair_state(
    "test/03_system/app/os/feature/ui_access_protocol_spec.spl",
    "doc/06_spec/test/03_system/app/os/feature/ui_access_protocol_spec.md"
)).to_equal("complete")
step("Confirm the test runner debug TUI SGTTI manual mirrors its executable SSpec")
expect(_manual_pair_state(
    "test/03_system/app/testing/feature/test_runner_debug_tui_sgtti_spec.spl",
    "doc/06_spec/test/03_system/app/testing/feature/test_runner_debug_tui_sgtti_spec.md"
)).to_equal("complete")
step("Confirm the HTML/CSS binary caching manual mirrors its executable SSpec")
expect(_manual_pair_state(
    "test/03_system/app/ui/feature/html_css_binary_caching_spec.spl",
    "doc/06_spec/test/03_system/app/ui/feature/html_css_binary_caching_spec.md"
)).to_equal("complete")
step("Confirm the shared WM renderer manual mirrors its executable SSpec")
expect(_manual_pair_state(
    "test/03_system/app/ui/feature/shared_wm_renderer_unification_spec.spl",
    "doc/06_spec/test/03_system/app/ui/feature/shared_wm_renderer_unification_spec.md"
)).to_equal("complete")
step("Confirm the Draw IR inspection manual mirrors its executable SSpec")
expect(_manual_pair_state(
    "test/03_system/app/ui_test_api/feature/draw_ir_inspection_contract_spec.spl",
    "doc/06_spec/test/03_system/app/ui_test_api/feature/draw_ir_inspection_contract_spec.md"
)).to_equal("complete")
step("Confirm the Draw IR protocol evidence manual mirrors its executable SSpec")
expect(_manual_pair_state(
    "test/03_system/app/ui_test_api/feature/draw_ir_protocol_evidence_spec.spl",
    "doc/06_spec/test/03_system/app/ui_test_api/feature/draw_ir_protocol_evidence_spec.md"
)).to_equal("complete")
step("Confirm the SGTTI shared surface manual mirrors its executable SSpec")
expect(_manual_pair_state(
    "test/03_system/app/ui_test/feature/sgtti_shared_surface_contract_spec.spl",
    "doc/06_spec/test/03_system/app/ui_test/feature/sgtti_shared_surface_contract_spec.md"
)).to_equal("complete")
step("Confirm the VS Code math editor panel manual mirrors its executable SSpec")
expect(_manual_pair_state(
    "test/03_system/app/vscode_extension/feature/vscode_math_editor_panel_spec.spl",
    "doc/06_spec/test/03_system/app/vscode_extension/feature/vscode_math_editor_panel_spec.md"
)).to_equal("complete")
step("Confirm the VS Code rich editor manual mirrors its executable SSpec")
expect(_manual_pair_state(
    "test/03_system/app/vscode_rich_editor/feature/vscode_rich_editor_spec.spl",
    "doc/06_spec/test/03_system/app/vscode_rich_editor/feature/vscode_rich_editor_spec.md"
)).to_equal("complete")
step("Confirm the WM text access MCP manual mirrors its executable SSpec")
expect(_manual_pair_state(
    "test/03_system/app/wm_text_access_mcp/feature/wm_text_access_mcp_spec.spl",
    "doc/06_spec/test/03_system/app/wm_text_access_mcp/feature/wm_text_access_mcp_spec.md"
)).to_equal("complete")
```

</details>

#### keeps concrete UI evidence markers in the authoritative behavior specs

1. Check browser UI access snapshots are captured in the behavior spec
2. Check browser UI actions are captured in the behavior spec
3. Check Draw IR inspection keeps its API evidence marker
4. Check Draw IR protocol keeps its JSON evidence marker
5. Check SGTTI specs keep their shared test driver marker
6. Check IDE office plugin suite embeds TUI evidence
7. Check the test runner debug TUI spec declares TUI captures
8. Check the test runner debug TUI spec uses the SGTTI driver


<details>
<summary>Executable SSpec</summary>

Runnable source: 40 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Check browser UI access snapshots are captured in the behavior spec")
expect(_marker_state(
    "test/03_system/app/browser/feature/browser_session_ui_access_controls_spec.spl",
    "ui_access_snapshot"
)).to_equal("present")
step("Check browser UI actions are captured in the behavior spec")
expect(_marker_state(
    "test/03_system/app/browser/feature/browser_session_ui_access_controls_spec.spl",
    "ui_access_act"
)).to_equal("present")
step("Check Draw IR inspection keeps its API evidence marker")
expect(_marker_state(
    "test/03_system/app/ui_test_api/feature/draw_ir_inspection_contract_spec.spl",
    "/api/test/draw-ir"
)).to_equal("present")
step("Check Draw IR protocol keeps its JSON evidence marker")
expect(_marker_state(
    "test/03_system/app/ui_test_api/feature/draw_ir_protocol_evidence_spec.spl",
    "draw_ir_protocol.json"
)).to_equal("present")
step("Check SGTTI specs keep their shared test driver marker")
expect(_marker_state(
    "test/03_system/app/ui_test/feature/sgtti_shared_surface_contract_spec.spl",
    "SgttiTestDriver"
)).to_equal("present")
step("Check IDE office plugin suite embeds TUI evidence")
expect(_marker_state(
    "test/03_system/app/ide/feature/ide_office_plugin_suite_spec.spl",
    "# @evidence-display: embed_tui"
)).to_equal("present")
step("Check the test runner debug TUI spec declares TUI captures")
expect(_marker_state(
    "test/03_system/app/testing/feature/test_runner_debug_tui_sgtti_spec.spl",
    "**TUI Captures:**"
)).to_equal("present")
step("Check the test runner debug TUI spec uses the SGTTI driver")
expect(_marker_state(
    "test/03_system/app/testing/feature/test_runner_debug_tui_sgtti_spec.spl",
    "SgttiTestDriver"
)).to_equal("present")
```

</details>

#### keeps generated UI manuals useful instead of stub-only

1. Write a TUI capture for the UI evidence audit manual
   - Expected: _write_audit_capture() equals `0`
2. Check the audit TUI capture was written with manual evidence state
   - Expected: _capture_state("step-manual: enabled") equals `present`
3. Check the generated audit manual exposes embedded TUI captures
4. Check the generated audit manual includes readable operator steps
5. Check the test runner debug TUI manual exposes embedded TUI captures
6. Check the IDE office plugin suite manual links the feature-check TUI capture
7. Check browser UI access manual keeps action evidence text
8. Check browser UI access manual links the snapshot capture
9. Check Draw IR inspection manual keeps endpoint evidence text
10. Check Draw IR protocol manual links the JSON evidence file
11. Check SGTTI shared surface manual names the test driver
12. Check VS Code rich editor manual links the contract capture
13. Check VS Code rich editor manual keeps provider implementation evidence
14. Check VS Code math editor panel manual links the contract capture
15. Check VS Code math editor panel manual keeps panel-state evidence


<details>
<summary>Executable SSpec</summary>

Runnable source: 69 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Write a TUI capture for the UI evidence audit manual")
expect(_write_audit_capture()).to_equal(0)
step("Check the audit TUI capture was written with manual evidence state")
expect(_capture_state("step-manual: enabled")).to_equal("present")
step("Check the generated audit manual exposes embedded TUI captures")
expect(_marker_state(
    "doc/06_spec/test/03_system/app/testing/feature/ui_sspec_evidence_audit_spec.md",
    "### TUI Captures"
)).to_equal("present")
step("Check the generated audit manual includes readable operator steps")
expect(_marker_state(
    "doc/06_spec/test/03_system/app/testing/feature/ui_sspec_evidence_audit_spec.md",
    "Confirm the browser session UI access controls manual mirrors its executable SSpec"
)).to_equal("present")
step("Check the test runner debug TUI manual exposes embedded TUI captures")
expect(_marker_state(
    "doc/06_spec/test/03_system/app/testing/feature/test_runner_debug_tui_sgtti_spec.md",
    "### TUI Captures"
)).to_equal("present")
step("Check the IDE office plugin suite manual links the feature-check TUI capture")
expect(_marker_state(
    "doc/06_spec/test/03_system/app/ide/feature/ide_office_plugin_suite_spec.md",
    "feature_check_tui.txt"
)).to_equal("present")
step("Check browser UI access manual keeps action evidence text")
expect(_marker_state(
    "doc/06_spec/test/03_system/app/browser/feature/browser_session_ui_access_controls_spec.md",
    "ui_access_act"
)).to_equal("present")
step("Check browser UI access manual links the snapshot capture")
expect(_marker_state(
    "doc/06_spec/test/03_system/app/browser/feature/browser_session_ui_access_controls_spec.md",
    "browser_ui_access_snapshot.txt"
)).to_equal("present")
step("Check Draw IR inspection manual keeps endpoint evidence text")
expect(_marker_state(
    "doc/06_spec/test/03_system/app/ui_test_api/feature/draw_ir_inspection_contract_spec.md",
    "/api/test/draw-ir"
)).to_equal("present")
step("Check Draw IR protocol manual links the JSON evidence file")
expect(_marker_state(
    "doc/06_spec/test/03_system/app/ui_test_api/feature/draw_ir_protocol_evidence_spec.md",
    "draw_ir_protocol.json"
)).to_equal("present")
step("Check SGTTI shared surface manual names the test driver")
expect(_marker_state(
    "doc/06_spec/test/03_system/app/ui_test/feature/sgtti_shared_surface_contract_spec.md",
    "SgttiTestDriver"
)).to_equal("present")
step("Check VS Code rich editor manual links the contract capture")
expect(_marker_state(
    "doc/06_spec/test/03_system/app/vscode_rich_editor/feature/vscode_rich_editor_spec.md",
    "rich_editor_contract.txt"
)).to_equal("present")
step("Check VS Code rich editor manual keeps provider implementation evidence")
expect(_marker_state(
    "doc/06_spec/test/03_system/app/vscode_rich_editor/feature/vscode_rich_editor_spec.md",
    "implements vscode.CustomTextEditorProvider"
)).to_equal("present")
step("Check VS Code math editor panel manual links the contract capture")
expect(_marker_state(
    "doc/06_spec/test/03_system/app/vscode_extension/feature/vscode_math_editor_panel_spec.md",
    "math_panel_contract.txt"
)).to_equal("present")
step("Check VS Code math editor panel manual keeps panel-state evidence")
expect(_marker_state(
    "doc/06_spec/test/03_system/app/vscode_extension/feature/vscode_math_editor_panel_spec.md",
    "buildMathSyncPanelState"
)).to_equal("present")
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

- **Requirements:** [doc/03_plan/sys_test/ui_sspec_evidence_audit.md](doc/03_plan/sys_test/ui_sspec_evidence_audit.md)
- **Plan:** [doc/03_plan/sys_test/ui_sspec_evidence_audit.md](doc/03_plan/sys_test/ui_sspec_evidence_audit.md)
- **Design:** [doc/05_design/app/testing/ui_sspec_evidence_audit.md](doc/05_design/app/testing/ui_sspec_evidence_audit.md)


</details>
