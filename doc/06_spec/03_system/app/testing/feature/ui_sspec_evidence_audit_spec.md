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

## Syntax

The spec reads source and generated manual files directly. It is an audit of the
SPipe evidence contract, not a replacement for the behavior specs it references.

## Scenarios

### UI SSPEC evidence audit

#### keeps UI-facing app specs mirrored into generated manuals

1. )) to equal

2. )) to equal

3. )) to equal

4. )) to equal

5. )) to equal

6. )) to equal

7. )) to equal

8. )) to equal

9. )) to equal

10. )) to equal

11. )) to equal

12. )) to equal

13. )) to equal

14. )) to equal


<details>
<summary>Executable SPipe</summary>

Runnable source: 56 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_manual_pair_state(
    "test/03_system/app/browser/feature/browser_session_ui_access_controls_spec.spl",
    "doc/06_spec/03_system/app/browser/feature/browser_session_ui_access_controls_spec.md"
)).to_equal("complete")
expect(_manual_pair_state(
    "test/03_system/app/browser/feature/webgpu_js_wasm_simple_spec.spl",
    "doc/06_spec/03_system/app/browser/feature/webgpu_js_wasm_simple_spec.md"
)).to_equal("complete")
expect(_manual_pair_state(
    "test/03_system/app/graphics_backend/feature/graphics_3d_session_managed_backend_spec.spl",
    "doc/06_spec/03_system/app/graphics_backend/feature/graphics_3d_session_managed_backend_spec.md"
)).to_equal("complete")
expect(_manual_pair_state(
    "test/03_system/app/ide/feature/ide_office_plugin_suite_spec.spl",
    "doc/06_spec/03_system/app/ide/feature/ide_office_plugin_suite_spec.md"
)).to_equal("complete")
expect(_manual_pair_state(
    "test/03_system/app/os/feature/ui_access_protocol_spec.spl",
    "doc/06_spec/03_system/app/os/feature/ui_access_protocol_spec.md"
)).to_equal("complete")
expect(_manual_pair_state(
    "test/03_system/app/testing/feature/test_runner_debug_tui_sgtti_spec.spl",
    "doc/06_spec/03_system/app/testing/feature/test_runner_debug_tui_sgtti_spec.md"
)).to_equal("complete")
expect(_manual_pair_state(
    "test/03_system/app/ui/feature/html_css_binary_caching_spec.spl",
    "doc/06_spec/03_system/app/ui/feature/html_css_binary_caching_spec.md"
)).to_equal("complete")
expect(_manual_pair_state(
    "test/03_system/app/ui/feature/shared_wm_renderer_unification_spec.spl",
    "doc/06_spec/03_system/app/ui/feature/shared_wm_renderer_unification_spec.md"
)).to_equal("complete")
expect(_manual_pair_state(
    "test/03_system/app/ui_test_api/feature/draw_ir_inspection_contract_spec.spl",
    "doc/06_spec/03_system/app/ui_test_api/feature/draw_ir_inspection_contract_spec.md"
)).to_equal("complete")
expect(_manual_pair_state(
    "test/03_system/app/ui_test_api/feature/draw_ir_protocol_evidence_spec.spl",
    "doc/06_spec/03_system/app/ui_test_api/feature/draw_ir_protocol_evidence_spec.md"
)).to_equal("complete")
expect(_manual_pair_state(
    "test/03_system/app/ui_test/feature/sgtti_shared_surface_contract_spec.spl",
    "doc/06_spec/03_system/app/ui_test/feature/sgtti_shared_surface_contract_spec.md"
)).to_equal("complete")
expect(_manual_pair_state(
    "test/03_system/app/vscode_extension/feature/vscode_math_editor_panel_spec.spl",
    "doc/06_spec/03_system/app/vscode_extension/feature/vscode_math_editor_panel_spec.md"
)).to_equal("complete")
expect(_manual_pair_state(
    "test/03_system/app/vscode_rich_editor/feature/vscode_rich_editor_spec.spl",
    "doc/06_spec/03_system/app/vscode_rich_editor/feature/vscode_rich_editor_spec.md"
)).to_equal("complete")
expect(_manual_pair_state(
    "test/03_system/app/wm_text_access_mcp/feature/wm_text_access_mcp_spec.spl",
    "doc/06_spec/03_system/app/wm_text_access_mcp/feature/wm_text_access_mcp_spec.md"
)).to_equal("complete")
```

</details>

#### keeps concrete UI evidence markers in the authoritative behavior specs

1. )) to equal

2. )) to equal

3. )) to equal

4. )) to equal

5. )) to equal

6. )) to equal

7. )) to equal

8. )) to equal


<details>
<summary>Executable SPipe</summary>

Runnable source: 32 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_marker_state(
    "test/03_system/app/browser/feature/browser_session_ui_access_controls_spec.spl",
    "ui_access_snapshot"
)).to_equal("present")
expect(_marker_state(
    "test/03_system/app/browser/feature/browser_session_ui_access_controls_spec.spl",
    "ui_access_act"
)).to_equal("present")
expect(_marker_state(
    "test/03_system/app/ui_test_api/feature/draw_ir_inspection_contract_spec.spl",
    "/api/test/draw-ir"
)).to_equal("present")
expect(_marker_state(
    "test/03_system/app/ui_test_api/feature/draw_ir_protocol_evidence_spec.spl",
    "draw_ir_protocol.json"
)).to_equal("present")
expect(_marker_state(
    "test/03_system/app/ui_test/feature/sgtti_shared_surface_contract_spec.spl",
    "SgttiTestDriver"
)).to_equal("present")
expect(_marker_state(
    "test/03_system/app/ide/feature/ide_office_plugin_suite_spec.spl",
    "# @evidence-display: embed_tui"
)).to_equal("present")
expect(_marker_state(
    "test/03_system/app/testing/feature/test_runner_debug_tui_sgtti_spec.spl",
    "**TUI Captures:**"
)).to_equal("present")
expect(_marker_state(
    "test/03_system/app/testing/feature/test_runner_debug_tui_sgtti_spec.spl",
    "SgttiTestDriver"
)).to_equal("present")
```

</details>

#### keeps generated UI manuals useful instead of stub-only

1. )) to equal

2. )) to equal

3. )) to equal

4. )) to equal

5. )) to equal

6. )) to equal

7. )) to equal

8. )) to equal

9. )) to equal

10. )) to equal

11. )) to equal


<details>
<summary>Executable SPipe</summary>

Runnable source: 44 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_marker_state(
    "doc/06_spec/03_system/app/testing/feature/test_runner_debug_tui_sgtti_spec.md",
    "### TUI Captures"
)).to_equal("present")
expect(_marker_state(
    "doc/06_spec/03_system/app/ide/feature/ide_office_plugin_suite_spec.md",
    "feature_check_tui.txt"
)).to_equal("present")
expect(_marker_state(
    "doc/06_spec/03_system/app/browser/feature/browser_session_ui_access_controls_spec.md",
    "ui_access_act"
)).to_equal("present")
expect(_marker_state(
    "doc/06_spec/03_system/app/browser/feature/browser_session_ui_access_controls_spec.md",
    "browser_ui_access_snapshot.txt"
)).to_equal("present")
expect(_marker_state(
    "doc/06_spec/03_system/app/ui_test_api/feature/draw_ir_inspection_contract_spec.md",
    "/api/test/draw-ir"
)).to_equal("present")
expect(_marker_state(
    "doc/06_spec/03_system/app/ui_test_api/feature/draw_ir_protocol_evidence_spec.md",
    "draw_ir_protocol.json"
)).to_equal("present")
expect(_marker_state(
    "doc/06_spec/03_system/app/ui_test/feature/sgtti_shared_surface_contract_spec.md",
    "SgttiTestDriver"
)).to_equal("present")
expect(_marker_state(
    "doc/06_spec/03_system/app/vscode_rich_editor/feature/vscode_rich_editor_spec.md",
    "rich_editor_contract.txt"
)).to_equal("present")
expect(_marker_state(
    "doc/06_spec/03_system/app/vscode_rich_editor/feature/vscode_rich_editor_spec.md",
    "implements vscode.CustomTextEditorProvider"
)).to_equal("present")
expect(_marker_state(
    "doc/06_spec/03_system/app/vscode_extension/feature/vscode_math_editor_panel_spec.md",
    "math_panel_contract.txt"
)).to_equal("present")
expect(_marker_state(
    "doc/06_spec/03_system/app/vscode_extension/feature/vscode_math_editor_panel_spec.md",
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
