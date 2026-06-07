# VSCode Math Editor Panel System Spec

> Verifies that the synchronized math editor panel is backed by the real VS Code extension source and bundled output: command registration, active-block state, selection mirroring, source edit delegation, and panel HTML controls.

<!-- sdn-diagram:id=vscode_math_editor_panel_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=vscode_math_editor_panel_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

vscode_math_editor_panel_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=vscode_math_editor_panel_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# VSCode Math Editor Panel System Spec

Verifies that the synchronized math editor panel is backed by the real VS Code extension source and bundled output: command registration, active-block state, selection mirroring, source edit delegation, and panel HTML controls.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/vscode_extension/feature/vscode_math_editor_panel_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Verifies that the synchronized math editor panel is backed by the real VS Code
extension source and bundled output: command registration, active-block state,
selection mirroring, source edit delegation, and panel HTML controls.

**Artifacts:** build/test-artifacts/03_system/app/vscode_extension/feature/vscode_math_editor_panel/math_panel_contract.txt

## Evidence

Display policy: `links`

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `math_panel_contract.txt` | Text artifact | `build/test-artifacts/03_system/app/vscode_extension/feature/vscode_math_editor_panel/math_panel_contract.txt` |

## Scenarios

### VSCode math editor panel feature

#### registers the sync panel command and hover entrypoint

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_has(EXTENSION_TS, "simple.math.toggleSyncPanel")).to_equal("present")
expect(_has(EXTENSION_TS, "MathSyncPanel.show()")).to_equal("present")
expect(_has(PACKAGE_JSON, "\"command\": \"simple.math.toggleSyncPanel\"")).to_equal("present")
expect(_has(NATIVE_PROVIDER_TS, "Open Synced Math Panel")).to_equal("present")
expect(_has(NATIVE_PROVIDER_TS, "contentRange")).to_equal("present")
```

</details>

#### builds active and empty panel states from the canonical source document

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_has(PANEL_SHARED_TS, "buildMathSyncPanelState")).to_equal("present")
expect(_has(PANEL_SHARED_TS, "findMathBlockAtOffset")).to_equal("present")
expect(_has(PANEL_SHARED_TS, "activeBlock: null")).to_equal("present")
expect(_has(PANEL_SHARED_TS, "activeSelectionStart")).to_equal("present")
expect(_has(PANEL_SHARED_TS, "contentRange")).to_equal("present")
```

</details>

#### renders panel shell controls and mirrors textarea selection

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_has(PANEL_HTML_TS, "textarea id=\"math-source\"")).to_equal("present")
expect(_has(PANEL_HTML_TS, "source.selectionStart")).to_equal("present")
expect(_has(PANEL_HTML_TS, "source.selectionEnd")).to_equal("present")
expect(_has(PANEL_HTML_TS, "type: 'selectionChanged'")).to_equal("present")
expect(_has(PANEL_HTML_TS, "type: 'editAll'")).to_equal("present")
```

</details>

#### delegates edits through WorkspaceEdit and ships bundled output

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_has(SYNC_PANEL_TS, "message.type !== 'editAll'")).to_equal("present")
expect(_has(SYNC_PANEL_TS, "new vscode.WorkspaceEdit()")).to_equal("present")
expect(_has(SYNC_PANEL_TS, "edit.replace(editor.document.uri")).to_equal("present")
expect(_has(BUNDLE_SYNC_JS, "new vscode.WorkspaceEdit()")).to_equal("present")
expect(_has(BUNDLE_HTML_JS, "selectionChanged")).to_equal("present")
```

</details>

#### writes a generated-manual evidence summary

<details>
<summary>Executable SPipe</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val capture = "VSCode Math Panel Evidence\n" +
    "command: simple.math.toggleSyncPanel\n" +
    "state: buildMathSyncPanelState + activeBlock\n" +
    "selection: selectionStart/selectionEnd mirrored through textarea\n" +
    "edit: editAll -> WorkspaceEdit\n" +
    "hover: NativeMathProvider opens synced panel"
expect(_write_capture(capture)).to_equal(0)
expect(_capture_state(capture)).to_equal("matched")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
