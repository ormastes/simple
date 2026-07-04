# VSCode Rich Editor System Spec

> Verifies that the VS Code rich editor feature is backed by the real custom editor, webview, widget, and bundled output files rather than placeholder contract strings.

<!-- sdn-diagram:id=vscode_rich_editor_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=vscode_rich_editor_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

vscode_rich_editor_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=vscode_rich_editor_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# VSCode Rich Editor System Spec

Verifies that the VS Code rich editor feature is backed by the real custom editor, webview, widget, and bundled output files rather than placeholder contract strings.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/vscode_rich_editor/feature/vscode_rich_editor_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Verifies that the VS Code rich editor feature is backed by the real custom
editor, webview, widget, and bundled output files rather than placeholder
contract strings.

**Artifacts:** build/test-artifacts/03_system/app/vscode_rich_editor/feature/vscode_rich_editor/rich_editor_contract.txt

## Evidence

Display policy: `links`

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `rich_editor_contract.txt` | Text artifact | `build/test-artifacts/03_system/app/vscode_rich_editor/feature/vscode_rich_editor/rich_editor_contract.txt` |

## Scenarios

### VSCode rich editor feature

#### uses a real custom text editor provider backed by TextDocument

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_has(PROVIDER_TS, "implements vscode.CustomTextEditorProvider")).to_equal("present")
expect(_has(PROVIDER_TS, "public static readonly viewType = 'simple.richSourceEditor'")).to_equal("present")
expect(_has(PROVIDER_TS, "resolveCustomTextEditor")).to_equal("present")
expect(_has(PROVIDER_TS, "document.getText()")).to_equal("present")
expect(_has(PROVIDER_TS, "new vscode.WorkspaceEdit()")).to_equal("present")
expect(_has(PACKAGE_JSON, "\"viewType\": \"simple.richSourceEditor\"")).to_equal("present")
```

</details>

#### renders variable-height math and image widgets through CodeMirror

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_has(WEBVIEW_TS, "lineNumberWidgetMarker")).to_equal("present")
expect(_has(WEBVIEW_TS, "RichLineNumberWidgetMarker")).to_equal("present")
expect(_has(MATH_WIDGET_TS, "cm-math-widget-block")).to_equal("present")
expect(_has(IMAGE_WIDGET_TS, "maxHeight = 'none'")).to_equal("present")
expect(_has(DECORATION_TS, "new ImageWidget")).to_equal("present")
expect(_has(DECORATION_TS, "new MathWidget")).to_equal("present")
```

</details>

#### reveals raw source when the cursor enters a renderable block

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_has(DECORATION_TS, "const cursor = view.state.selection.main.head")).to_equal("present")
expect(_has(DECORATION_TS, "cursor >= block.from && cursor <= block.to")).to_equal("present")
expect(_has(DECORATION_TS, "continue")).to_equal("present")
```

</details>

#### keeps the backing document authoritative and bundled

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_has(PROVIDER_TS, "webviewPanel.webview.onDidReceiveMessage")).to_equal("present")
expect(_has(PROVIDER_TS, "message.type !== 'editAll'")).to_equal("present")
expect(_has(PROVIDER_TS, "edit.replace(document.uri")).to_equal("present")
expect(_has(BUNDLE_JS, "RichCustomEditorProvider.viewType = 'simple.richSourceEditor'")).to_equal("present")
expect(_has(BUNDLE_DTS, "implements vscode.CustomTextEditorProvider")).to_equal("present")
```

</details>

#### writes a generated-manual evidence summary

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val capture = "VSCode Rich Editor Evidence\n" +
    "provider: " + PROVIDER_TS + "\n" +
    "webview: " + WEBVIEW_TS + "\n" +
    "custom-editor: simple.richSourceEditor\n" +
    "widgets: math natural-height, image intrinsic-height\n" +
    "sync: TextDocument + WorkspaceEdit + editAll + selectionChanged"
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
