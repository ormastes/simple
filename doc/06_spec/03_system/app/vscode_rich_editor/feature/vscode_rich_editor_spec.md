# VSCode Rich Editor System Spec

> Verifies that the VS Code rich editor feature is backed by the real custom editor, webview, widget, and bundled output files rather than placeholder contract strings.

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
| Updated | 2026-08-26 |
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

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- uses a real custom text editor provider backed by TextDocument
   - Expected: _has(PROVIDER_TS, "implements vscode.CustomTextEditorProvider") equals `present`
   - Expected: _has(PROVIDER_TS, "public static readonly viewType = 'simple.richSourceEditor'") equals `present`
   - Expected: _has(PROVIDER_TS, "resolveCustomTextEditor") equals `present`
   - Expected: _has(PROVIDER_TS, "document.getText()") equals `present`
   - Expected: _has(PROVIDER_TS, "new vscode.WorkspaceEdit()") equals `present`
   - Expected: _has(PACKAGE_JSON, "\"viewType\": \"simple.richSourceEditor\"") equals `present`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("uses a real custom text editor provider backed by TextDocument")
expect(_has(PROVIDER_TS, "implements vscode.CustomTextEditorProvider")).to_equal("present")
expect(_has(PROVIDER_TS, "public static readonly viewType = 'simple.richSourceEditor'")).to_equal("present")
expect(_has(PROVIDER_TS, "resolveCustomTextEditor")).to_equal("present")
expect(_has(PROVIDER_TS, "document.getText()")).to_equal("present")
expect(_has(PROVIDER_TS, "new vscode.WorkspaceEdit()")).to_equal("present")
expect(_has(PACKAGE_JSON, "\"viewType\": \"simple.richSourceEditor\"")).to_equal("present")
```

</details>

#### renders variable-height math and image widgets through CodeMirror

- renders variable-height math and image widgets through CodeMirror
   - Expected: _has(WEBVIEW_TS, "lineNumberWidgetMarker") equals `present`
   - Expected: _has(WEBVIEW_TS, "RichLineNumberWidgetMarker") equals `present`
   - Expected: _has(MATH_WIDGET_TS, "cm-math-widget-block") equals `present`
   - Expected: _has(IMAGE_WIDGET_TS, "maxHeight = 'none'") equals `present`
   - Expected: _has(DECORATION_TS, "new ImageWidget") equals `present`
   - Expected: _has(DECORATION_TS, "new MathWidget") equals `present`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("renders variable-height math and image widgets through CodeMirror")
expect(_has(WEBVIEW_TS, "lineNumberWidgetMarker")).to_equal("present")
expect(_has(WEBVIEW_TS, "RichLineNumberWidgetMarker")).to_equal("present")
expect(_has(MATH_WIDGET_TS, "cm-math-widget-block")).to_equal("present")
expect(_has(IMAGE_WIDGET_TS, "maxHeight = 'none'")).to_equal("present")
expect(_has(DECORATION_TS, "new ImageWidget")).to_equal("present")
expect(_has(DECORATION_TS, "new MathWidget")).to_equal("present")
```

</details>

#### reveals raw source when the cursor enters a renderable block

- reveals raw source when the cursor enters a renderable block
   - Expected: _has(DECORATION_TS, "const cursor = view.state.selection.main.head") equals `present`
   - Expected: _has(DECORATION_TS, "cursor >= block.from && cursor <= block.to") equals `present`
   - Expected: _has(DECORATION_TS, "continue") equals `present`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("reveals raw source when the cursor enters a renderable block")
expect(_has(DECORATION_TS, "const cursor = view.state.selection.main.head")).to_equal("present")
expect(_has(DECORATION_TS, "cursor >= block.from && cursor <= block.to")).to_equal("present")
expect(_has(DECORATION_TS, "continue")).to_equal("present")
```

</details>

#### keeps the backing document authoritative and bundled

- keeps the backing document authoritative and bundled
   - Expected: _has(PROVIDER_TS, "webviewPanel.webview.onDidReceiveMessage") equals `present`
   - Expected: _has(PROVIDER_TS, "message.type !== 'editAll'") equals `present`
   - Expected: _has(PROVIDER_TS, "edit.replace(document.uri") equals `present`
   - Expected: _has(BUNDLE_JS, "RichCustomEditorProvider.viewType = 'simple.richSourceEditor'") equals `present`
   - Expected: _has(BUNDLE_DTS, "implements vscode.CustomTextEditorProvider") equals `present`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("keeps the backing document authoritative and bundled")
expect(_has(PROVIDER_TS, "webviewPanel.webview.onDidReceiveMessage")).to_equal("present")
expect(_has(PROVIDER_TS, "message.type !== 'editAll'")).to_equal("present")
expect(_has(PROVIDER_TS, "edit.replace(document.uri")).to_equal("present")
expect(_has(BUNDLE_JS, "RichCustomEditorProvider.viewType = 'simple.richSourceEditor'")).to_equal("present")
expect(_has(BUNDLE_DTS, "implements vscode.CustomTextEditorProvider")).to_equal("present")
```

</details>

#### writes a generated-manual evidence summary

- writes a generated-manual evidence summary
   - Expected: _write_capture(capture) equals `0`
   - Expected: _capture_state(capture) equals `matched`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("writes a generated-manual evidence summary")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `083e8b9ccc0b9b87751a26d7cc618e09ed22d6fd011acd44f8616a91660b1ec6`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `083e8b9ccc0b9b87751a26d7cc618e09ed22d6fd011acd44f8616a91660b1ec6`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `083e8b9ccc0b9b87751a26d7cc618e09ed22d6fd011acd44f8616a91660b1ec6`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/03_system/app/vscode_rich_editor/feature/vscode_rich_editor_spec.spl
mirror: doc/06_spec/03_system/app/vscode_rich_editor/feature/vscode_rich_editor_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/app/vscode_rich_editor/feature/vscode_rich_editor_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/vscode_rich_editor/feature/vscode_rich_editor_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/vscode_rich_editor/feature/vscode_rich_editor_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/app/vscode_rich_editor/feature/vscode_rich_editor_spec.spl:59:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'uses a real custom text editor provider backed by TextDocument' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/vscode_rich_editor/feature/vscode_rich_editor_spec.spl:69:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'renders variable-height math and image widgets through CodeMirror' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/vscode_rich_editor/feature/vscode_rich_editor_spec.spl:79:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reveals raw source when the cursor enters a renderable block' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
