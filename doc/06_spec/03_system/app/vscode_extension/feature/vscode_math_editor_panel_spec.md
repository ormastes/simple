# VSCode Math Editor Panel System Spec

> Verifies that the synchronized math editor panel is backed by the real VS Code extension source and bundled output: command registration, active-block state, selection mirroring, source edit delegation, and panel HTML controls.

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
| Updated | 2026-08-26 |
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

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- registers the sync panel command and hover entrypoint
   - Expected: _has(EXTENSION_TS, "simple.math.toggleSyncPanel") equals `present`
   - Expected: _has(EXTENSION_TS, "MathSyncPanel.show()") equals `present`
   - Expected: _has(PACKAGE_JSON, "\"command\": \"simple.math.toggleSyncPanel\"") equals `present`
   - Expected: _has(NATIVE_PROVIDER_TS, "Open Synced Math Panel") equals `present`
   - Expected: _has(NATIVE_PROVIDER_TS, "contentRange") equals `present`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("registers the sync panel command and hover entrypoint")
expect(_has(EXTENSION_TS, "simple.math.toggleSyncPanel")).to_equal("present")
expect(_has(EXTENSION_TS, "MathSyncPanel.show()")).to_equal("present")
expect(_has(PACKAGE_JSON, "\"command\": \"simple.math.toggleSyncPanel\"")).to_equal("present")
expect(_has(NATIVE_PROVIDER_TS, "Open Synced Math Panel")).to_equal("present")
expect(_has(NATIVE_PROVIDER_TS, "contentRange")).to_equal("present")
```

</details>

#### builds active and empty panel states from the canonical source document

- builds active and empty panel states from the canonical source document
   - Expected: _has(PANEL_SHARED_TS, "buildMathSyncPanelState") equals `present`
   - Expected: _has(PANEL_SHARED_TS, "findMathBlockAtOffset") equals `present`
   - Expected: _has(PANEL_SHARED_TS, "activeBlock: null") equals `present`
   - Expected: _has(PANEL_SHARED_TS, "activeSelectionStart") equals `present`
   - Expected: _has(PANEL_SHARED_TS, "contentRange") equals `present`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("builds active and empty panel states from the canonical source document")
expect(_has(PANEL_SHARED_TS, "buildMathSyncPanelState")).to_equal("present")
expect(_has(PANEL_SHARED_TS, "findMathBlockAtOffset")).to_equal("present")
expect(_has(PANEL_SHARED_TS, "activeBlock: null")).to_equal("present")
expect(_has(PANEL_SHARED_TS, "activeSelectionStart")).to_equal("present")
expect(_has(PANEL_SHARED_TS, "contentRange")).to_equal("present")
```

</details>

#### renders panel shell controls and mirrors textarea selection

- renders panel shell controls and mirrors textarea selection
   - Expected: _has(PANEL_HTML_TS, "textarea id=\"math-source\"") equals `present`
   - Expected: _has(PANEL_HTML_TS, "source.selectionStart") equals `present`
   - Expected: _has(PANEL_HTML_TS, "source.selectionEnd") equals `present`
   - Expected: _has(PANEL_HTML_TS, "type: 'selectionChanged'") equals `present`
   - Expected: _has(PANEL_HTML_TS, "type: 'editAll'") equals `present`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("renders panel shell controls and mirrors textarea selection")
expect(_has(PANEL_HTML_TS, "textarea id=\"math-source\"")).to_equal("present")
expect(_has(PANEL_HTML_TS, "source.selectionStart")).to_equal("present")
expect(_has(PANEL_HTML_TS, "source.selectionEnd")).to_equal("present")
expect(_has(PANEL_HTML_TS, "type: 'selectionChanged'")).to_equal("present")
expect(_has(PANEL_HTML_TS, "type: 'editAll'")).to_equal("present")
```

</details>

#### delegates edits through WorkspaceEdit and ships bundled output

- delegates edits through WorkspaceEdit and ships bundled output
   - Expected: _has(SYNC_PANEL_TS, "message.type !== 'editAll'") equals `present`
   - Expected: _has(SYNC_PANEL_TS, "new vscode.WorkspaceEdit()") equals `present`
   - Expected: _has(SYNC_PANEL_TS, "edit.replace(editor.document.uri") equals `present`
   - Expected: _has(BUNDLE_SYNC_JS, "new vscode.WorkspaceEdit()") equals `present`
   - Expected: _has(BUNDLE_HTML_JS, "selectionChanged") equals `present`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("delegates edits through WorkspaceEdit and ships bundled output")
expect(_has(SYNC_PANEL_TS, "message.type !== 'editAll'")).to_equal("present")
expect(_has(SYNC_PANEL_TS, "new vscode.WorkspaceEdit()")).to_equal("present")
expect(_has(SYNC_PANEL_TS, "edit.replace(editor.document.uri")).to_equal("present")
expect(_has(BUNDLE_SYNC_JS, "new vscode.WorkspaceEdit()")).to_equal("present")
expect(_has(BUNDLE_HTML_JS, "selectionChanged")).to_equal("present")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `b6d0c1d6eaf461065075c565be38c9cd16029e98a1301c83d19e365cb47d766b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b6d0c1d6eaf461065075c565be38c9cd16029e98a1301c83d19e365cb47d766b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b6d0c1d6eaf461065075c565be38c9cd16029e98a1301c83d19e365cb47d766b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/03_system/app/vscode_extension/feature/vscode_math_editor_panel_spec.spl
mirror: doc/06_spec/03_system/app/vscode_extension/feature/vscode_math_editor_panel_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/app/vscode_extension/feature/vscode_math_editor_panel_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/vscode_extension/feature/vscode_math_editor_panel_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/vscode_extension/feature/vscode_math_editor_panel_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/app/vscode_extension/feature/vscode_math_editor_panel_spec.spl:59:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'registers the sync panel command and hover entrypoint' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/vscode_extension/feature/vscode_math_editor_panel_spec.spl:68:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'builds active and empty panel states from the canonical source document' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/vscode_extension/feature/vscode_math_editor_panel_spec.spl:77:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'renders panel shell controls and mirrors textarea selection' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
