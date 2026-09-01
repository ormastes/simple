# Host Simpleos Surface Contract Specification

> Tests covering editor host and SimpleOS surface contract.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Host Simpleos Surface Contract Specification

## Scenarios

### editor host and SimpleOS surface contract

#### keeps shared editor services runtime neutral

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- keeps shared editor services runtime neutral


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps shared editor services runtime neutral")
assert_no_host_tokens("src/lib/editor/buffer/buffer.spl")
assert_no_host_tokens("src/lib/editor/core/launch.spl")
assert_no_host_tokens("src/lib/editor/core/path_text.spl")
assert_no_host_tokens("src/lib/editor/core/session.spl")
assert_no_host_tokens("src/lib/editor/view/layout.spl")
assert_no_host_tokens("src/lib/editor/70.backend/gui_backend.spl")
assert_no_host_tokens("src/lib/editor/services/command_palette.spl")
assert_no_host_tokens("src/lib/editor/extensions/host.spl")
```

</details>

#### keeps IDE launch entrypoints host and SimpleOS runnable

- keeps IDE launch entrypoints host and SimpleOS runnable


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps IDE launch entrypoints host and SimpleOS runnable")
assert_no_host_tokens("src/app/ide/main.spl")
assert_no_host_tokens("examples/10_tooling/ide/simple_ide_launch.spl")
assert_no_host_tokens("examples/10_tooling/ide/simple_ide_render.spl")
assert_no_host_tokens("examples/10_tooling/ide/extensions/markdown-notes/main.spl")
```

</details>

#### keeps the TUI path SimpleOS-safe

- keeps the TUI path SimpleOS-safe


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps the TUI path SimpleOS-safe")
assert_no_host_tokens("src/app/editor/tui_main.spl")
assert_no_host_tokens("src/app/editor/tui_shell.spl")
assert_no_host_tokens("src/app/editor/tui_shell_panels.spl")
assert_no_host_tokens("src/lib/editor/70.backend/tui_backend.spl")
```

</details>

#### documents host adapters outside the SimpleOS-safe path

- documents host adapters outside the SimpleOS-safe path
   - Expected: guide contains `Host and SimpleOS Runtime Contract`
   - Expected: guide contains `src/app/editor/gui_shell_*`
   - Expected: guide contains `src/app/ui.tauri/`
   - Expected: guide contains `src/app/ui.browser/`
   - Expected: guide contains `src/app/ui.web/`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("documents host adapters outside the SimpleOS-safe path")
val guide = read_text("doc/07_guide/app/editor_tui.md")
expect(guide.contains("Host and SimpleOS Runtime Contract")).to_equal(true)
expect(guide.contains("src/app/editor/gui_shell_*")).to_equal(true)
expect(guide.contains("src/app/ui.tauri/")).to_equal(true)
expect(guide.contains("src/app/ui.browser/")).to_equal(true)
expect(guide.contains("src/app/ui.web/")).to_equal(true)
```

</details>

#### keeps legacy VS Code docs pointed at current shared IDE surfaces

- keeps legacy VS Code docs pointed at current shared IDE surfaces
   - Expected: arch does not contain `../../src/app/vscode_rich_editor`
   - Expected: design does not contain `src/app/vscode_rich_editor`
   - Expected: tui does not contain `30.view/`
   - Expected: arch contains `Legacy VS Code Rich Editor Architecture`
   - Expected: design contains `Markdown-first`
   - Expected: tui contains `examples/ide/**` contains sample integrations only`
   - Expected: arch contains `src/app/ide/main.spl`
   - Expected: design contains `not the embedded app`
   - Expected: tui contains `src/lib/editor/view/file_tree.spl`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps legacy VS Code docs pointed at current shared IDE surfaces")
val arch = read_text("doc/04_architecture/vscode_rich_editor.md")
val design = read_text("doc/05_design/vscode_rich_editor.md")
val tui = read_text("doc/05_design/app/editor/vscode_rich_editor_tui.md")
expect(arch.contains("../../src/app/vscode_rich_editor")).to_equal(false)
expect(design.contains("src/app/vscode_rich_editor")).to_equal(false)
expect(tui.contains("30.view/")).to_equal(false)
expect(arch.contains("Legacy VS Code Rich Editor Architecture")).to_equal(true)
expect(design.contains("Markdown-first")).to_equal(true)
expect(tui.contains("examples/ide/**` contains sample integrations only")).to_equal(true)
expect(arch.contains("src/app/ide/main.spl")).to_equal(true)
expect(design.contains("not the embedded app")).to_equal(true)
expect(tui.contains("src/lib/editor/view/file_tree.spl")).to_equal(true)
```

</details>

#### wraps editor GUI HTML for pure Simple web before host presentation

- wraps editor GUI HTML for pure Simple web before host presentation
   - Expected: req.target equals `WEB_RENDER_TARGET_PURE_SIMPLE`
   - Expected: shell contains `gui_render_editor_area_with_diagnostics_and_hover_delay`
   - Expected: shell contains `gui_render_tab_bar_html`
   - Expected: shell contains `gui_render_file_tree_html`
   - Expected: ide contains `src/lib/editor/70.backend/gui_backend.spl`
   - Expected: ide contains `pure HTML`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("wraps editor GUI HTML for pure Simple web before host presentation")
val buffer = EditorBuffer.from_text(EditorBufferId(value: 1), "fn main() -> i64:\n    0\n")
val html = gui_render_editor_area(buffer, "simple", EditorViewport(top_row: 0, left_col: 0, width: 80, height: 4))
val req = WebRenderRequest.html(WEB_RENDER_TARGET_PURE_SIMPLE, "Simple IDE", html, "", "", 800, 600)
expect(req.target).to_equal(WEB_RENDER_TARGET_PURE_SIMPLE)
expect(req.body_html).to_contain("class=\"editor-area gui-editor-source\"")
expect(req.body_html).to_contain("contenteditable=\"true\"")
expect(req.body_html).to_contain("data-line=\"0\"")
expect(req.body_html).to_contain("data-language=\"simple\"")

val shell = read_text("src/app/editor/gui_shell_render.spl")
expect(shell.contains("gui_render_editor_area_with_diagnostics_and_hover_delay")).to_equal(true)
expect(shell.contains("gui_render_tab_bar_html")).to_equal(true)
expect(shell.contains("gui_render_file_tree_html")).to_equal(true)

val ide = read_text("doc/07_guide/app/ide_llm_integration_guide.md")
expect(ide.contains("src/lib/editor/70.backend/gui_backend.spl")).to_equal(true)
expect(ide.contains("pure HTML")).to_equal(true)
```

</details>

#### documents the live editor MCP subset without overclaiming the full catalog

- documents the live editor MCP subset without overclaiming the full catalog
   - Expected: ide contains `The live `simple mcp` server wires the safe stateful subset`
   - Expected: ide contains `editor.open_file`
   - Expected: ide contains `editor.read_buffer`
   - Expected: ide contains `editor.list_open_files`
   - Expected: ide contains `Most `editor.*` commands are not registered`
   - Expected: ide does not contain ``editor.*` is not registered in the MCP server`
   - Expected: tui contains `sample IDE`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("documents the live editor MCP subset without overclaiming the full catalog")
val ide = read_text("doc/07_guide/app/ide_llm_integration_guide.md")
val tui = read_text("doc/07_guide/app/editor_tui.md")
expect(ide.contains("The live `simple mcp` server wires the safe stateful subset")).to_equal(true)
expect(ide.contains("editor.open_file")).to_equal(true)
expect(ide.contains("editor.read_buffer")).to_equal(true)
expect(ide.contains("editor.list_open_files")).to_equal(true)
expect(ide.contains("Most `editor.*` commands are not registered")).to_equal(true)
expect(ide.contains("`editor.*` is not registered in the MCP server")).to_equal(false)
expect(tui.contains("sample IDE")).to_equal(true)
```

</details>

#### documents pure Simple render proof separately from Tauri shell proof

- documents pure Simple render proof separately from Tauri shell proof
   - Expected: tui contains `test/unit/lib/editor/editor_web_tauri_render_contract_spec.spl`
   - Expected: tui contains `pure Simple WebRender artifacts and the Tauri`
   - Expected: tui contains `live Tauri editor-shell WebView`
   - Expected: ide contains `Tauri evidence`
   - Expected: ide contains `test/unit/lib/editor/editor_web_tauri_render_contract_spec.spl`
   - Expected: ide contains `test/unit/app/ui/tauri_backend_spec.spl`
   - Expected: ide contains `not yet a live Tauri editor-shell`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("documents pure Simple render proof separately from Tauri shell proof")
val tui = read_text("doc/07_guide/app/editor_tui.md")
val ide = read_text("doc/07_guide/app/ide_llm_integration_guide.md")
expect(tui.contains("test/unit/lib/editor/editor_web_tauri_render_contract_spec.spl")).to_equal(true)
expect(tui.contains("pure Simple WebRender artifacts and the Tauri")).to_equal(true)
expect(tui.contains("live Tauri editor-shell WebView")).to_equal(true)
expect(ide.contains("Tauri evidence")).to_equal(true)
expect(ide.contains("test/unit/lib/editor/editor_web_tauri_render_contract_spec.spl")).to_equal(true)
expect(ide.contains("test/unit/app/ui/tauri_backend_spec.spl")).to_equal(true)
expect(ide.contains("not yet a live Tauri editor-shell")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/editor/host_simpleos_surface_contract_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering editor host and SimpleOS surface contract.
- editor host and SimpleOS surface contract

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `f68ffa379b2ca0e255598b053b160c1bb88ac02bbd213c22eac15d9970ea9bba`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f68ffa379b2ca0e255598b053b160c1bb88ac02bbd213c22eac15d9970ea9bba`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f68ffa379b2ca0e255598b053b160c1bb88ac02bbd213c22eac15d9970ea9bba`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/lib/editor/host_simpleos_surface_contract_spec.spl
mirror: doc/06_spec/unit/lib/editor/host_simpleos_surface_contract_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/editor/host_simpleos_surface_contract_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/editor/host_simpleos_surface_contract_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/editor/host_simpleos_surface_contract_spec.spl:44:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps shared editor services runtime neutral' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/editor/host_simpleos_surface_contract_spec.spl:56:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps IDE launch entrypoints host and SimpleOS runnable' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/editor/host_simpleos_surface_contract_spec.spl:64:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps the TUI path SimpleOS-safe' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
