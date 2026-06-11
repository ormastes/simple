# Host Simpleos Surface Contract Specification

> 1. assert no host tokens

<!-- sdn-diagram:id=host_simpleos_surface_contract_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=host_simpleos_surface_contract_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

host_simpleos_surface_contract_spec -> std
host_simpleos_surface_contract_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=host_simpleos_surface_contract_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Host Simpleos Surface Contract Specification

## Scenarios

### editor host and SimpleOS surface contract

#### keeps shared editor services runtime neutral

1. assert no host tokens
2. assert no host tokens
3. assert no host tokens
4. assert no host tokens
5. assert no host tokens
6. assert no host tokens
7. assert no host tokens
8. assert no host tokens


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. assert no host tokens
2. assert no host tokens
3. assert no host tokens
4. assert no host tokens


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
assert_no_host_tokens("src/app/ide/main.spl")
assert_no_host_tokens("examples/10_tooling/ide/simple_ide_launch.spl")
assert_no_host_tokens("examples/10_tooling/ide/simple_ide_render.spl")
assert_no_host_tokens("examples/10_tooling/ide/extensions/markdown-notes/main.spl")
```

</details>

#### keeps the TUI path SimpleOS-safe

1. assert no host tokens
2. assert no host tokens
3. assert no host tokens
4. assert no host tokens


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
assert_no_host_tokens("src/app/editor/tui_main.spl")
assert_no_host_tokens("src/app/editor/tui_shell.spl")
assert_no_host_tokens("src/app/editor/tui_shell_panels.spl")
assert_no_host_tokens("src/lib/editor/70.backend/tui_backend.spl")
```

</details>

#### documents host adapters outside the SimpleOS-safe path

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val guide = read_text("doc/07_guide/editor_tui.md")
expect(guide.contains("Host and SimpleOS Runtime Contract")).to_equal(true)
expect(guide.contains("src/app/editor/gui_shell_*")).to_equal(true)
expect(guide.contains("src/app/ui.tauri/")).to_equal(true)
expect(guide.contains("src/app/ui.browser/")).to_equal(true)
expect(guide.contains("src/app/ui.web/")).to_equal(true)
```

</details>

#### keeps legacy VS Code docs pointed at current shared IDE surfaces

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arch = read_text("doc/04_architecture/vscode_rich_editor.md")
val design = read_text("doc/05_design/vscode_rich_editor.md")
val tui = read_text("doc/05_design/vscode_rich_editor_tui.md")
expect(arch.contains("../../src/app/vscode_rich_editor")).to_equal(false)
expect(design.contains("src/app/vscode_rich_editor")).to_equal(false)
expect(tui.contains("30.view/")).to_equal(false)
expect(arch.contains("Legacy VS Code Rich Editor Architecture")).to_equal(true)
expect(design.contains("Markdown-first")).to_equal(true)
expect(tui.contains("examples/10_tooling/ide/**` contains sample integrations only")).to_equal(true)
expect(arch.contains("src/app/ide/main.spl")).to_equal(true)
expect(design.contains("not the embedded app")).to_equal(true)
expect(tui.contains("src/lib/editor/view/file_tree.spl")).to_equal(true)
```

</details>

#### wraps editor GUI HTML for pure Simple web before host presentation

<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

val ide = read_text("doc/07_guide/ide_llm_integration_guide.md")
expect(ide.contains("src/lib/editor/70.backend/gui_backend.spl")).to_equal(true)
expect(ide.contains("pure HTML")).to_equal(true)
```

</details>

#### documents the live editor MCP subset without overclaiming the full catalog

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ide = read_text("doc/07_guide/ide_llm_integration_guide.md")
val tui = read_text("doc/07_guide/editor_tui.md")
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tui = read_text("doc/07_guide/editor_tui.md")
val ide = read_text("doc/07_guide/ide_llm_integration_guide.md")
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
| Source | `test/01_unit/lib/editor/host_simpleos_surface_contract_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
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
