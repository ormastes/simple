# Editor Palette Specification

> <details>

<!-- sdn-diagram:id=editor_palette_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=editor_palette_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

editor_palette_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=editor_palette_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Editor Palette Specification

## Scenarios

### editor command palette service

#### defines palette entries and visible state

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/services/command_palette.spl")
expect(src.contains("struct PaletteEntry:")).to_equal(true)
expect(src.contains("struct PaletteState:")).to_equal(true)
expect(src.contains("visible: bool")).to_equal(true)
```

</details>

#### supports show, hide, query update, and selection

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/services/command_palette.spl")
expect(src.contains("fn palette_show(state: PaletteState) -> PaletteState")).to_equal(true)
expect(src.contains("fn palette_hide(state: PaletteState) -> PaletteState")).to_equal(true)
expect(src.contains("fn palette_update_query(state: PaletteState, query: text) -> PaletteState")).to_equal(true)
expect(src.contains("fn palette_selected(state: PaletteState) -> PaletteEntry")).to_equal(true)
```

</details>

#### uses fuzzy matching for IDE-style command lookup

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/services/command_palette.spl")
expect(src.contains("fn fuzzy_match(query: text, candidate: text) -> bool")).to_equal(true)
expect(src.contains("fn fuzzy_score(query: text, candidate: text) -> i64")).to_equal(true)
```

</details>

#### uses a typed score record for parser-safe ranking

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/services/command_palette.spl")
expect(src.contains("struct PaletteScore:")).to_equal(true)
expect(src.contains("var scored: [PaletteScore]")).to_equal(true)
expect(src.contains("PaletteScore(score: sc")).to_equal(true)
```

</details>

### editor command palette wiring

#### controller opens the palette from normal-mode Ctrl+P

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/app/editor/editor_ctrl_core.spl")
expect(src.contains("if key == \"\\x10\"")).to_equal(true)
expect(src.contains("ctrl_open_palette(ctrl)")).to_equal(true)
```

</details>

#### controller routes palette keys before editor mode handling

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/app/editor/editor_ctrl_core.spl")
expect(src.contains("if ctrl.palette_state != nil and ctrl.palette_state.visible:")).to_equal(true)
expect(src.contains("return ctrl_dispatch_palette_key(ctrl, key)")).to_equal(true)
```

</details>

#### controller merges Markdown commands only for Markdown documents

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/app/editor/editor_ctrl_core.spl")
expect(src.contains("doc.language_id == \"markdown\"")).to_equal(true)
expect(src.contains("md_commands_palette_entries()")).to_equal(true)
```

</details>

#### controller dispatches markdown commands through extension host registration

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val controller_src = read_text("src/app/editor/editor_controller.spl")
val src = read_text("src/app/editor/editor_ctrl_core.spl")
expect(controller_src.contains("extension_host: ExtensionHost")).to_equal(true)
expect(controller_src.contains("extension_host_with_builtins()")).to_equal(true)
expect(src.contains("ctrl.extension_host.activate_command(command_name)")).to_equal(true)
expect(src.contains("ctrl.extension_host.emit_event(\"onWillExecuteCommand\", command_name)")).to_equal(true)
expect(src.contains("ctrl.extension_host.emit_event(\"onDidExecuteCommand\", command_name)")).to_equal(true)
expect(src.contains("extension_command_entry_name(registered_command) == \"markdown-language\"")).to_equal(true)
expect(src.contains("ctrl.extension_host.dispatch_external_command(command_name, command_payload)")).to_equal(true)
expect(src.contains("\"extension command queued: \" + extension_command_invocation_command_id(invocation)")).to_equal(true)
expect(src.contains("fn ctrl_execute_markdown_extension_command(ctrl: EditorController, command_name: text)")).to_equal(true)
expect(src.contains("md_commands_dispatch(command_name, doc.markdown_state()")).to_equal(true)
expect(src.contains("md_apply_result(buffer, cmd_result)")).to_equal(true)
```

</details>

### editor Markdown palette entries

#### registers Obsidian-style document actions

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/extensions/builtin/md_commands.spl")
expect(src.contains("Markdown: Toggle Preview")).to_equal(true)
expect(src.contains("Markdown: Toggle Outline")).to_equal(true)
expect(src.contains("Markdown: Go to Heading")).to_equal(true)
expect(src.contains("Markdown: Document Statistics")).to_equal(true)
```

</details>

#### registers common Markdown authoring commands

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/extensions/builtin/md_commands.spl")
expect(src.contains("Markdown: Toggle Task")).to_equal(true)
expect(src.contains("Markdown: Insert Table")).to_equal(true)
expect(src.contains("Markdown: Insert Link")).to_equal(true)
expect(src.contains("Markdown: Insert Code Block")).to_equal(true)
```

</details>

#### keeps markdown commands namespaced for IDE-style routing

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/extensions/builtin/md_commands.spl")
expect(src.contains("command_name: \"markdown.togglePreview\"")).to_equal(true)
expect(src.contains("command_name: \"markdown.toggleOutline\"")).to_equal(true)
expect(src.contains("command_name: \"markdown.insertTable\"")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/gui/editor_palette_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- editor command palette service
- editor command palette wiring
- editor Markdown palette entries

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
