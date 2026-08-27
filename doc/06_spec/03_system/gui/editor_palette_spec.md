# Editor Palette Specification

> Tests covering editor command palette service, editor command palette wiring, editor Markdown palette entries.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Editor Palette Specification

## Scenarios

### editor command palette service

#### defines palette entries and visible state

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- defines palette entries and visible state
   - Expected: src contains `struct PaletteEntry:`
   - Expected: src contains `struct PaletteState:`
   - Expected: src contains `visible: bool`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("defines palette entries and visible state")
val src = read_text("src/lib/editor/services/command_palette.spl")
expect(src.contains("struct PaletteEntry:")).to_equal(true)
expect(src.contains("struct PaletteState:")).to_equal(true)
expect(src.contains("visible: bool")).to_equal(true)
```

</details>

#### supports show, hide, query update, and selection

- supports show, hide, query update, and selection
   - Expected: src contains `fn palette_show(state: PaletteState) -> PaletteState`
   - Expected: src contains `fn palette_hide(state: PaletteState) -> PaletteState`
   - Expected: src contains `fn palette_update_query(state: PaletteState, query: text) -> PaletteState`
   - Expected: src contains `fn palette_selected(state: PaletteState) -> PaletteEntry`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("supports show, hide, query update, and selection")
val src = read_text("src/lib/editor/services/command_palette.spl")
expect(src.contains("fn palette_show(state: PaletteState) -> PaletteState")).to_equal(true)
expect(src.contains("fn palette_hide(state: PaletteState) -> PaletteState")).to_equal(true)
expect(src.contains("fn palette_update_query(state: PaletteState, query: text) -> PaletteState")).to_equal(true)
expect(src.contains("fn palette_selected(state: PaletteState) -> PaletteEntry")).to_equal(true)
```

</details>

#### uses fuzzy matching for IDE-style command lookup

- uses fuzzy matching for IDE-style command lookup
   - Expected: src contains `fn fuzzy_match(query: text, candidate: text) -> bool`
   - Expected: src contains `fn fuzzy_score(query: text, candidate: text) -> i64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("uses fuzzy matching for IDE-style command lookup")
val src = read_text("src/lib/editor/services/command_palette.spl")
expect(src.contains("fn fuzzy_match(query: text, candidate: text) -> bool")).to_equal(true)
expect(src.contains("fn fuzzy_score(query: text, candidate: text) -> i64")).to_equal(true)
```

</details>

#### uses a typed score record for parser-safe ranking

- uses a typed score record for parser-safe ranking
   - Expected: src contains `struct PaletteScore:`
   - Expected: src contains `var scored: [PaletteScore]`
   - Expected: src contains `PaletteScore(score: sc`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("uses a typed score record for parser-safe ranking")
val src = read_text("src/lib/editor/services/command_palette.spl")
expect(src.contains("struct PaletteScore:")).to_equal(true)
expect(src.contains("var scored: [PaletteScore]")).to_equal(true)
expect(src.contains("PaletteScore(score: sc")).to_equal(true)
```

</details>

### editor command palette wiring

#### controller opens the palette from normal-mode Ctrl+P

- controller opens the palette from normal-mode Ctrl+P
   - Expected: src contains `if key == "\\x10"`
   - Expected: src contains `ctrl_open_palette(ctrl)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("controller opens the palette from normal-mode Ctrl+P")
val src = read_text("src/app/editor/editor_ctrl_core.spl")
expect(src.contains("if key == \"\\x10\"")).to_equal(true)
expect(src.contains("ctrl_open_palette(ctrl)")).to_equal(true)
```

</details>

#### controller routes palette keys before editor mode handling

- controller routes palette keys before editor mode handling
   - Expected: src contains `if ctrl.palette_state != nil and ctrl.palette_state.visible:`
   - Expected: src contains `return ctrl_dispatch_palette_key(ctrl, key)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("controller routes palette keys before editor mode handling")
val src = read_text("src/app/editor/editor_ctrl_core.spl")
expect(src.contains("if ctrl.palette_state != nil and ctrl.palette_state.visible:")).to_equal(true)
expect(src.contains("return ctrl_dispatch_palette_key(ctrl, key)")).to_equal(true)
```

</details>

#### controller merges Markdown commands only for Markdown documents

- controller merges Markdown commands only for Markdown documents
   - Expected: src contains `doc.language_id == "markdown"`
   - Expected: src contains `md_commands_palette_entries()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("controller merges Markdown commands only for Markdown documents")
val src = read_text("src/app/editor/editor_ctrl_core.spl")
expect(src.contains("doc.language_id == \"markdown\"")).to_equal(true)
expect(src.contains("md_commands_palette_entries()")).to_equal(true)
```

</details>

#### controller dispatches markdown commands through extension host registration

- controller dispatches markdown commands through extension host registration
   - Expected: controller_src contains `extension_host: ExtensionHost`
   - Expected: controller_src contains `extension_host_with_builtins()`
   - Expected: src contains `ctrl.extension_host.activate_command(command_name)`
   - Expected: src contains `ctrl.extension_host.emit_event("onWillExecuteCommand", command_name)`
   - Expected: src contains `ctrl.extension_host.emit_event("onDidExecuteCommand", command_name)`
   - Expected: src contains `extension_command_entry_name(registered_command) == "markdown-language"`
   - Expected: src contains `ctrl.extension_host.dispatch_external_command(command_name, command_payload)`
   - Expected: src contains `"extension command queued: " + extension_command_invocation_command_id(invoca... (full value in folded executable source)`
   - Expected: src contains `fn ctrl_execute_markdown_extension_command(ctrl: EditorController, command_na... (full value in folded executable source)`
   - Expected: src contains `md_commands_dispatch(command_name, doc.markdown_state()`
   - Expected: src contains `md_apply_result(buffer, cmd_result)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("controller dispatches markdown commands through extension host registration")
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

- registers Obsidian-style document actions
   - Expected: src contains `Markdown: Toggle Preview`
   - Expected: src contains `Markdown: Toggle Outline`
   - Expected: src contains `Markdown: Go to Heading`
   - Expected: src contains `Markdown: Document Statistics`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("registers Obsidian-style document actions")
val src = read_text("src/lib/editor/extensions/builtin/md_commands.spl")
expect(src.contains("Markdown: Toggle Preview")).to_equal(true)
expect(src.contains("Markdown: Toggle Outline")).to_equal(true)
expect(src.contains("Markdown: Go to Heading")).to_equal(true)
expect(src.contains("Markdown: Document Statistics")).to_equal(true)
```

</details>

#### registers common Markdown authoring commands

- registers common Markdown authoring commands
   - Expected: src contains `Markdown: Toggle Task`
   - Expected: src contains `Markdown: Insert Table`
   - Expected: src contains `Markdown: Insert Link`
   - Expected: src contains `Markdown: Insert Code Block`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("registers common Markdown authoring commands")
val src = read_text("src/lib/editor/extensions/builtin/md_commands.spl")
expect(src.contains("Markdown: Toggle Task")).to_equal(true)
expect(src.contains("Markdown: Insert Table")).to_equal(true)
expect(src.contains("Markdown: Insert Link")).to_equal(true)
expect(src.contains("Markdown: Insert Code Block")).to_equal(true)
```

</details>

#### keeps markdown commands namespaced for IDE-style routing

- keeps markdown commands namespaced for IDE-style routing
   - Expected: src contains `command_name: "markdown.togglePreview"`
   - Expected: src contains `command_name: "markdown.toggleOutline"`
   - Expected: src contains `command_name: "markdown.insertTable"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("keeps markdown commands namespaced for IDE-style routing")
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
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering editor command palette service, editor command palette wiring, editor Markdown palette entries.
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `c0671725a37db0d56b6179dd5e747ed1f029166cffd9f199e40904b75d1c0ad0`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `c0671725a37db0d56b6179dd5e747ed1f029166cffd9f199e40904b75d1c0ad0`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `c0671725a37db0d56b6179dd5e747ed1f029166cffd9f199e40904b75d1c0ad0`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/gui/editor_palette_spec.spl
mirror: doc/06_spec/03_system/gui/editor_palette_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/gui/editor_palette_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/gui/editor_palette_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/gui/editor_palette_spec.spl:20:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'defines palette entries and visible state' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/gui/editor_palette_spec.spl:28:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'supports show, hide, query update, and selection' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/gui/editor_palette_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'uses fuzzy matching for IDE-style command lookup' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
