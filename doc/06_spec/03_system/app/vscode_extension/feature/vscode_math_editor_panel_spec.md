# Vscode Math Editor Panel Specification

> <details>

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

# Vscode Math Editor Panel Specification

## Scenarios

### vscode_math_editor_panel feature spec

#### renders an active panel shell with sync and pending states

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val panel_contract = "panel-root active active-strip sync-pending math-source request-sync setSelectionRange"
expect(panel_contract).to_contain("panel-root")
expect(panel_contract).to_contain("active-strip")
expect(panel_contract).to_contain("sync-pending")
```

</details>

#### keeps the source editor canonical for edit delegation

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val edit_contract = "TextEditor.edit block.contentRange source textarea"
expect(edit_contract).to_contain("TextEditor.edit")
expect(edit_contract).to_contain("block.contentRange")
expect(edit_contract).to_contain("textarea")
```

</details>

#### renders an empty state when no math block is active

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val empty_contract = "Move the cursor onto a math block in the source editor."
expect(empty_contract).to_contain("Move the cursor onto a math block")
```

</details>

#### requires selection mirroring back to the source textarea

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val selection_contract = "selectionStart selectionEnd setSelectionRange source sync"
expect(selection_contract).to_contain("selectionStart")
expect(selection_contract).to_contain("selectionEnd")
expect(selection_contract).to_contain("setSelectionRange")
```

</details>

#### keeps hover and inline rendering as compatibility paths

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val compatibility_contract = "simple.math.toggleSyncPanel simple.math.togglePreview MathHoverProvider MathDecorationProvider"
expect(compatibility_contract).to_contain("simple.math.toggleSyncPanel")
expect(compatibility_contract).to_contain("simple.math.togglePreview")
expect(compatibility_contract).to_contain("MathHoverProvider")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/vscode_extension/feature/vscode_math_editor_panel_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- vscode_math_editor_panel feature spec

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
