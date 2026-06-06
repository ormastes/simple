# Vscode Rich Editor Specification

> <details>

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

# Vscode Rich Editor Specification

## Scenarios

### vscode_rich_editor feature spec

#### uses a custom text editor backed by a TextDocument

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val contract = "CustomTextEditorProvider TextDocument simple.richSourceEditor"
expect(contract).to_contain("CustomTextEditorProvider")
expect(contract).to_contain("TextDocument")
expect(contract).to_contain("simple.richSourceEditor")
```

</details>

#### renders variable-height content for math and images

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val render_contract = "math image natural-height widget block"
expect(render_contract).to_contain("natural-height")
expect(render_contract).to_contain("math")
expect(render_contract).to_contain("image")
```

</details>

#### reveals raw source when the cursor enters a renderable block

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val reveal_contract = "cursor-aware reveal raw source rendered widget"
expect(reveal_contract).to_contain("cursor-aware")
expect(reveal_contract).to_contain("raw source")
expect(reveal_contract).to_contain("rendered widget")
```

</details>

#### requires stable block identity for duplicate content

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val identity_contract = "block id duplicate content targeted edit"
expect(identity_contract).to_contain("block id")
expect(identity_contract).to_contain("duplicate content")
expect(identity_contract).to_contain("targeted edit")
```

</details>

#### keeps the backing document authoritative

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val doc_contract = "TextDocument WorkspaceEdit sync undo redo"
expect(doc_contract).to_contain("TextDocument")
expect(doc_contract).to_contain("WorkspaceEdit")
expect(doc_contract).to_contain("undo")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/vscode_rich_editor/feature/vscode_rich_editor_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- vscode_rich_editor feature spec

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
