# Markdown State Specification

> <details>

<!-- sdn-diagram:id=markdown_state_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=markdown_state_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

markdown_state_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=markdown_state_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Markdown State Specification

## Scenarios

### markdown_state via MdEditorState

#### new state has preview and outline hidden

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val state = md_editor_state_new()
expect(md_editor_state_preview_visible(state)).to_equal(false)
expect(md_editor_state_outline_visible(state)).to_equal(false)
```

</details>

#### toggle preview shows then hides

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val state = md_editor_state_new()
val result1 = md_commands_dispatch("markdown.togglePreview", state, "", 0, 0)
expect(result1.preview_visible).to_equal(true)
val state2 = md_command_result_state(result1)
val result2 = md_commands_dispatch("markdown.togglePreview", state2, "", 0, 0)
expect(result2.preview_visible).to_equal(false)
```

</details>

#### toggle outline shows then hides

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val state = md_editor_state_new()
val result1 = md_commands_dispatch("markdown.toggleOutline", state, "", 0, 0)
expect(result1.outline_visible).to_equal(true)
val state2 = md_command_result_state(result1)
val result2 = md_commands_dispatch("markdown.toggleOutline", state2, "", 0, 0)
expect(result2.outline_visible).to_equal(false)
```

</details>

#### repeated preview toggles return to initial state

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val state = md_editor_state_new()
val r1 = md_commands_dispatch("markdown.togglePreview", state, "", 0, 0)
val r2 = md_commands_dispatch("markdown.togglePreview", md_command_result_state(r1), "", 0, 0)
val r3 = md_commands_dispatch("markdown.togglePreview", md_command_result_state(r2), "", 0, 0)
expect(r3.preview_visible).to_equal(true)
```

</details>

#### toggle preview does not affect outline state

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val state = md_editor_state_new()
val after_outline = md_command_result_state(md_commands_dispatch("markdown.toggleOutline", state, "", 0, 0))
val after_preview = md_command_result_state(md_commands_dispatch("markdown.togglePreview", after_outline, "", 0, 0))
expect(md_editor_state_outline_visible(after_preview)).to_equal(true)
expect(md_editor_state_preview_visible(after_preview)).to_equal(true)
```

</details>

#### toggle outline does not affect preview state

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val state = md_editor_state_new()
val after_preview = md_command_result_state(md_commands_dispatch("markdown.togglePreview", state, "", 0, 0))
val after_outline = md_command_result_state(md_commands_dispatch("markdown.toggleOutline", after_preview, "", 0, 0))
expect(md_editor_state_preview_visible(after_outline)).to_equal(true)
expect(md_editor_state_outline_visible(after_outline)).to_equal(true)
```

</details>

#### state on empty buffer toggles do not crash

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val state = md_editor_state_new()
val result = md_commands_dispatch("markdown.togglePreview", state, "", 0, 0)
expect(result.preview_visible).to_equal(true)
```

</details>

#### unknown command preserves state unchanged

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val state = md_editor_state_new()
val result = md_commands_dispatch("unknown.command", state, "", 0, 0)
expect(result.preview_visible).to_equal(false)
expect(result.outline_visible).to_equal(false)
```

</details>

#### command_result_state round-trips preview and outline

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val state = md_editor_state_new()
val r1 = md_commands_dispatch("markdown.togglePreview", state, "", 0, 0)
val r2 = md_commands_dispatch("markdown.toggleOutline", md_command_result_state(r1), "", 0, 0)
val final_state = md_command_result_state(r2)
expect(md_editor_state_preview_visible(final_state)).to_equal(true)
expect(md_editor_state_outline_visible(final_state)).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/editor/markdown_state_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- markdown_state via MdEditorState

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
