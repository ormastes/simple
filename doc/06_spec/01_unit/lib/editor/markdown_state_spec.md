# Markdown State Specification

> Tests covering markdown_state via MdEditorState.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Markdown State Specification

## Scenarios

### markdown_state via MdEditorState

#### new state has preview and outline hidden

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- new state has preview and outline hidden
   - Expected: md_editor_state_preview_visible(state) is false
   - Expected: md_editor_state_outline_visible(state) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("new state has preview and outline hidden")
val state = md_editor_state_new()
expect(md_editor_state_preview_visible(state)).to_equal(false)
expect(md_editor_state_outline_visible(state)).to_equal(false)
```

</details>

#### toggle preview shows then hides

- toggle preview shows then hides
   - Expected: result1.preview_visible is true
   - Expected: result2.preview_visible is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("toggle preview shows then hides")
val state = md_editor_state_new()
val result1 = md_commands_dispatch("markdown.togglePreview", state, "", 0, 0)
expect(result1.preview_visible).to_equal(true)
val state2 = md_command_result_state(result1)
val result2 = md_commands_dispatch("markdown.togglePreview", state2, "", 0, 0)
expect(result2.preview_visible).to_equal(false)
```

</details>

#### toggle outline shows then hides

- toggle outline shows then hides
   - Expected: result1.outline_visible is true
   - Expected: result2.outline_visible is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("toggle outline shows then hides")
val state = md_editor_state_new()
val result1 = md_commands_dispatch("markdown.toggleOutline", state, "", 0, 0)
expect(result1.outline_visible).to_equal(true)
val state2 = md_command_result_state(result1)
val result2 = md_commands_dispatch("markdown.toggleOutline", state2, "", 0, 0)
expect(result2.outline_visible).to_equal(false)
```

</details>

#### repeated preview toggles return to initial state

- repeated preview toggles return to initial state
   - Expected: r3.preview_visible is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("repeated preview toggles return to initial state")
val state = md_editor_state_new()
val r1 = md_commands_dispatch("markdown.togglePreview", state, "", 0, 0)
val r2 = md_commands_dispatch("markdown.togglePreview", md_command_result_state(r1), "", 0, 0)
val r3 = md_commands_dispatch("markdown.togglePreview", md_command_result_state(r2), "", 0, 0)
expect(r3.preview_visible).to_equal(true)
```

</details>

#### toggle preview does not affect outline state

- toggle preview does not affect outline state
   - Expected: md_editor_state_outline_visible(after_preview) is true
   - Expected: md_editor_state_preview_visible(after_preview) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("toggle preview does not affect outline state")
val state = md_editor_state_new()
val after_outline = md_command_result_state(md_commands_dispatch("markdown.toggleOutline", state, "", 0, 0))
val after_preview = md_command_result_state(md_commands_dispatch("markdown.togglePreview", after_outline, "", 0, 0))
expect(md_editor_state_outline_visible(after_preview)).to_equal(true)
expect(md_editor_state_preview_visible(after_preview)).to_equal(true)
```

</details>

#### toggle outline does not affect preview state

- toggle outline does not affect preview state
   - Expected: md_editor_state_preview_visible(after_outline) is true
   - Expected: md_editor_state_outline_visible(after_outline) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("toggle outline does not affect preview state")
val state = md_editor_state_new()
val after_preview = md_command_result_state(md_commands_dispatch("markdown.togglePreview", state, "", 0, 0))
val after_outline = md_command_result_state(md_commands_dispatch("markdown.toggleOutline", after_preview, "", 0, 0))
expect(md_editor_state_preview_visible(after_outline)).to_equal(true)
expect(md_editor_state_outline_visible(after_outline)).to_equal(true)
```

</details>

#### state on empty buffer toggles do not crash

- state on empty buffer toggles do not crash
   - Expected: result.preview_visible is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("state on empty buffer toggles do not crash")
val state = md_editor_state_new()
val result = md_commands_dispatch("markdown.togglePreview", state, "", 0, 0)
expect(result.preview_visible).to_equal(true)
```

</details>

#### unknown command preserves state unchanged

- unknown command preserves state unchanged
   - Expected: result.preview_visible is false
   - Expected: result.outline_visible is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("unknown command preserves state unchanged")
val state = md_editor_state_new()
val result = md_commands_dispatch("unknown.command", state, "", 0, 0)
expect(result.preview_visible).to_equal(false)
expect(result.outline_visible).to_equal(false)
```

</details>

#### command_result_state round-trips preview and outline

- command_result_state round-trips preview and outline
   - Expected: md_editor_state_preview_visible(final_state) is true
   - Expected: md_editor_state_outline_visible(final_state) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("command_result_state round-trips preview and outline")
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
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering markdown_state via MdEditorState.
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `7656da796472e4a3d90b510fadb2e532e040b84963722607a7f7809eb75bfe6f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `7656da796472e4a3d90b510fadb2e532e040b84963722607a7f7809eb75bfe6f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `7656da796472e4a3d90b510fadb2e532e040b84963722607a7f7809eb75bfe6f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/editor/markdown_state_spec.spl
mirror: doc/06_spec/01_unit/lib/editor/markdown_state_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/editor/markdown_state_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/editor/markdown_state_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/editor/markdown_state_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'new state has preview and outline hidden' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/editor/markdown_state_spec.spl:25:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'toggle preview shows then hides' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/editor/markdown_state_spec.spl:35:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'toggle outline shows then hides' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
