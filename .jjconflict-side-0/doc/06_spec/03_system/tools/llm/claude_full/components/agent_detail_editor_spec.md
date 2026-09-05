# Claude Full Agent Detail and Editor

> Checks agent detail row/action parity and editor validation/save summaries.

<!-- sdn-diagram:id=agent_detail_editor_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=agent_detail_editor_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

agent_detail_editor_spec -> std
agent_detail_editor_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=agent_detail_editor_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full Agent Detail and Editor

Checks agent detail row/action parity and editor validation/save summaries.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/components/agent_detail_editor_spec.spl` |
| Updated | 2026-07-05 |
| Generator | `simple spipe-docgen` (Simple) |

Checks agent detail row/action parity and editor validation/save summaries.

## Scenarios

### Claude full AgentDetail and AgentEditor

#### renders detail rows and enabled actions

- Build enabled detail
- Assert rows and summary
   - Expected: detail.statusLabel() equals `enabled`
   - Expected: rows.len() equals `6`
   - Expected: rows[0].label equals `Name`
   - Expected: rows[0].value equals `reviewer`
   - Expected: rows[3].value equals `read, write`
- Assert enabled actions
   - Expected: actions.len() equals `3`
   - Expected: actions[0].label equals `Disable`
   - Expected: actions[0].enabled is true
   - Expected: actions[2].label equals `Run`
   - Expected: actions[2].enabled is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Build enabled detail")
val detail = agentDetailReady("reviewer", "Reviews changes", "sonnet", ["read", "write"], "/agents/reviewer.md")
val rows = detail.rows()
val actions = detail.actions()

step("Assert rows and summary")
expect(detail.statusLabel()).to_equal("enabled")
expect(rows.len()).to_equal(6)
expect(rows[0].label).to_equal("Name")
expect(rows[0].value).to_equal("reviewer")
expect(rows[3].value).to_equal("read, write")
expect(detail.renderSummary()).to_contain("reviewer | enabled | sonnet")

step("Assert enabled actions")
expect(actions.len()).to_equal(3)
expect(actions[0].label).to_equal("Disable")
expect(actions[0].enabled).to_equal(true)
expect(actions[2].label).to_equal("Run")
expect(actions[2].enabled).to_equal(true)
```

</details>

#### renders missing and disabled detail states

- Build missing detail
   - Expected: missing.statusLabel() equals `missing`
   - Expected: missingRows.len() equals `3`
   - Expected: missingRows[2].value equals `/agents/planner.md`
   - Expected: missingActions[0].label equals `Create`
   - Expected: missingActions[1].enabled is false
   - Expected: missingActions[1].reason equals `agent file is missing`
- Build disabled detail
   - Expected: disabled.statusLabel() equals `disabled`
   - Expected: disabledActions[0].label equals `Enable`
   - Expected: disabledActions[2].enabled is false
   - Expected: disabledActions[2].reason equals `agent is disabled`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Build missing detail")
val missing = agentDetailMissing("planner", "/agents/planner.md")
val missingRows = missing.rows()
val missingActions = missing.actions()
expect(missing.statusLabel()).to_equal("missing")
expect(missingRows.len()).to_equal(3)
expect(missingRows[2].value).to_equal("/agents/planner.md")
expect(missingActions[0].label).to_equal("Create")
expect(missingActions[1].enabled).to_equal(false)
expect(missingActions[1].reason).to_equal("agent file is missing")

step("Build disabled detail")
val disabled = agentDetailDisabled("coder", "Codes", "opus", ["shell"], "/agents/coder.md")
val disabledActions = disabled.actions()
expect(disabled.statusLabel()).to_equal("disabled")
expect(disabledActions[0].label).to_equal("Enable")
expect(disabledActions[2].enabled).to_equal(false)
expect(disabledActions[2].reason).to_equal("agent is disabled")
```

</details>

#### validates editor drafts and renders save summaries

- Validate empty draft
   - Expected: empty.canSave() is false
   - Expected: errors.len() equals `3`
   - Expected: errors[0] equals `name is required`
   - Expected: blocked.saved is false
- Validate complete draft
   - Expected: draft.canSave() is true
   - Expected: saved.saved is true
   - Expected: saved.status equals `saved`
   - Expected: saved.toolCount equals `2`
   - Expected: saved.enabledLabel equals `disabled`
   - Expected: saved.render() equals `saved | reviewer | sonnet | tools=2 | disabled`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Validate empty draft")
val empty = agentEditorEmptyDraft()
val errors = empty.validate()
val blocked = empty.saveSummary()
expect(empty.canSave()).to_equal(false)
expect(errors.len()).to_equal(3)
expect(errors[0]).to_equal("name is required")
expect(blocked.saved).to_equal(false)
expect(blocked.render()).to_contain("blocked | name is required")

step("Validate complete draft")
val draft = agentEditorDraft("reviewer", "Reviews", "sonnet", ["read", "write"], "Review the diff", false)
val saved = draft.saveSummary()
expect(draft.canSave()).to_equal(true)
expect(saved.saved).to_equal(true)
expect(saved.status).to_equal("saved")
expect(saved.toolCount).to_equal(2)
expect(saved.enabledLabel).to_equal("disabled")
expect(saved.render()).to_equal("saved | reviewer | sonnet | tools=2 | disabled")
```

</details>

#### exports source-backed helpers

- Check detail and editor helper values
   - Expected: joinAgentTools([]) equals `none`
   - Expected: joinAgentTools(["read", "write"]) equals `read, write`
   - Expected: joinEditorErrors([]) equals `none`
   - Expected: joinEditorErrors(["name is required", "model is required"]) equals `name is required, model is required`
   - Expected: agentDetailSourceLinesModeled() equals `219`
   - Expected: agentDetailModeledStatusCount() equals `3`
   - Expected: agentDetailModeledActionCount() equals `3`
   - Expected: agentEditorSourceLinesModeled() equals `177`
   - Expected: agentEditorRequiredFieldCount() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Check detail and editor helper values")
expect(joinAgentTools([])).to_equal("none")
expect(joinAgentTools(["read", "write"])).to_equal("read, write")
expect(joinEditorErrors([])).to_equal("none")
expect(joinEditorErrors(["name is required", "model is required"])).to_equal("name is required, model is required")
expect(agentDetailSourceLinesModeled()).to_equal(219)
expect(agentDetailModeledStatusCount()).to_equal(3)
expect(agentDetailModeledActionCount()).to_equal(3)
expect(agentEditorSourceLinesModeled()).to_equal(177)
expect(agentEditorRequiredFieldCount()).to_equal(3)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
