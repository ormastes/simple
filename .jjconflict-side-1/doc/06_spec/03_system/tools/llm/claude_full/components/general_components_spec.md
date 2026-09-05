# Claude Full General Components

> Checks modern SSpec parity for small general component models.

<!-- sdn-diagram:id=general_components_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=general_components_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

general_components_spec -> std
general_components_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=general_components_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full General Components

Checks modern SSpec parity for small general component models.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/components/general_components_spec.spl` |
| Updated | 2026-07-05 |
| Generator | `simple spipe-docgen` (Simple) |

Checks modern SSpec parity for small general component models.

## Scenarios

### Claude full general components

#### should validate agent and app state

- Validate agent draft
   - Expected: agentDisplayName("") equals `Unnamed agent`
   - Expected: agentStatusLabel(true) equals `active`
   - Expected: validateAgentDraft("", "long enough", "review pull requests").ok is false
   - Expected: validateAgentDraft("reviewer", "reviews code carefully", "review pull requests").ok is true
- Render app shell
   - Expected: appRootTitle() equals `Claude Code`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Validate agent draft")
expect(agentDisplayName("")).to_equal("Unnamed agent")
expect(agentStatusLabel(true)).to_equal("active")
expect(validateAgentDraft("", "long enough", "review pull requests").ok).to_equal(false)
expect(validateAgentDraft("reviewer", "reviews code carefully", "review pull requests").ok).to_equal(true)

step("Render app shell")
expect(appRootTitle()).to_equal("Claude Code")
expect(appRootSummary(true)).to_contain("ready")
```

</details>

#### should render approval auth and input state

- Render API key approval
   - Expected: approveApiKeyCanSubmit(approval) is true
- Render auth and input controls
   - Expected: awsAuthStatusCanRetry(false) is true
   - Expected: baseTextInputDisplay(input) equals `Ask Claude`
   - Expected: baseTextInputCanEdit(input) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Render API key approval")
val approval = ApiKeyApproval.new("aws", "sk-***", false)
expect(approveApiKeyCanSubmit(approval)).to_equal(true)
expect(approveApiKeyMessage(approval)).to_contain("Approve")

step("Render auth and input controls")
expect(awsAuthStatusLabel(false)).to_contain("not authenticated")
expect(awsAuthStatusCanRetry(false)).to_equal(true)
val input = BaseTextInputState.new("", "Ask Claude", false)
expect(baseTextInputDisplay(input)).to_equal("Ask Claude")
expect(baseTextInputCanEdit(input)).to_equal(true)
```

</details>

#### should render updater and auto mode state

- Render auto mode dialog
   - Expected: autoModeDialogVisible(dialog) is true
- Render updater state
   - Expected: autoUpdateAvailable(update) is true
   - Expected: autoUpdaterWrapperVisible(true, true) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Render auto mode dialog")
val dialog = AutoModeOptInState.new(false, false)
expect(autoModeDialogVisible(dialog)).to_equal(true)
expect(autoModeDialogMessage(dialog)).to_contain("Auto mode")

step("Render updater state")
val update = AutoUpdateState.new("1.0.0", "1.0.1", false)
expect(autoUpdateAvailable(update)).to_equal(true)
expect(autoUpdaterStatus(update)).to_contain("1.0.1")
expect(autoUpdaterWrapperVisible(true, true)).to_equal(true)
expect(autoUpdaterWrapperMessage(false, true)).to_contain("hidden")
```

</details>

#### should check modeled TypeScript source floors

- Read source line helpers
   - Expected: agentUtilsSourceLinesModeled() equals `18`
   - Expected: validateAgentSourceLinesModeled() equals `109`
   - Expected: approveApiKeySourceLinesModeled() equals `122`
   - Expected: appSourceLinesModeled() equals `55`
   - Expected: autoModeOptInDialogSourceLinesModeled() equals `141`
   - Expected: autoUpdaterSourceLinesModeled() equals `197`
   - Expected: autoUpdaterWrapperSourceLinesModeled() equals `90`
   - Expected: awsAuthStatusBoxSourceLinesModeled() equals `81`
   - Expected: baseTextInputSourceLinesModeled() equals `135`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Read source line helpers")
expect(agentUtilsSourceLinesModeled()).to_equal(18)
expect(validateAgentSourceLinesModeled()).to_equal(109)
expect(approveApiKeySourceLinesModeled()).to_equal(122)
expect(appSourceLinesModeled()).to_equal(55)
expect(autoModeOptInDialogSourceLinesModeled()).to_equal(141)
expect(autoUpdaterSourceLinesModeled()).to_equal(197)
expect(autoUpdaterWrapperSourceLinesModeled()).to_equal(90)
expect(awsAuthStatusBoxSourceLinesModeled()).to_equal(81)
expect(baseTextInputSourceLinesModeled()).to_equal(135)
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
