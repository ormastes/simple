# Claude Full Agent Wizard Small Components

> Checks modern SSpec parity for small agent wizard and picker components.

<!-- sdn-diagram:id=agent_wizard_small_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=agent_wizard_small_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

agent_wizard_small_spec -> std
agent_wizard_small_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=agent_wizard_small_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full Agent Wizard Small Components

Checks modern SSpec parity for small agent wizard and picker components.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/components/agent_wizard_small_spec.spl` |
| Updated | 2026-07-05 |
| Generator | `simple spipe-docgen` (Simple) |

Checks modern SSpec parity for small agent wizard and picker components.

## Scenarios

### Claude full agent wizard small components

#### should normalize picker values

- Resolve colors and models
   - Expected: normalizeAgentColor("BLUE") equals `blue`
   - Expected: normalizeAgentColor("bad") equals `gray`
   - Expected: normalizeAgentModel("OPUS") equals `opus`
   - Expected: normalizeAgentModel("bad") equals `sonnet`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Resolve colors and models")
expect(normalizeAgentColor("BLUE")).to_equal("blue")
expect(normalizeAgentColor("bad")).to_equal("gray")
expect(colorPickerLabel("green")).to_contain("green")
expect(availableAgentColors()).to_contain("purple")
expect(normalizeAgentModel("OPUS")).to_equal("opus")
expect(normalizeAgentModel("bad")).to_equal("sonnet")
expect(modelSelectorLabel("haiku")).to_contain("haiku")
```

</details>

#### should model wizard progress

- Create wizard state
   - Expected: wizardStepTitle(state) equals `Name`
   - Expected: canContinueWizard(state) is true
- Check step helpers
   - Expected: colorStepCanContinue("blue") is true
   - Expected: colorStepCanContinue("") is false
   - Expected: descriptionStepCanContinue("too short") is false
   - Expected: descriptionStepCanContinue("a useful coding assistant") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Create wizard state")
val state = CreateAgentWizardState.new("Name", "reviewer", "reviews pull requests")
expect(wizardStepTitle(state)).to_equal("Name")
expect(canContinueWizard(state)).to_equal(true)
expect(createAgentWizardSummary(state)).to_contain("reviewer")

step("Check step helpers")
expect(colorStepTitle()).to_contain("color")
expect(colorStepCanContinue("blue")).to_equal(true)
expect(colorStepCanContinue("")).to_equal(false)
expect(confirmStepWrapperStatus(true)).to_contain("Ready")
expect(confirmStepWrapperStatus(false)).to_contain("Missing")
expect(descriptionStepCanContinue("too short")).to_equal(false)
expect(descriptionStepCanContinue("a useful coding assistant")).to_equal(true)
expect(descriptionStepHint("a useful coding assistant")).to_contain("ready")
```

</details>

#### should check modeled TypeScript source floors

- Read source line helpers
   - Expected: colorPickerSourceLinesModeled() equals `111`
   - Expected: modelSelectorSourceLinesModeled() equals `67`
   - Expected: createAgentWizardSourceLinesModeled() equals `96`
   - Expected: colorStepSourceLinesModeled() equals `83`
   - Expected: confirmStepWrapperSourceLinesModeled() equals `73`
   - Expected: descriptionStepSourceLinesModeled() equals `122`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Read source line helpers")
expect(colorPickerSourceLinesModeled()).to_equal(111)
expect(modelSelectorSourceLinesModeled()).to_equal(67)
expect(createAgentWizardSourceLinesModeled()).to_equal(96)
expect(colorStepSourceLinesModeled()).to_equal(83)
expect(confirmStepWrapperSourceLinesModeled()).to_equal(73)
expect(descriptionStepSourceLinesModeled()).to_equal(122)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
