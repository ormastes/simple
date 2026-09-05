# Claude Full Agent Wizard Step Components

> Checks modern SSpec parity for the remaining agent wizard step models.

<!-- sdn-diagram:id=agent_wizard_steps_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=agent_wizard_steps_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

agent_wizard_steps_spec -> std
agent_wizard_steps_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=agent_wizard_steps_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full Agent Wizard Step Components

Checks modern SSpec parity for the remaining agent wizard step models.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/components/agent_wizard_steps_spec.spl` |
| Updated | 2026-07-05 |
| Generator | `simple spipe-docgen` (Simple) |

Checks modern SSpec parity for the remaining agent wizard step models.

## Scenarios

### Claude full agent wizard step components

#### should normalize wizard selections

- Resolve location memory method model and type
   - Expected: normalizeAgentLocation("GLOBAL") equals `global`
   - Expected: normalizeMemoryMode("none") equals `none`
   - Expected: normalizeAgentMethod("generate") equals `generate`
   - Expected: normalizeModelStep("opus") equals `opus`
   - Expected: normalizeAgentKind("reviewer") equals `reviewer`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Resolve location memory method model and type")
expect(normalizeAgentLocation("GLOBAL")).to_equal("global")
expect(normalizeMemoryMode("none")).to_equal("none")
expect(normalizeAgentMethod("generate")).to_equal("generate")
expect(normalizeModelStep("opus")).to_equal("opus")
expect(normalizeAgentKind("reviewer")).to_equal("reviewer")
expect(typeStepSummary("specialist")).to_contain("specialist")
```

</details>

#### should validate prompt and tools steps

- Check prompt details
   - Expected: promptStepCanContinue("short") is false
   - Expected: promptStepCanContinue("review all pull requests") is true
- Check tool selection
   - Expected: toolsStepCanContinue([]) is false
   - Expected: toolsStepCanContinue(["read", "edit"]) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Check prompt details")
expect(promptStepCanContinue("short")).to_equal(false)
expect(promptStepCanContinue("review all pull requests")).to_equal(true)
expect(promptStepHint("review all pull requests")).to_contain("ready")

step("Check tool selection")
expect(toolsStepCanContinue([])).to_equal(false)
expect(toolsStepCanContinue(["read", "edit"])).to_equal(true)
expect(toolsStepSummary(["read", "edit"])).to_contain("2")
```

</details>

#### should summarize shared agent type data

- Render a shared type summary


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Render a shared type summary")
val summary = AgentTypeSummary.new("reviewer", "sonnet", "blue")
expect(agentTypeSummaryLabel(summary)).to_contain("reviewer")
expect(agentTypeSummaryLabel(summary)).to_contain("sonnet")
```

</details>

#### should check modeled TypeScript source floors

- Read source line helpers
   - Expected: agentTypesSourceLinesModeled() equals `27`
   - Expected: locationStepSourceLinesModeled() equals `79`
   - Expected: memoryStepSourceLinesModeled() equals `112`
   - Expected: methodStepSourceLinesModeled() equals `79`
   - Expected: modelStepSourceLinesModeled() equals `51`
   - Expected: promptStepSourceLinesModeled() equals `127`
   - Expected: toolsStepSourceLinesModeled() equals `60`
   - Expected: typeStepSourceLinesModeled() equals `102`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Read source line helpers")
expect(agentTypesSourceLinesModeled()).to_equal(27)
expect(locationStepSourceLinesModeled()).to_equal(79)
expect(memoryStepSourceLinesModeled()).to_equal(112)
expect(methodStepSourceLinesModeled()).to_equal(79)
expect(modelStepSourceLinesModeled()).to_equal(51)
expect(promptStepSourceLinesModeled()).to_equal(127)
expect(toolsStepSourceLinesModeled()).to_equal(60)
expect(typeStepSourceLinesModeled()).to_equal(102)
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
