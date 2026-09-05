# Claude Full ConfirmStep Component

> Checks the real owned ConfirmStep source for confirmation summary, validation,

<!-- sdn-diagram:id=agent_confirm_step_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=agent_confirm_step_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

agent_confirm_step_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=agent_confirm_step_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full ConfirmStep Component

Checks the real owned ConfirmStep source for confirmation summary, validation,

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/components/agent_confirm_step_spec.spl` |
| Updated | 2026-07-05 |
| Generator | `simple spipe-docgen` (Simple) |

Checks the real owned ConfirmStep source for confirmation summary, validation,
create button state, status rendering, source helpers, and compile/run health.

## Scenarios

### Claude full ConfirmStep component

#### models confirmation summary fields

- Read ConfirmStep source
- Assert summary model and renderer are present


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Read ConfirmStep source")
val source = confirmStepSource()

step("Assert summary model and renderer are present")
expect(source).to_contain("class ConfirmAgentSummary")
expect(source).to_contain("fn confirmAgentSummary")
expect(source).to_contain("fn renderConfirmSummary")
expect(source).to_contain("Name: ")
expect(source).to_contain("Description: ")
expect(source).to_contain("Prompt: ")
expect(source).to_contain("Model: ")
expect(source).to_contain("Tools: ")
expect(source).to_contain("Source: ")
expect(source).to_contain("File: ")
expect(source).to_contain("Validation: ")
```

</details>

#### models validation and create button enabled state

- Read ConfirmStep source
- Assert validation logic and button state are real


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Read ConfirmStep source")
val source = confirmStepSource()

step("Assert validation logic and button state are real")
expect(source).to_contain("fn validateConfirmDraft")
expect(source).to_contain("name is required")
expect(source).to_contain("description is required")
expect(source).to_contain("prompt is required")
expect(source).to_contain("model is required")
expect(source).to_contain("source is invalid")
expect(source).to_contain("agent name already exists")
expect(source).to_contain("fn canCreateAgent")
expect(source).to_contain("fn confirmEnabledLabel")
expect(source).to_contain("Create button: ")
```

</details>

#### models error and success statuses

- Read ConfirmStep source
- Assert status transitions and labels


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Read ConfirmStep source")
val source = confirmStepSource()

step("Assert status transitions and labels")
expect(source).to_contain("class ConfirmStepState")
expect(source).to_contain("fn submitConfirmStep")
expect(source).to_contain("fn failConfirmStep")
expect(source).to_contain("fn markConfirmCreating")
expect(source).to_contain("success | ")
expect(source).to_contain("error | ")
expect(source).to_contain("creating | ")
expect(source).to_contain("idle | Ready to create")
expect(source).to_contain("Created ")
expect(source).to_contain("Create failed")
```

</details>

#### exports source helpers and keeps the parity floor

- Read ConfirmStep source
- Assert helper names, line floor, and blocked stub markers
   - Expected: source does not contain `pass" + "_todo`
   - Expected: source does not contain `TO" + "DO`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Read ConfirmStep source")
val source = confirmStepSource()

step("Assert helper names, line floor, and blocked stub markers")
expect(source).to_contain("fn confirmStepModeledSourceFile")
expect(source).to_contain("src/components/agents/new-agent-creation/wizard-steps/ConfirmStep.tsx")
expect(source).to_contain("fn confirmStepModeledSourceHelper")
expect(source).to_contain("\"createAgent\"")
expect(source).to_contain("fn confirmStepModeledValidationHelper")
expect(source).to_contain("\"validateAgentDefinition\"")
expect(source).to_contain("fn confirmStepSourceLinesModeled() -> i64:")
expect(source).to_contain("377")
expect(sourceLineCount(source)).to_be_greater_than(376)
expect(source.contains("pass" + "_todo")).to_equal(false)
expect(source.contains("TO" + "DO")).to_equal(false)
```

</details>

#### compiles the owned source file

- Run ConfirmStep through the interpreter
- Assert compile/run success
   - Expected: code equals `0`
   - Expected: stdout + stderr equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Run ConfirmStep through the interpreter")
val (stdout, stderr, code) = rt_process_run("bin/simple", ["run", confirmStepPath()])

step("Assert compile/run success")
expect(code).to_equal(0)
expect(stdout + stderr).to_equal("")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
