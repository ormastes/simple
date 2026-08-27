# Claude Full ConfirmStep Component

> Checks the real owned ConfirmStep source for confirmation summary, validation,

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
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Checks the real owned ConfirmStep source for confirmation summary, validation,
create button state, status rendering, source helpers, and compile/run health.

## Scenarios

### Claude full ConfirmStep component

#### models confirmation summary fields

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- models confirmation summary fields
- Read ConfirmStep source
- Assert summary model and renderer are present


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("models confirmation summary fields")
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

- models validation and create button enabled state
- Read ConfirmStep source
- Assert validation logic and button state are real


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("models validation and create button enabled state")
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

- models error and success statuses
- Read ConfirmStep source
- Assert status transitions and labels


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("models error and success statuses")
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

- exports source helpers and keeps the parity floor
- Read ConfirmStep source
- Assert helper names, line floor, and blocked stub markers
   - Expected: source does not contain `pass" + "_todo`
   - Expected: source does not contain `TO" + "DO`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("exports source helpers and keeps the parity floor")
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

- compiles the owned source file
- Run ConfirmStep through the interpreter
- Assert compile/run success
   - Expected: code equals `0`
   - Expected: stdout + stderr equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("compiles the owned source file")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `ea9a881a09cf479eaba5c53217025a85b66219056dbc9a70f3b6d10fb2a074a7`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ea9a881a09cf479eaba5c53217025a85b66219056dbc9a70f3b6d10fb2a074a7`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ea9a881a09cf479eaba5c53217025a85b66219056dbc9a70f3b6d10fb2a074a7`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **80/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/03_system/tools/llm/claude_full/components/agent_confirm_step_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/components/agent_confirm_step_spec.md (current)
findings: 7 blockers: 1
  narrative=100 structure=100 oracle=40
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=80; blocker cap makes effective=49
doc/06_spec/03_system/tools/llm/claude_full/components/agent_confirm_step_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/components/agent_confirm_step_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/components/agent_confirm_step_spec.spl:1:1: blocker SSDOC-ORA-002 [oracle] (-50): scenario relies on source-text inspection as system evidence
  why: Source presence or self-created arithmetic does not demonstrate production behavior.
  improve: Observe runtime behavior or a stable generated artifact instead.
test/03_system/tools/llm/claude_full/components/agent_confirm_step_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/tools/llm/claude_full/components/agent_confirm_step_spec.spl:30:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'models confirmation summary fields' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/components/agent_confirm_step_spec.spl:49:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'models validation and create button enabled state' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/components/agent_confirm_step_spec.spl:67:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'models error and success statuses' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
