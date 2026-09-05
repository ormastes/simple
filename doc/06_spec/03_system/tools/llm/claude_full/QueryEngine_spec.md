# Claude Full QueryEngine

> Purpose: should initialize from config and preserve initial state

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full QueryEngine

Purpose: should initialize from config and preserve initial state

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/QueryEngine_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: should initialize from config and preserve initial state
Audience: compiler and tooling engineers who maintain this spec

# Claude Full QueryEngine

Checks QueryEngine stateful SDK/headless query lifecycle parity.

## Scenarios

### Claude full QueryEngine

#### should initialize from config and preserve initial state

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should initialize from config and preserve initial state
- Verify: should initialize from config and preserve initial state
- Create QueryEngine
   - Expected: engine.getMessages()[0] equals `previous`
   - Expected: engine.getReadFileState() equals `cache-a`
   - Expected: engine.getSessionId() equals `session_a`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should initialize from config and preserve initial state")
step("Verify: should initialize from config and preserve initial state")
# @req: REQ-TOOLS-Quer-001
step("Create QueryEngine")
var config = QueryEngineConfig.new("/repo", ["Read"])
config.initialMessages = ["previous"]
config.readFileCache = "cache-a"
config.sessionId = "session_a"
val engine = QueryEngine.new(config)
expect(engine.getMessages()[0]).to_equal("previous")
expect(engine.getReadFileState()).to_equal("cache-a")
expect(engine.getSessionId()).to_equal("session_a")
```

</details>

#### should submit a prompt and emit user assistant result messages

- should submit a prompt and emit user assistant result messages
- Verify: should submit a prompt and emit user assistant result messages
- Submit one prompt
   - Expected: messages.len() equals `3`
   - Expected: messages[0].type equals `user`
   - Expected: messages[0].uuid equals `u1`
   - Expected: messages[1].content equals `response:hello`
   - Expected: messages[2].type equals `result`
   - Expected: engine.getMessages().len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should submit a prompt and emit user assistant result messages")
step("Verify: should submit a prompt and emit user assistant result messages")
# @req: REQ-TOOLS-Quer-001
step("Submit one prompt")
val engine = QueryEngine.new(QueryEngineConfig.new("/repo", ["Read"]))
val messages = engine.submitMessage("hello", SubmitOptions.new("u1", false))
expect(messages.len()).to_equal(3)  # oracle: value fixed by the spec contract
expect(messages[0].type).to_equal("user")
expect(messages[0].uuid).to_equal("u1")
expect(messages[1].content).to_equal("response:hello")
expect(messages[2].type).to_equal("result")
expect(engine.getMessages().len()).to_equal(2)  # oracle: value fixed by the spec contract
```

</details>

#### should accumulate usage across turns

- should accumulate usage across turns
- Verify: should accumulate usage across turns
- Submit two prompts
   - Expected: second[2].usageInputTokens equals `5`
   - Expected: second[2].usageOutputTokens equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should accumulate usage across turns")
step("Verify: should accumulate usage across turns")
# @req: REQ-TOOLS-Quer-001
step("Submit two prompts")
val engine = QueryEngine.new(QueryEngineConfig.new("/repo", ["Read"]))
engine.submitMessage("abc", SubmitOptions.new("", false))
val second = engine.submitMessage("de", SubmitOptions.new("", false))
expect(second[2].usageInputTokens).to_equal(5)  # oracle: value fixed by the spec contract
expect(second[2].usageOutputTokens).to_equal(2)  # oracle: value fixed by the spec contract
```

</details>

#### should track explicit and orphaned permission denials

- should track explicit and orphaned permission denials
- Verify: should track explicit and orphaned permission denials
- Record denials
   - Expected: messages[2].permissionDenials.len() equals `2`
   - Expected: messages[2].permissionDenials[0].toolName equals `read`
   - Expected: messages[2].permissionDenials[1].toolName equals `bash`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should track explicit and orphaned permission denials")
step("Verify: should track explicit and orphaned permission denials")
# @req: REQ-TOOLS-Quer-001
step("Record denials")
var config = QueryEngineConfig.new("/repo", ["Bash"])
config.orphanedPermission = "Bash"
val engine = QueryEngine.new(config)
engine.denyPermission("Read", "toolu_1", "{\"file\":\"a\"}")
val messages = engine.submitMessage("run", SubmitOptions.new("", false))
expect(messages[2].permissionDenials.len()).to_equal(2)  # oracle: value fixed by the spec contract
expect(messages[2].permissionDenials[0].toolName).to_equal("read")
expect(messages[2].permissionDenials[1].toolName).to_equal("bash")
```

</details>

#### should register structured output only when schema and tool exist

- should register structured output only when schema and tool exist
- Verify: should register structured output only when schema and tool exist
- Check structured output enforcement
   - Expected: engine.structuredOutputRegistered is true
   - Expected: messages[2].structuredOutput equals `enforced`
   - Expected: hasStructuredOutputTool(["Read"]) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should register structured output only when schema and tool exist")
step("Verify: should register structured output only when schema and tool exist")
# @req: REQ-TOOLS-Quer-001
step("Check structured output enforcement")
var config = QueryEngineConfig.new("/repo", ["SyntheticOutputTool"])
config.jsonSchema = "{\"type\":\"object\"}"
val engine = QueryEngine.new(config)
val messages = engine.submitMessage("json", SubmitOptions.new("", false))
expect(engine.structuredOutputRegistered).to_equal(true)
expect(messages[2].structuredOutput).to_equal("enforced")
expect(hasStructuredOutputTool(["Read"])).to_equal(false)
```

</details>

#### should interrupt and update model

- should interrupt and update model
- Verify: should interrupt and update model
- Abort and set model
   - Expected: engine.abortController.aborted is true
   - Expected: engine.config.userSpecifiedModel equals `sonnet`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should interrupt and update model")
step("Verify: should interrupt and update model")
# @req: REQ-TOOLS-Quer-001
step("Abort and set model")
val engine = QueryEngine.new(QueryEngineConfig.new("/repo", ["Read"]))
engine.interrupt()
engine.setModel("sonnet")
expect(engine.abortController.aborted).to_equal(true)
expect(engine.config.userSpecifiedModel).to_equal("sonnet")
```

</details>

#### should ask as a one-shot QueryEngine wrapper

- should ask as a one-shot QueryEngine wrapper
- Verify: should ask as a one-shot QueryEngine wrapper
- Run ask wrapper
   - Expected: messages[0].content equals `once`
   - Expected: messages[2].content equals `response:once`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should ask as a one-shot QueryEngine wrapper")
step("Verify: should ask as a one-shot QueryEngine wrapper")
# @req: REQ-TOOLS-Quer-001
step("Run ask wrapper")
val messages = ask(QueryEngineConfig.new("/repo", ["Read"]), "once")
expect(messages[0].content).to_equal("once")
expect(messages[2].content).to_equal("response:once")
```

</details>

#### should expose source-backed helper surface

- should expose source-backed helper surface
- Verify: should expose source-backed helper surface
- Pin source helpers
   - Expected: sdkCompatToolName("Bash") equals `bash`
   - Expected: toolMatchesName("SyntheticOutputTool", "structured_output") is true
   - Expected: queryEngineSourceLinesModeled() equals `1295`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should expose source-backed helper surface")
step("Verify: should expose source-backed helper surface")
# @req: REQ-TOOLS-Quer-001
step("Pin source helpers")
expect(sdkCompatToolName("Bash")).to_equal("bash")
expect(toolMatchesName("SyntheticOutputTool", "structured_output")).to_equal(true)
expect(queryEngineSourceLinesModeled()).to_equal(1295)  # oracle: value fixed by the spec contract
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
- `REQ-TOOLS-Quer-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `65853bb645e38461341aa5914f5f1fdc83e0ce44cb156b352bcbdfcb6ce33917`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `65853bb645e38461341aa5914f5f1fdc83e0ce44cb156b352bcbdfcb6ce33917`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `65853bb645e38461341aa5914f5f1fdc83e0ce44cb156b352bcbdfcb6ce33917`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/03_system/tools/llm/claude_full/QueryEngine_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/QueryEngine_spec.md (current)
findings: 11 blockers: 0
  narrative=100 structure=70 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/QueryEngine_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/QueryEngine_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/QueryEngine_spec.spl:24:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should initialize from config and preserve initial state' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/QueryEngine_spec.spl:24:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should initialize from config and preserve initial state' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/QueryEngine_spec.spl:39:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should submit a prompt and emit user assistant result messages' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/QueryEngine_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should submit a prompt and emit user assistant result messages' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/QueryEngine_spec.spl:54:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should accumulate usage across turns' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/QueryEngine_spec.spl:54:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should accumulate usage across turns' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/QueryEngine_spec.spl:66:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should track explicit and orphaned permission denials' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/QueryEngine_spec.spl:81:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should register structured output only when schema and tool exist' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/QueryEngine_spec.spl:95:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should interrupt and update model' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
