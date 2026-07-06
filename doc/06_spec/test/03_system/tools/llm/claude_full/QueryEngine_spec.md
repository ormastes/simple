# Claude Full QueryEngine

> Checks QueryEngine stateful SDK/headless query lifecycle parity.

<!-- sdn-diagram:id=QueryEngine_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=QueryEngine_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

QueryEngine_spec -> std
QueryEngine_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=QueryEngine_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full QueryEngine

Checks QueryEngine stateful SDK/headless query lifecycle parity.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/QueryEngine_spec.spl` |
| Updated | 2026-07-05 |
| Generator | `simple spipe-docgen` (Simple) |

Checks QueryEngine stateful SDK/headless query lifecycle parity.

## Scenarios

### Claude full QueryEngine

#### should initialize from config and preserve initial state

- Create QueryEngine
- var config = QueryEngineConfig new
   - Expected: engine.getMessages()[0] equals `previous`
   - Expected: engine.getReadFileState() equals `cache-a`
   - Expected: engine.getSessionId() equals `session_a`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

- Submit one prompt
   - Expected: messages.len() equals `3`
   - Expected: messages[0].type equals `user`
   - Expected: messages[0].uuid equals `u1`
   - Expected: messages[1].content equals `response:hello`
   - Expected: messages[2].type equals `result`
   - Expected: engine.getMessages().len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Submit one prompt")
val engine = QueryEngine.new(QueryEngineConfig.new("/repo", ["Read"]))
val messages = engine.submitMessage("hello", SubmitOptions.new("u1", false))
expect(messages.len()).to_equal(3)
expect(messages[0].type).to_equal("user")
expect(messages[0].uuid).to_equal("u1")
expect(messages[1].content).to_equal("response:hello")
expect(messages[2].type).to_equal("result")
expect(engine.getMessages().len()).to_equal(2)
```

</details>

#### should accumulate usage across turns

- Submit two prompts
- engine submitMessage
   - Expected: second[2].usageInputTokens equals `5`
   - Expected: second[2].usageOutputTokens equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Submit two prompts")
val engine = QueryEngine.new(QueryEngineConfig.new("/repo", ["Read"]))
engine.submitMessage("abc", SubmitOptions.new("", false))
val second = engine.submitMessage("de", SubmitOptions.new("", false))
expect(second[2].usageInputTokens).to_equal(5)
expect(second[2].usageOutputTokens).to_equal(2)
```

</details>

#### should track explicit and orphaned permission denials

- Record denials
- var config = QueryEngineConfig new
- engine denyPermission
   - Expected: messages[2].permissionDenials.len() equals `2`
   - Expected: messages[2].permissionDenials[0].toolName equals `read`
   - Expected: messages[2].permissionDenials[1].toolName equals `bash`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Record denials")
var config = QueryEngineConfig.new("/repo", ["Bash"])
config.orphanedPermission = "Bash"
val engine = QueryEngine.new(config)
engine.denyPermission("Read", "toolu_1", "{\"file\":\"a\"}")
val messages = engine.submitMessage("run", SubmitOptions.new("", false))
expect(messages[2].permissionDenials.len()).to_equal(2)
expect(messages[2].permissionDenials[0].toolName).to_equal("read")
expect(messages[2].permissionDenials[1].toolName).to_equal("bash")
```

</details>

#### should register structured output only when schema and tool exist

- Check structured output enforcement
- var config = QueryEngineConfig new
   - Expected: engine.structuredOutputRegistered is true
   - Expected: messages[2].structuredOutput equals `enforced`
   - Expected: hasStructuredOutputTool(["Read"]) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

- Abort and set model
- engine interrupt
- engine setModel
   - Expected: engine.abortController.aborted is true
   - Expected: engine.config.userSpecifiedModel equals `sonnet`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Abort and set model")
val engine = QueryEngine.new(QueryEngineConfig.new("/repo", ["Read"]))
engine.interrupt()
engine.setModel("sonnet")
expect(engine.abortController.aborted).to_equal(true)
expect(engine.config.userSpecifiedModel).to_equal("sonnet")
```

</details>

#### should ask as a one-shot QueryEngine wrapper

- Run ask wrapper
   - Expected: messages[0].content equals `once`
   - Expected: messages[2].content equals `response:once`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Run ask wrapper")
val messages = ask(QueryEngineConfig.new("/repo", ["Read"]), "once")
expect(messages[0].content).to_equal("once")
expect(messages[2].content).to_equal("response:once")
```

</details>

#### should expose source-backed helper surface

- Pin source helpers
   - Expected: sdkCompatToolName("Bash") equals `bash`
   - Expected: toolMatchesName("SyntheticOutputTool", "structured_output") is true
   - Expected: queryEngineSourceLinesModeled() equals `1295`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Pin source helpers")
expect(sdkCompatToolName("Bash")).to_equal("bash")
expect(toolMatchesName("SyntheticOutputTool", "structured_output")).to_equal(true)
expect(queryEngineSourceLinesModeled()).to_equal(1295)
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
