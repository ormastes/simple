# Claude Full Streaming Tool Executor

> Checks streaming tool queueing, cancellation, progress, completion, and context behavior.

<!-- sdn-diagram:id=StreamingToolExecutor_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=StreamingToolExecutor_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

StreamingToolExecutor_spec -> std
StreamingToolExecutor_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=StreamingToolExecutor_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full Streaming Tool Executor

Checks streaming tool queueing, cancellation, progress, completion, and context behavior.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/services/tools/StreamingToolExecutor_spec.spl` |
| Updated | 2026-07-05 |
| Generator | `simple spipe-docgen` (Simple) |

Checks streaming tool queueing, cancellation, progress, completion, and context behavior.

## Scenarios

### Claude full StreamingToolExecutor

#### should create completed error result for missing tools

- Add unknown tool
- executor addTool
   - Expected: results[0].message.isError is true
   - Expected: executor.tools[0].status equals `yielded`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Add unknown tool")
val executor = StreamingToolExecutor.new(toolDefs(), ToolUseContextModel.new())
executor.addTool(ToolBlock.new("t1", "Missing", ""), AssistantMessage.new("a1"))
val results = executor.getCompletedResults()
expect(results[0].message.isError).to_equal(true)
expect(results[0].message.content).to_contain("No such tool available")
expect(executor.tools[0].status).to_equal("yielded")
```

</details>

#### should execute concurrency-safe tools and mark completion

- Add safe tools
- executor addTool
- executor addTool
   - Expected: results.len() equals `2`
   - Expected: results[0].message.content equals `result:Read`
   - Expected: results[1].message.content equals `result:WebFetch`
   - Expected: executor.toolUseContext.completedToolUseIDs equals `["r1", "w1"]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Add safe tools")
val executor = StreamingToolExecutor.new(toolDefs(), ToolUseContextModel.new())
executor.addTool(ToolBlock.new("r1", "Read", ""), AssistantMessage.new("a1"))
executor.addTool(ToolBlock.new("w1", "WebFetch", ""), AssistantMessage.new("a1"))
val results = executor.getCompletedResults()
expect(results.len()).to_equal(2)
expect(results[0].message.content).to_equal("result:Read")
expect(results[1].message.content).to_equal("result:WebFetch")
expect(executor.toolUseContext.completedToolUseIDs).to_equal(["r1", "w1"])
```

</details>

#### should emit progress before final result

- Add progress-producing tool
- executor addTool
   - Expected: results[0].message.type equals `progress`
   - Expected: results[0].message.content equals `progress:Read`
   - Expected: results[1].message.content equals `result:Read`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Add progress-producing tool")
val executor = StreamingToolExecutor.new(toolDefs(), ToolUseContextModel.new())
executor.addTool(ToolBlock.new("r1", "Read", "PROGRESS"), AssistantMessage.new("a1"))
val results = executor.getCompletedResults()
expect(results[0].message.type).to_equal("progress")
expect(results[0].message.content).to_equal("progress:Read")
expect(results[1].message.content).to_equal("result:Read")
```

</details>

#### should create streaming fallback errors when discarded

- Discard before running queued tool
- executor discard
- executor addTool
   - Expected: executor.getCompletedResults().len() equals `0`
   - Expected: executor.discarded is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Discard before running queued tool")
val executor = StreamingToolExecutor.new(toolDefs(), ToolUseContextModel.new())
executor.discard()
executor.addTool(ToolBlock.new("r1", "Read", ""), AssistantMessage.new("a1"))
expect(executor.getCompletedResults().len()).to_equal(0)
expect(executor.discarded).to_equal(true)
```

</details>

#### should create user interruption errors only for cancel tools

- Abort with interrupt
- executor addTool
- executor addTool
   - Expected: results[0].message.content equals `User rejected tool use`
   - Expected: executor.tools[1].status equals `yielded`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Abort with interrupt")
val context = ToolUseContextModel.new()
context.abortReason = "interrupt"
val executor = StreamingToolExecutor.new(toolDefs(), context)
executor.addTool(ToolBlock.new("r1", "Read", ""), AssistantMessage.new("a1"))
executor.addTool(ToolBlock.new("e1", "Edit", ""), AssistantMessage.new("a1"))
val results = executor.getCompletedResults()
expect(results[0].message.content).to_equal("User rejected tool use")
expect(executor.tools[1].status).to_equal("yielded")
```

</details>

#### should cancel siblings after Bash error

- Run Bash error then sibling
- executor addTool
- executor addTool
   - Expected: results[0].message.isError is true
   - Expected: executor.hasErrored is true
   - Expected: executor.erroredToolDescription equals `Bash(ERROR)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Run Bash error then sibling")
val executor = StreamingToolExecutor.new(toolDefs(), ToolUseContextModel.new())
executor.addTool(ToolBlock.new("b1", "Bash", "ERROR"), AssistantMessage.new("a1"))
executor.addTool(ToolBlock.new("r1", "Read", ""), AssistantMessage.new("a1"))
val results = executor.getCompletedResults()
expect(results[0].message.isError).to_equal(true)
expect(executor.hasErrored).to_equal(true)
expect(executor.erroredToolDescription).to_equal("Bash(ERROR)")
```

</details>

#### should apply context modifiers for non-concurrent tools

- Run modifying Bash tool
- executor addTool
- executor getCompletedResults
   - Expected: executor.toolUseContext.modifierCount equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Run modifying Bash tool")
val executor = StreamingToolExecutor.new(toolDefs(), ToolUseContextModel.new())
executor.addTool(ToolBlock.new("b1", "Bash", "MODIFY"), AssistantMessage.new("a1"))
executor.getCompletedResults()
expect(executor.toolUseContext.modifierCount).to_equal(1)
```

</details>

#### should describe long tool inputs with truncation

- Describe tool


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Describe tool")
val executor = StreamingToolExecutor.new(toolDefs(), ToolUseContextModel.new())
val tool = TrackedTool.new(ToolBlock.new("b1", "Bash", "abcdefghijklmnopqrstuvwxyzabcdefghijklmnopqrstuvwxyz"), AssistantMessage.new("a1"), "queued", false)
expect(executor.getToolDescription(tool)).to_contain("abcdefghijklmnopqrstuvwxyzabcdefghijklmn…")
```

</details>

#### should expose remaining-results and helper surface

- Drain remaining results
- executor addTool
   - Expected: executor.hasCompletedResults() is true
   - Expected: executor.hasUnfinishedTools() is true
   - Expected: remaining[0].message.content equals `result:Read`
   - Expected: executor.getUpdatedContext().completedToolUseIDs equals `["r1"]`
   - Expected: streamingToolExecutorSourceLinesModeled() equals `530`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Drain remaining results")
val executor = StreamingToolExecutor.new(toolDefs(), ToolUseContextModel.new())
executor.addTool(ToolBlock.new("r1", "Read", ""), AssistantMessage.new("a1"))
expect(executor.hasCompletedResults()).to_equal(true)
expect(executor.hasUnfinishedTools()).to_equal(true)
val remaining = executor.getRemainingResults()
expect(remaining[0].message.content).to_equal("result:Read")
expect(executor.getUpdatedContext().completedToolUseIDs).to_equal(["r1"])
expect(streamingToolExecutorSourceLinesModeled()).to_equal(530)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
