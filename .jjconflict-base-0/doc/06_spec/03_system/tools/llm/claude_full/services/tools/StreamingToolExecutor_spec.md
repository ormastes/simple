# Claude Full Streaming Tool Executor

> Purpose: should create completed error result for missing tools

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full Streaming Tool Executor

Purpose: should create completed error result for missing tools

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/services/tools/StreamingToolExecutor_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: should create completed error result for missing tools
Audience: compiler and tooling engineers who maintain this spec

# Claude Full Streaming Tool Executor

Checks streaming tool queueing, cancellation, progress, completion, and context behavior.

## Scenarios

### Claude full StreamingToolExecutor

#### should create completed error result for missing tools

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should create completed error result for missing tools
- Verify: should create completed error result for missing tools
- Add unknown tool
   - Expected: results[0].message.isError is true
   - Expected: executor.tools[0].status equals `yielded`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should create completed error result for missing tools")
step("Verify: should create completed error result for missing tools")
# @req: REQ-TOOLS-Stre-001
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

- should execute concurrency-safe tools and mark completion
- Verify: should execute concurrency-safe tools and mark completion
- Add safe tools
   - Expected: results.len() equals `2`
   - Expected: results[0].message.content equals `result:Read`
   - Expected: results[1].message.content equals `result:WebFetch`
   - Expected: executor.toolUseContext.completedToolUseIDs equals `["r1", "w1"]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should execute concurrency-safe tools and mark completion")
step("Verify: should execute concurrency-safe tools and mark completion")
# @req: REQ-TOOLS-Stre-001
step("Add safe tools")
val executor = StreamingToolExecutor.new(toolDefs(), ToolUseContextModel.new())
executor.addTool(ToolBlock.new("r1", "Read", ""), AssistantMessage.new("a1"))
executor.addTool(ToolBlock.new("w1", "WebFetch", ""), AssistantMessage.new("a1"))
val results = executor.getCompletedResults()
expect(results.len()).to_equal(2)  # oracle: value fixed by the spec contract
expect(results[0].message.content).to_equal("result:Read")
expect(results[1].message.content).to_equal("result:WebFetch")
expect(executor.toolUseContext.completedToolUseIDs).to_equal(["r1", "w1"])
```

</details>

#### should emit progress before final result

- should emit progress before final result
- Verify: should emit progress before final result
- Add progress-producing tool
   - Expected: results[0].message.type equals `progress`
   - Expected: results[0].message.content equals `progress:Read`
   - Expected: results[1].message.content equals `result:Read`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should emit progress before final result")
step("Verify: should emit progress before final result")
# @req: REQ-TOOLS-Stre-001
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

- should create streaming fallback errors when discarded
- Verify: should create streaming fallback errors when discarded
- Discard before running queued tool
   - Expected: executor.getCompletedResults().len() equals `0`
   - Expected: executor.discarded is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should create streaming fallback errors when discarded")
step("Verify: should create streaming fallback errors when discarded")
# @req: REQ-TOOLS-Stre-001
step("Discard before running queued tool")
val executor = StreamingToolExecutor.new(toolDefs(), ToolUseContextModel.new())
executor.discard()
executor.addTool(ToolBlock.new("r1", "Read", ""), AssistantMessage.new("a1"))
expect(executor.getCompletedResults().len()).to_equal(0)  # oracle: value fixed by the spec contract
expect(executor.discarded).to_equal(true)
```

</details>

#### should create user interruption errors only for cancel tools

- should create user interruption errors only for cancel tools
- Verify: should create user interruption errors only for cancel tools
- Abort with interrupt
   - Expected: results[0].message.content equals `User rejected tool use`
   - Expected: executor.tools[1].status equals `yielded`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should create user interruption errors only for cancel tools")
step("Verify: should create user interruption errors only for cancel tools")
# @req: REQ-TOOLS-Stre-001
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

- should cancel siblings after Bash error
- Verify: should cancel siblings after Bash error
- Run Bash error then sibling
   - Expected: results[0].message.isError is true
   - Expected: executor.hasErrored is true
   - Expected: executor.erroredToolDescription equals `Bash(ERROR)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should cancel siblings after Bash error")
step("Verify: should cancel siblings after Bash error")
# @req: REQ-TOOLS-Stre-001
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

- should apply context modifiers for non-concurrent tools
- Verify: should apply context modifiers for non-concurrent tools
- Run modifying Bash tool
   - Expected: executor.toolUseContext.modifierCount equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should apply context modifiers for non-concurrent tools")
step("Verify: should apply context modifiers for non-concurrent tools")
# @req: REQ-TOOLS-Stre-001
step("Run modifying Bash tool")
val executor = StreamingToolExecutor.new(toolDefs(), ToolUseContextModel.new())
executor.addTool(ToolBlock.new("b1", "Bash", "MODIFY"), AssistantMessage.new("a1"))
executor.getCompletedResults()
expect(executor.toolUseContext.modifierCount).to_equal(1)  # oracle: value fixed by the spec contract
```

</details>

#### should describe long tool inputs with truncation

- should describe long tool inputs with truncation
- Verify: should describe long tool inputs with truncation
- Describe tool


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should describe long tool inputs with truncation")
step("Verify: should describe long tool inputs with truncation")
# @req: REQ-TOOLS-Stre-001
step("Describe tool")
val executor = StreamingToolExecutor.new(toolDefs(), ToolUseContextModel.new())
val tool = TrackedTool.new(ToolBlock.new("b1", "Bash", "abcdefghijklmnopqrstuvwxyzabcdefghijklmnopqrstuvwxyz"), AssistantMessage.new("a1"), "queued", false)
expect(executor.getToolDescription(tool)).to_contain("abcdefghijklmnopqrstuvwxyzabcdefghijklmn…")
```

</details>

#### should expose remaining-results and helper surface

- should expose remaining-results and helper surface
- Verify: should expose remaining-results and helper surface
- Drain remaining results
   - Expected: executor.hasCompletedResults() is true
   - Expected: executor.hasUnfinishedTools() is true
   - Expected: remaining[0].message.content equals `result:Read`
   - Expected: executor.getUpdatedContext().completedToolUseIDs equals `["r1"]`
   - Expected: streamingToolExecutorSourceLinesModeled() equals `530`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should expose remaining-results and helper surface")
step("Verify: should expose remaining-results and helper surface")
# @req: REQ-TOOLS-Stre-001
step("Drain remaining results")
val executor = StreamingToolExecutor.new(toolDefs(), ToolUseContextModel.new())
executor.addTool(ToolBlock.new("r1", "Read", ""), AssistantMessage.new("a1"))
expect(executor.hasCompletedResults()).to_equal(true)
expect(executor.hasUnfinishedTools()).to_equal(true)
val remaining = executor.getRemainingResults()
expect(remaining[0].message.content).to_equal("result:Read")
expect(executor.getUpdatedContext().completedToolUseIDs).to_equal(["r1"])
expect(streamingToolExecutorSourceLinesModeled()).to_equal(530)  # oracle: value fixed by the spec contract
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
- `REQ-TOOLS-Stre-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `1b0453394e032f964f7fe03ba7f6030f031b4ea20f92171470d4888d69b8e71c`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `1b0453394e032f964f7fe03ba7f6030f031b4ea20f92171470d4888d69b8e71c`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `1b0453394e032f964f7fe03ba7f6030f031b4ea20f92171470d4888d69b8e71c`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/03_system/tools/llm/claude_full/services/tools/StreamingToolExecutor_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/services/tools/StreamingToolExecutor_spec.md (current)
findings: 11 blockers: 0
  narrative=100 structure=70 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/services/tools/StreamingToolExecutor_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/services/tools/StreamingToolExecutor_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/services/tools/StreamingToolExecutor_spec.spl:32:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should create completed error result for missing tools' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/services/tools/StreamingToolExecutor_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should create completed error result for missing tools' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/services/tools/StreamingToolExecutor_spec.spl:45:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should execute concurrency-safe tools and mark completion' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/services/tools/StreamingToolExecutor_spec.spl:45:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should execute concurrency-safe tools and mark completion' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/services/tools/StreamingToolExecutor_spec.spl:60:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should emit progress before final result' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/services/tools/StreamingToolExecutor_spec.spl:60:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should emit progress before final result' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/services/tools/StreamingToolExecutor_spec.spl:73:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should create streaming fallback errors when discarded' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/services/tools/StreamingToolExecutor_spec.spl:85:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should create user interruption errors only for cancel tools' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/services/tools/StreamingToolExecutor_spec.spl:100:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should cancel siblings after Bash error' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
