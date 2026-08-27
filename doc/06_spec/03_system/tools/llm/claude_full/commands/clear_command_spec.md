# Claude Full Clear Command

> Mirrors `tmp/claude/claude-code-main/src/commands/clear` for clear command

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full Clear Command

Mirrors `tmp/claude/claude-code-main/src/commands/clear` for clear command

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/commands/clear_command_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Mirrors `tmp/claude/claude-code-main/src/commands/clear` for clear command
metadata-free call behavior, cache preservation, and conversation reset effects.

## Scenarios

### Claude full clear command

#### clears request-keyed caches only when no agents are preserved

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- clears request-keyed caches only when no agents are preserved
- Clear a plain session
   - Expected: plain.hasPreservedAgents is false
   - Expected: plain.resetPromptCacheBreakDetection is true
   - Expected: plain.clearedPendingCallbacks is true
   - Expected: plain.clearedDumpState is true
   - Expected: plain.memoryLoadReason equals `session_start`
- Preserve request-keyed state when background agents survive clear
   - Expected: preserved.hasPreservedAgents is true
   - Expected: preserved.resetPromptCacheBreakDetection is false
   - Expected: preserved.clearedPendingCallbacks is false
   - Expected: preserved.clearedDumpState is false
   - Expected: preserved.preservedAgentIds[0] equals `agent-1`
   - Expected: clearSessionCachesSourceLinesModeled() equals `144`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("clears request-keyed caches only when no agents are preserved")
step("Clear a plain session")
val plain = clearSessionCaches([])
expect(plain.hasPreservedAgents).to_equal(false)
expect(plain.resetPromptCacheBreakDetection).to_equal(true)
expect(plain.clearedPendingCallbacks).to_equal(true)
expect(plain.clearedDumpState).to_equal(true)
expect(plain.memoryLoadReason).to_equal("session_start")
expect(plain.clearedCacheNames).to_contain("commands")
expect(plain.asyncCacheNames).to_contain("web-fetch-url-cache")

step("Preserve request-keyed state when background agents survive clear")
val preserved = clearSessionCaches(["agent-1"])
expect(preserved.hasPreservedAgents).to_equal(true)
expect(preserved.resetPromptCacheBreakDetection).to_equal(false)
expect(preserved.clearedPendingCallbacks).to_equal(false)
expect(preserved.clearedDumpState).to_equal(false)
expect(preserved.preservedAgentIds[0]).to_equal("agent-1")
expect(clearSessionCachesSourceLinesModeled()).to_equal(144)
```

</details>

#### partitions foreground tasks from preserved agent tasks

- partitions foreground tasks from preserved agent tasks
- Clear messages, app state, cache state, ids, and hooks
   - Expected: result.messagesCleared is true
   - Expected: result.finalMessages[0] equals `hook-message`
   - Expected: result.contextBlockedReset is true
   - Expected: result.conversationIdRegenerated is true
   - Expected: result.cacheEvictionRequestId equals `req-1`
   - Expected: result.sessionIdRegenerated is true
   - Expected: result.envSessionIdUpdated is true
   - Expected: result.modePersisted equals `coordinator`
   - Expected: result.worktreeStateSaved equals `wt-1`
- Remove only foreground tasks and re-point running preserved local agents
   - Expected: result.killedTaskIds.len() equals `1`
   - Expected: result.killedTaskIds[0] equals `fg-shell`
   - Expected: result.taskOutputEvictions[0] equals `fg-shell`
   - Expected: result.preservedAgentIds.len() equals `4`
   - Expected: result.runningTaskOutputSymlinkIds.len() equals `2`
   - Expected: result.cacheResult.clearedPendingCallbacks is false
   - Expected: clearConversationSourceLinesModeled() equals `251`


<details>
<summary>Executable SSpec</summary>

Runnable source: 36 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("partitions foreground tasks from preserved agent tasks")
val tasks = [
    ClearTask.new("fg-shell", "local_shell", "", true, false, "running"),
    ClearTask.new("bg-agent", "local_agent", "agent-bg", true, true, "running"),
    ClearTask.new("main-agent", "local_agent", "agent-main", false, false, "running"),
    ClearTask.new("teammate", "in_process_teammate", "agent-team", true, true, "running"),
    ClearTask.new("done-agent", "local_agent", "agent-done", true, true, "done"),
]
val input = ClearConversationInput.new(2, tasks, true, false, true, true, "req-1", ["hook-message"], "wt-1", true, true, "ant", true)

step("Clear messages, app state, cache state, ids, and hooks")
val result = clearConversation(input)
expect(result.messagesCleared).to_equal(true)
expect(result.finalMessages[0]).to_equal("hook-message")
expect(result.contextBlockedReset).to_equal(true)
expect(result.conversationIdRegenerated).to_equal(true)
expect(result.cacheEvictionRequestId).to_equal("req-1")
expect(result.sessionIdRegenerated).to_equal(true)
expect(result.envSessionIdUpdated).to_equal(true)
expect(result.modePersisted).to_equal("coordinator")
expect(result.worktreeStateSaved).to_equal("wt-1")

step("Remove only foreground tasks and re-point running preserved local agents")
expect(result.killedTaskIds.len()).to_equal(1)
expect(result.killedTaskIds[0]).to_equal("fg-shell")
expect(result.taskOutputEvictions[0]).to_equal("fg-shell")
expect(result.preservedAgentIds.len()).to_equal(4)
expect(result.preservedAgentIds).to_contain("agent-bg")
expect(result.preservedAgentIds).to_contain("agent-main")
expect(result.preservedAgentIds).to_contain("agent-team")
expect(result.runningTaskOutputSymlinkIds.len()).to_equal(2)
expect(result.runningTaskOutputSymlinkIds).to_contain("bg-agent")
expect(result.runningTaskOutputSymlinkIds).to_contain("main-agent")
expect(result.cacheResult.clearedPendingCallbacks).to_equal(false)
expect(clearConversationSourceLinesModeled()).to_equal(251)
```

</details>

#### returns the clear command empty text result after clearing

- returns the clear command empty text result after clearing
   - Expected: result.typeName equals `text`
   - Expected: result.value equals ``
   - Expected: result.conversation.messagesCleared is true
   - Expected: result.conversation.finalMessages.len() equals `0`
   - Expected: clearCommandSourceLinesModeled() equals `7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("returns the clear command empty text result after clearing")
val input = ClearConversationInput.new(1, [], false, false, false, false, "", [], "", false, false, "", false)
val result = call(input)

expect(result.typeName).to_equal("text")
expect(result.value).to_equal("")
expect(result.conversation.messagesCleared).to_equal(true)
expect(result.conversation.finalMessages.len()).to_equal(0)
expect(clearCommandSourceLinesModeled()).to_equal(7)
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `ee3c2c5b61f1c51df599e20167c47f81ea65f2b6f01f3248fc8c490e6bf01c45`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ee3c2c5b61f1c51df599e20167c47f81ea65f2b6f01f3248fc8c490e6bf01c45`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ee3c2c5b61f1c51df599e20167c47f81ea65f2b6f01f3248fc8c490e6bf01c45`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/03_system/tools/llm/claude_full/commands/clear_command_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/commands/clear_command_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/commands/clear_command_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/commands/clear_command_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/commands/clear_command_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 7 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/tools/llm/claude_full/commands/clear_command_spec.spl:21:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'clears request-keyed caches only when no agents are preserved' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/commands/clear_command_spec.spl:43:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'partitions foreground tasks from preserved agent tasks' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/commands/clear_command_spec.spl:81:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns the clear command empty text result after clearing' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
