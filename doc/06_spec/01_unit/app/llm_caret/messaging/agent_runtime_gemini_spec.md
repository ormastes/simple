# Agent Runtime Gemini Specification

> Tests covering LLM Caret agent runtime provider commands.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Agent Runtime Gemini Specification

## Scenarios

### LLM Caret agent runtime provider commands

#### selects Gemini CLI as a first-class agent runtime

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- selects Gemini CLI as a first-class agent runtime
   - Expected: agent_command_for_provider_with_gemini("gemini", "", "", "", "") equals `gemini`
   - Expected: agent_command_for_provider_with_gemini("gemini_cli", "", "", "gemini-dev", "") equals `gemini-dev`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("selects Gemini CLI as a first-class agent runtime")
expect(agent_command_for_provider_with_gemini("gemini", "", "", "", "")).to_equal("gemini")
expect(agent_command_for_provider_with_gemini("gemini_cli", "", "", "gemini-dev", "")).to_equal("gemini-dev")
```

</details>

#### preserves explicit Claude Codex and OpenCode paths

- preserves explicit Claude Codex and OpenCode paths
   - Expected: agent_command_for_provider_with_gemini("claude_cli", "claude-dev", "", "", "") equals `claude-dev`
   - Expected: agent_command_for_provider_with_gemini("codex", "", "codex-dev", "", "") equals `codex-dev`
   - Expected: agent_command_for_provider_with_gemini("opencode_cli", "", "", "", "opencode-dev") equals `opencode-dev`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("preserves explicit Claude Codex and OpenCode paths")
expect(agent_command_for_provider_with_gemini("claude_cli", "claude-dev", "", "", "")).to_equal("claude-dev")
expect(agent_command_for_provider_with_gemini("codex", "", "codex-dev", "", "")).to_equal("codex-dev")
expect(agent_command_for_provider_with_gemini("opencode_cli", "", "", "", "opencode-dev")).to_equal("opencode-dev")
```

</details>

#### builds a narrowly scoped hook-correlation environment

- builds a narrowly scoped hook-correlation environment
   - Expected: env["LLM_CARET_TASK_ID"] equals `task-1`
   - Expected: env["LLM_CARET_ROOM_ID"] equals `room-1`
   - Expected: env["LLM_CARET_AGENT_ID"] equals `gemini-agent`
   - Expected: env["LLM_CARET_MESSAGING_DB"] equals `.simple/state/messages.db`
   - Expected: env.has("SLACK_TOKEN") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("builds a narrowly scoped hook-correlation environment")
val env = messaging_agent_environment(MessagingAgentLaunchContext(
    task_id: "task-1", room_id: "room-1", agent_id: "gemini-agent",
    database_path: ".simple/state/messages.db"))
expect(env["LLM_CARET_TASK_ID"]).to_equal("task-1")
expect(env["LLM_CARET_ROOM_ID"]).to_equal("room-1")
expect(env["LLM_CARET_AGENT_ID"]).to_equal("gemini-agent")
expect(env["LLM_CARET_MESSAGING_DB"]).to_equal(".simple/state/messages.db")
expect(env.has("SLACK_TOKEN")).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/llm_caret/messaging/agent_runtime_gemini_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering LLM Caret agent runtime provider commands.
- LLM Caret agent runtime provider commands

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

- `REQ-SSPEC-UNIT`
- `REQ-LLM-MSG-006`
- `REQ-LLM-MSG-013`
- `REQ-SSPEC-APP`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `54d0c2f08e740d137db878b3ef764538a423c3e88c36f8c85ff770c92e81e6e4`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `54d0c2f08e740d137db878b3ef764538a423c3e88c36f8c85ff770c92e81e6e4`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `54d0c2f08e740d137db878b3ef764538a423c3e88c36f8c85ff770c92e81e6e4`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/app/llm_caret/messaging/agent_runtime_gemini_spec.spl
mirror: doc/06_spec/01_unit/app/llm_caret/messaging/agent_runtime_gemini_spec.md (current)
findings: 6 blockers: 1
  narrative=100 structure=100 oracle=100
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=86; blocker cap makes effective=49
doc/06_spec/01_unit/app/llm_caret/messaging/agent_runtime_gemini_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/llm_caret/messaging/agent_runtime_gemini_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/llm_caret/messaging/agent_runtime_gemini_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 3 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/app/llm_caret/messaging/agent_runtime_gemini_spec.spl:19:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'selects Gemini CLI as a first-class agent runtime' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/llm_caret/messaging/agent_runtime_gemini_spec.spl:25:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'preserves explicit Claude Codex and OpenCode paths' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/llm_caret/messaging/agent_runtime_gemini_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'builds a narrowly scoped hook-correlation environment' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
