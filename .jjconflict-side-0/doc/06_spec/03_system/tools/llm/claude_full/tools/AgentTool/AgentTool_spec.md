# Claude Full AgentTool Slice

> Focused Simple/TUI-compatible coverage for AgentTool public contract helpers

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full AgentTool Slice

Focused Simple/TUI-compatible coverage for AgentTool public contract helpers

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/tools/AgentTool/AgentTool_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Focused Simple/TUI-compatible coverage for AgentTool public contract helpers
from tools/AgentTool/AgentTool.tsx.

## Scenarios

### Claude full AgentTool parity

#### should model constants and labels

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should model constants and labels
- Check names
   - Expected: AGENT_TOOL_NAME equals `Agent`
   - Expected: LEGACY_AGENT_TOOL_NAME equals `Task`
   - Expected: userFacingNameRoute("") equals `Agent`
   - Expected: userFacingNameRoute("worker") equals `Agent`
   - Expected: userFacingNameRoute("plan") equals `plan`
   - Expected: userFacingNameBackgroundColorRoute("") equals `nil`
   - Expected: userFacingNameBackgroundColorRoute("verification") equals `blue`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should model constants and labels")
step("Check names")
expect(AGENT_TOOL_NAME).to_equal("Agent")
expect(LEGACY_AGENT_TOOL_NAME).to_equal("Task")
expect(userFacingNameRoute("")).to_equal("Agent")
expect(userFacingNameRoute("worker")).to_equal("Agent")
expect(userFacingNameRoute("plan")).to_equal("plan")
expect(userFacingNameBackgroundColorRoute("")).to_equal("nil")
expect(userFacingNameBackgroundColorRoute("verification")).to_equal("blue")
```

</details>

#### should model output status and result rendering

- should model output status and result rendering
- Check output summaries
   - Expected: outputSchemaAcceptsRoute("completed") is true
   - Expected: outputSchemaAcceptsRoute("async_launched") is true
   - Expected: outputSchemaAcceptsRoute("remote_launched") is true
   - Expected: outputSchemaAcceptsRoute("unknown") is false
   - Expected: renderAgentResultRoute("remote_launched", "t1", "https://session", "desc", "prompt", "out.txt", 0, 0, 0) equals `Remote agent launched t1 https://session desc prompt out.txt`
   - Expected: renderAgentResultRoute("async_launched", "", "", "", "prompt", "", 0, 0, 0) equals `Backgrounded agent prompt`
   - Expected: renderAgentResultRoute("completed", "", "", "", "", "", 3, 42, 1000) equals `Done (3 tool uses · 42 tokens · 1000 ms)`
   - Expected: renderAgentResultRoute("rejected", "", "", "", "", "", 0, 0, 0) equals `Agent rejected`
   - Expected: renderAgentResultRoute("error", "", "", "", "", "", 0, 0, 0) equals `Agent error`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should model output status and result rendering")
step("Check output summaries")
expect(outputSchemaAcceptsRoute("completed")).to_equal(true)
expect(outputSchemaAcceptsRoute("async_launched")).to_equal(true)
expect(outputSchemaAcceptsRoute("remote_launched")).to_equal(true)
expect(outputSchemaAcceptsRoute("unknown")).to_equal(false)
expect(renderAgentResultRoute("remote_launched", "t1", "https://session", "desc", "prompt", "out.txt", 0, 0, 0)).to_equal("Remote agent launched t1 https://session desc prompt out.txt")
expect(renderAgentResultRoute("async_launched", "", "", "", "prompt", "", 0, 0, 0)).to_equal("Backgrounded agent prompt")
expect(renderAgentResultRoute("completed", "", "", "", "", "", 3, 42, 1000)).to_equal("Done (3 tool uses · 42 tokens · 1000 ms)")
expect(renderAgentResultRoute("rejected", "", "", "", "", "", 0, 0, 0)).to_equal("Agent rejected")
expect(renderAgentResultRoute("error", "", "", "", "", "", 0, 0, 0)).to_equal("Agent error")
```

</details>

#### should model tool use tags and grouped progress

- should model tool use tags and grouped progress
- Check TUI helper routes
   - Expected: renderToolUseRoute("", "prompt") equals `nil`
   - Expected: renderToolUseRoute("desc", "") equals `nil`
   - Expected: renderToolUseTagRoute("sonnet", "haiku") equals `haiku`
   - Expected: renderToolUseTagRoute("sonnet", "sonnet") equals `nil`
   - Expected: progressSummaryRoute(true) equals `initializing`
   - Expected: groupedUseRoute(true) equals `background agents launched`
   - Expected: agentToolSourceLinesModeled() equals `1397`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should model tool use tags and grouped progress")
step("Check TUI helper routes")
expect(renderToolUseRoute("", "prompt")).to_equal("nil")
expect(renderToolUseRoute("desc", "")).to_equal("nil")
expect(renderToolUseTagRoute("sonnet", "haiku")).to_equal("haiku")
expect(renderToolUseTagRoute("sonnet", "sonnet")).to_equal("nil")
expect(progressSummaryRoute(true)).to_equal("initializing")
expect(groupedUseRoute(true)).to_equal("background agents launched")
expect(agentToolSourceLinesModeled()).to_equal(1397)
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

- Canonical SPipe generation for source `ca712ea19ffd9e931c7ecd6715464aefd1b7a10cfcd7fb5e87a9fc2367ddc0c3`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ca712ea19ffd9e931c7ecd6715464aefd1b7a10cfcd7fb5e87a9fc2367ddc0c3`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ca712ea19ffd9e931c7ecd6715464aefd1b7a10cfcd7fb5e87a9fc2367ddc0c3`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/03_system/tools/llm/claude_full/tools/AgentTool/AgentTool_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/tools/AgentTool/AgentTool_spec.md (current)
findings: 9 blockers: 0
  narrative=100 structure=85 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/tools/AgentTool/AgentTool_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/tools/AgentTool/AgentTool_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/tools/AgentTool/AgentTool_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/tools/llm/claude_full/tools/AgentTool/AgentTool_spec.spl:19:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should model constants and labels' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/tools/AgentTool/AgentTool_spec.spl:19:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should model constants and labels' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/tools/AgentTool/AgentTool_spec.spl:31:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should model output status and result rendering' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/tools/AgentTool/AgentTool_spec.spl:31:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should model output status and result rendering' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/tools/AgentTool/AgentTool_spec.spl:45:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should model tool use tags and grouped progress' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/tools/AgentTool/AgentTool_spec.spl:45:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should model tool use tags and grouped progress' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
