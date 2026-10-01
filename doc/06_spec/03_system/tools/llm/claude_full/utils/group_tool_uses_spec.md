# Claude Full grouped tool uses

> Pure Simple coverage for grouped tool-use rendering decisions.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full grouped tool uses

Pure Simple coverage for grouped tool-use rendering decisions.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/utils/group_tool_uses_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Pure Simple coverage for grouped tool-use rendering decisions.

## Scenarios

### Claude full grouped tool uses

#### returns original message order in verbose mode

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- returns original message order in verbose mode
- Check verbose bypass
   - Expected: result.renderUuids equals `["a1", "a2"]`
   - Expected: result.groups.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("returns original message order in verbose mode")
step("Check verbose bypass")
val result = applyToolUseGrouping([assistantTool("a1", "m1", "u1", "Read"), assistantTool("a2", "m1", "u2", "Read")], ["Read"], true)
expect(result.renderUuids).to_equal(["a1", "a2"])
expect(result.groups.len()).to_equal(0)
```

</details>

#### groups two supported tool uses from the same assistant message

- groups two supported tool uses from the same assistant message
- Check grouped assistant tools
   - Expected: result.renderUuids equals `["grouped-a1"]`
   - Expected: result.renderTypes equals `["grouped_tool_use"]`
   - Expected: result.groups.len() equals `1`
   - Expected: result.groups[0].uuid equals `grouped-a1`
   - Expected: result.groups[0].messageIds equals `["a1", "a2"]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("groups two supported tool uses from the same assistant message")
step("Check grouped assistant tools")
val result = applyToolUseGrouping([assistantTool("a1", "m1", "u1", "Read"), assistantTool("a2", "m1", "u2", "Read")], ["Read"], false)
expect(result.renderUuids).to_equal(["grouped-a1"])
expect(result.renderTypes).to_equal(["grouped_tool_use"])
expect(result.groups.len()).to_equal(1)
expect(result.groups[0].uuid).to_equal("grouped-a1")
expect(result.groups[0].messageIds).to_equal(["a1", "a2"])
```

</details>

#### does not group a single tool use or unsupported tool

- does not group a single tool use or unsupported tool
- Check unsupported and singleton
   - Expected: result.renderUuids equals `["a1", "b1", "b2"]`
   - Expected: result.groups.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("does not group a single tool use or unsupported tool")
step("Check unsupported and singleton")
val result = applyToolUseGrouping([assistantTool("a1", "m1", "u1", "Read"), assistantTool("b1", "m2", "u2", "Write"), assistantTool("b2", "m2", "u3", "Write")], ["Read"], false)
expect(result.renderUuids).to_equal(["a1", "b1", "b2"])
expect(result.groups.len()).to_equal(0)
```

</details>

#### does not group the same tool name across different assistant messages

- does not group the same tool name across different assistant messages
- Check message id boundary
   - Expected: result.renderUuids equals `["a1", "a2"]`
   - Expected: result.groups.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("does not group the same tool name across different assistant messages")
step("Check message id boundary")
val result = applyToolUseGrouping([assistantTool("a1", "m1", "u1", "Read"), assistantTool("a2", "m2", "u2", "Read")], ["Read"], false)
expect(result.renderUuids).to_equal(["a1", "a2"])
expect(result.groups.len()).to_equal(0)
```

</details>

#### attaches matching results and skips grouped result-only user messages

- attaches matching results and skips grouped result-only user messages
- Check grouped results
   - Expected: result.renderUuids equals `["grouped-a1"]`
   - Expected: result.groups[0].resultIds equals `["r1", "r2"]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("attaches matching results and skips grouped result-only user messages")
step("Check grouped results")
val result = applyToolUseGrouping([assistantTool("a1", "m1", "u1", "Read"), assistantTool("a2", "m1", "u2", "Read"), userResult("r1", ["u1"]), userResult("r2", ["u2"])], ["Read"], false)
expect(result.renderUuids).to_equal(["grouped-a1"])
expect(result.groups[0].resultIds).to_equal(["r1", "r2"])
```

</details>

#### keeps mixed user result messages that include ungrouped results

- keeps mixed user result messages that include ungrouped results
- Check mixed user result
   - Expected: result.renderUuids equals `["grouped-a1", "r1"]`
   - Expected: result.groups[0].resultIds equals `["r1"]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("keeps mixed user result messages that include ungrouped results")
step("Check mixed user result")
val result = applyToolUseGrouping([assistantTool("a1", "m1", "u1", "Read"), assistantTool("a2", "m1", "u2", "Read"), userResult("r1", ["u1", "other"])], ["Read"], false)
expect(result.renderUuids).to_equal(["grouped-a1", "r1"])
expect(result.groups[0].resultIds).to_equal(["r1"])
```

</details>

#### emits grouped messages at their first assistant position

- emits grouped messages at their first assistant position
- Check ordered render stream
   - Expected: result.renderUuids equals `["before", "grouped-a1", "after"]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("emits grouped messages at their first assistant position")
step("Check ordered render stream")
val result = applyToolUseGrouping([textMessage("before"), assistantTool("a1", "m1", "u1", "Read"), assistantTool("a2", "m1", "u2", "Read"), textMessage("after")], ["Read"], false)
expect(result.renderUuids).to_equal(["before", "grouped-a1", "after"])
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
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

- Canonical SPipe generation for source `082f4088f560fbe9c584f1aac96dee175f0ec02f60133b815674d91d3869292e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `082f4088f560fbe9c584f1aac96dee175f0ec02f60133b815674d91d3869292e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `082f4088f560fbe9c584f1aac96dee175f0ec02f60133b815674d91d3869292e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/03_system/tools/llm/claude_full/utils/group_tool_uses_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/utils/group_tool_uses_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/utils/group_tool_uses_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/utils/group_tool_uses_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/utils/group_tool_uses_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 4 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/tools/llm/claude_full/utils/group_tool_uses_spec.spl:27:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns original message order in verbose mode' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/utils/group_tool_uses_spec.spl:35:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'groups two supported tool uses from the same assistant message' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/utils/group_tool_uses_spec.spl:46:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'does not group a single tool use or unsupported tool' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
