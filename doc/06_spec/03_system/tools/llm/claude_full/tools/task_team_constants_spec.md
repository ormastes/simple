# Claude Full Task And Team Tool Constants

> Mirrors one-line Claude task/team tool constant files so each mapped full-parity

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full Task And Team Tool Constants

Mirrors one-line Claude task/team tool constant files so each mapped full-parity

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/tools/task_team_constants_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Mirrors one-line Claude task/team tool constant files so each mapped full-parity
target has executable literal evidence.

## Scenarios

### Claude full task and team tool constants

#### should expose task tool names

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should expose task tool names
- Read the task tool constants mapped from Claude
   - Expected: TASK_CREATE_TOOL_NAME equals `TaskCreate`
   - Expected: TASK_GET_TOOL_NAME equals `TaskGet`
   - Expected: TASK_LIST_TOOL_NAME equals `TaskList`
   - Expected: TASK_OUTPUT_TOOL_NAME equals `TaskOutput`
   - Expected: TASK_UPDATE_TOOL_NAME equals `TaskUpdate`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should expose task tool names")
step("Read the task tool constants mapped from Claude")
expect(TASK_CREATE_TOOL_NAME).to_equal("TaskCreate")
expect(TASK_GET_TOOL_NAME).to_equal("TaskGet")
expect(TASK_LIST_TOOL_NAME).to_equal("TaskList")
expect(TASK_OUTPUT_TOOL_NAME).to_equal("TaskOutput")
expect(TASK_UPDATE_TOOL_NAME).to_equal("TaskUpdate")
```

</details>

#### should expose team, todo, and tool-search names

- should expose team, todo, and tool-search names
- Read the remaining constants in this batch
   - Expected: TEAM_CREATE_TOOL_NAME equals `TeamCreate`
   - Expected: TEAM_DELETE_TOOL_NAME equals `TeamDelete`
   - Expected: TODO_WRITE_TOOL_NAME equals `TodoWrite`
   - Expected: TOOL_SEARCH_TOOL_NAME equals `ToolSearch`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should expose team, todo, and tool-search names")
step("Read the remaining constants in this batch")
expect(TEAM_CREATE_TOOL_NAME).to_equal("TeamCreate")
expect(TEAM_DELETE_TOOL_NAME).to_equal("TeamDelete")
expect(TODO_WRITE_TOOL_NAME).to_equal("TodoWrite")
expect(TOOL_SEARCH_TOOL_NAME).to_equal("ToolSearch")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
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

- Canonical SPipe generation for source `16e760c81857a68e8445c6a1f7b8aeec769908ad563a0274efb070235de3dcb9`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `16e760c81857a68e8445c6a1f7b8aeec769908ad563a0274efb070235de3dcb9`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `16e760c81857a68e8445c6a1f7b8aeec769908ad563a0274efb070235de3dcb9`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/tools/llm/claude_full/tools/task_team_constants_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/tools/task_team_constants_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=90 oracle=100
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/tools/task_team_constants_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/tools/task_team_constants_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/tools/task_team_constants_spec.spl:27:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should expose task tool names' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/tools/task_team_constants_spec.spl:27:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should expose task tool names' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/tools/task_team_constants_spec.spl:37:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should expose team, todo, and tool-search names' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/tools/task_team_constants_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should expose team, todo, and tool-search names' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
