# Claude Full Tool Name Constants

> Mirrors one-line Claude tool constant files so the strict full-parity matrix

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full Tool Name Constants

Mirrors one-line Claude tool constant files so the strict full-parity matrix

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/tools/tool_name_constants_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Mirrors one-line Claude tool constant files so the strict full-parity matrix
has executable evidence for the literal tool names used by command dispatch.

## Scenarios

### Claude full tool name constants

#### should expose plan and worktree tool names

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should expose plan and worktree tool names
- Read the tool constants mapped from Claude tool constant files
   - Expected: ENTER_PLAN_MODE_TOOL_NAME equals `EnterPlanMode`
   - Expected: ENTER_WORKTREE_TOOL_NAME equals `EnterWorktree`
   - Expected: EXIT_WORKTREE_TOOL_NAME equals `ExitWorktree`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should expose plan and worktree tool names")
step("Read the tool constants mapped from Claude tool constant files")
expect(ENTER_PLAN_MODE_TOOL_NAME).to_equal("EnterPlanMode")
expect(ENTER_WORKTREE_TOOL_NAME).to_equal("EnterWorktree")
expect(EXIT_WORKTREE_TOOL_NAME).to_equal("ExitWorktree")
```

</details>

#### should expose message and skill tool names

- should expose message and skill tool names
- Read the remaining tool constants in this batch
   - Expected: SEND_MESSAGE_TOOL_NAME equals `SendMessage`
   - Expected: SKILL_TOOL_NAME equals `Skill`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should expose message and skill tool names")
step("Read the remaining tool constants in this batch")
expect(SEND_MESSAGE_TOOL_NAME).to_equal("SendMessage")
expect(SKILL_TOOL_NAME).to_equal("Skill")
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

- Canonical SPipe generation for source `590995c68579193d66a710db8c39ab97e0f69858232dd70cfa82f1d6b0049538`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `590995c68579193d66a710db8c39ab97e0f69858232dd70cfa82f1d6b0049538`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `590995c68579193d66a710db8c39ab97e0f69858232dd70cfa82f1d6b0049538`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/tools/llm/claude_full/tools/tool_name_constants_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/tools/tool_name_constants_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=90 oracle=100
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/tools/tool_name_constants_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/tools/tool_name_constants_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/tools/tool_name_constants_spec.spl:23:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should expose plan and worktree tool names' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/tools/tool_name_constants_spec.spl:23:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should expose plan and worktree tool names' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/tools/tool_name_constants_spec.spl:31:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should expose message and skill tool names' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/tools/tool_name_constants_spec.spl:31:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should expose message and skill tool names' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
