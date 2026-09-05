# Claude Full Additional Tool Constants

> Mirrors the next small Claude tool-name and render-interval constant files.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full Additional Tool Constants

Mirrors the next small Claude tool-name and render-interval constant files.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/tools/more_tool_constants_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Mirrors the next small Claude tool-name and render-interval constant files.

## Scenarios

### Claude full additional constants

#### should expose exit-plan and notebook tool names

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should expose exit-plan and notebook tool names
- Read the constants mapped from ExitPlanModeTool and NotebookEditTool
   - Expected: EXIT_PLAN_MODE_TOOL_NAME equals `ExitPlanMode`
   - Expected: EXIT_PLAN_MODE_V2_TOOL_NAME equals `ExitPlanMode`
   - Expected: NOTEBOOK_EDIT_TOOL_NAME equals `NotebookEdit`
   - Expected: notebookEditToolName() equals `NotebookEdit`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should expose exit-plan and notebook tool names")
step("Read the constants mapped from ExitPlanModeTool and NotebookEditTool")
expect(EXIT_PLAN_MODE_TOOL_NAME).to_equal("ExitPlanMode")
expect(EXIT_PLAN_MODE_V2_TOOL_NAME).to_equal("ExitPlanMode")
expect(NOTEBOOK_EDIT_TOOL_NAME).to_equal("NotebookEdit")
expect(notebookEditToolName()).to_equal("NotebookEdit")
```

</details>

#### should expose shell tool names and frame interval

- should expose shell tool names and frame interval
- Read the shell tool constants and render frame interval
   - Expected: BASH_TOOL_NAME equals `Bash`
   - Expected: bashToolName() equals `Bash`
   - Expected: POWERSHELL_TOOL_NAME equals `PowerShell`
   - Expected: powerShellToolName() equals `PowerShell`
   - Expected: FRAME_INTERVAL_MS equals `16`
   - Expected: frameIntervalMs() equals `16`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should expose shell tool names and frame interval")
step("Read the shell tool constants and render frame interval")
expect(BASH_TOOL_NAME).to_equal("Bash")
expect(bashToolName()).to_equal("Bash")
expect(POWERSHELL_TOOL_NAME).to_equal("PowerShell")
expect(powerShellToolName()).to_equal("PowerShell")
expect(FRAME_INTERVAL_MS).to_equal(16)
expect(frameIntervalMs()).to_equal(16)
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

- Canonical SPipe generation for source `6bb3f78da3acd47b5028465aa93f534e7179847ae45f6a45a2d17b0e6eeab0cb`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `6bb3f78da3acd47b5028465aa93f534e7179847ae45f6a45a2d17b0e6eeab0cb`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `6bb3f78da3acd47b5028465aa93f534e7179847ae45f6a45a2d17b0e6eeab0cb`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/03_system/tools/llm/claude_full/tools/more_tool_constants_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/tools/more_tool_constants_spec.md (current)
findings: 7 blockers: 0
  narrative=100 structure=90 oracle=80
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/tools/more_tool_constants_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/tools/more_tool_constants_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/tools/more_tool_constants_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/tools/llm/claude_full/tools/more_tool_constants_spec.spl:22:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should expose exit-plan and notebook tool names' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/tools/more_tool_constants_spec.spl:22:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should expose exit-plan and notebook tool names' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/tools/more_tool_constants_spec.spl:31:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should expose shell tool names and frame interval' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/tools/more_tool_constants_spec.spl:31:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should expose shell tool names and frame interval' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
