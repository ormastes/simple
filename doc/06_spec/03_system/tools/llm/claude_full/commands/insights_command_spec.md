# Claude Full Insights Command

> Focused parity for upstream `commands/insights.ts`.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full Insights Command

Focused parity for upstream `commands/insights.ts`.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/commands/insights_command_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Focused parity for upstream `commands/insights.ts`.

`REQ-LLM-CARET-HIDDEN-008` applies to the insights descriptor, enablement,
interactive-session admission, and rejection scenarios. This remains
parts-bin evidence and does not claim shipped Caret reachability.

This source-synchronized specification does not claim execution in the current
runtime-blocked tranche.

## Scenarios

### Claude full insights command

### REQ-LLM-CARET-HIDDEN-008: descriptor and enablement

#### should keep command metadata and source parity floor
### Supporting parts-bin summary and report mechanics

#### should summarize only the last thirty days of local sessions

- should summarize only the last thirty days of local sessions
- Summarize sessions from the last thirty days
   - Expected: metrics.sessionsAnalyzed equals `2`
   - Expected: metrics.messages equals `20`
   - Expected: metrics.inputTokens equals `13200`
   - Expected: metrics.outputTokens equals `2100`
   - Expected: metrics.totalTokens equals `15300`
   - Expected: metrics.filesTouched equals `8`
   - Expected: metrics.toolCalls equals `24`
   - Expected: metrics.firstAttemptSuccesses equals `1`
   - Expected: metrics.firstAttemptFailures equals `1`
   - Expected: metrics.topTaskKind equals `debugging`
   - Expected: insightSuccessRatePercent(metrics) equals `50`
   - Expected: boundaryMetrics.sessionsAnalyzed equals `1`
   - Expected: boundaryMetrics.messages equals `1`
   - Expected: boundaryMetrics.totalTokens equals `12`
   - Expected: boundaryMetrics.topTaskKind equals `review`


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should summarize only the last thirty days of local sessions")
step("Summarize sessions from the last thirty days")
val metrics = summarizeInsightsSessions(InsightsState.sample().sessions)
expect(metrics.sessionsAnalyzed).to_equal(2)
expect(metrics.messages).to_equal(20)
expect(metrics.inputTokens).to_equal(13200)
expect(metrics.outputTokens).to_equal(2100)
expect(metrics.totalTokens).to_equal(15300)
expect(metrics.filesTouched).to_equal(8)
expect(metrics.toolCalls).to_equal(24)
expect(metrics.firstAttemptSuccesses).to_equal(1)
expect(metrics.firstAttemptFailures).to_equal(1)
expect(metrics.topTaskKind).to_equal("debugging")
expect(insightSuccessRatePercent(metrics)).to_equal(50)

val dayThirty = InsightsSession.new("day-30", 30, 1, 10, 2, 1, 1, true, "review")
val dayThirtyOne = InsightsSession.new("day-31", 31, 100, 1000, 200, 10, 10, true, "feature")
val negativeDay = InsightsSession.new("negative-day", -1, 100, 1000, 200, 10, 10, true, "debugging")
val boundaryMetrics = summarizeInsightsSessions([dayThirty, dayThirtyOne, negativeDay])
expect(boundaryMetrics.sessionsAnalyzed).to_equal(1)
expect(boundaryMetrics.messages).to_equal(1)
expect(boundaryMetrics.totalTokens).to_equal(12)
expect(boundaryMetrics.topTaskKind).to_equal("review")
```

</details>

#### should generate report HTML and handle browser fallback

- should generate report HTML and handle browser fallback
- Generate the insights report and handle browser fallback
   - Expected: result.typeName equals `report`
   - Expected: result.reportPath equals `~/.claude/usage-data/report.html`
   - Expected: result.openedBrowser is true
   - Expected: insightsReportContainsCoreSections(result.html) is true
   - Expected: result.openedBrowser is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should generate report HTML and handle browser fallback")
step("Generate the insights report and handle browser fallback")
var state = InsightsState.sample()
var result = runInsights(state)
expect(result.typeName).to_equal("report")
expect(result.reportPath).to_equal("~/.claude/usage-data/report.html")
expect(result.openedBrowser).to_equal(true)
expect(result.message).to_contain("opened")
expect(insightsReportContainsCoreSections(result.html)).to_equal(true)
expect(result.html).to_contain("sessions=2")
expect(result.html).to_contain("tokens=15300")

state.browserOpenFails = true
result = runInsights(state)
expect(result.openedBrowser).to_equal(false)
expect(result.message).to_contain("Open it in your browser")
```

</details>

### REQ-LLM-CARET-HIDDEN-008: rejections and admission

#### should reject no-data noninteractive and write-failure states

- should reject no-data noninteractive and write-failure states
- Reject no-data noninteractive and write-failure states
   - Expected: noData.typeName equals `message`
   - Expected: noData.reportPath equals ``
   - Expected: noData.html equals ``
   - Expected: noData.metrics.sessionsAnalyzed equals `0`
   - Expected: noData.metrics.messages equals `0`
   - Expected: noData.metrics.inputTokens equals `0`
   - Expected: noData.metrics.outputTokens equals `0`
   - Expected: noData.metrics.totalTokens equals `0`
   - Expected: noData.metrics.filesTouched equals `0`
   - Expected: noData.metrics.toolCalls equals `0`
   - Expected: noData.metrics.firstAttemptSuccesses equals `0`
   - Expected: noData.metrics.firstAttemptFailures equals `0`
   - Expected: noData.metrics.topTaskKind equals ``
   - Expected: nonInteractive.typeName equals `message`
   - Expected: nonInteractive.reportPath equals ``
   - Expected: nonInteractive.html equals ``
   - Expected: nonInteractive.metrics.sessionsAnalyzed equals `0`
   - Expected: nonInteractive.metrics.messages equals `0`
   - Expected: nonInteractive.metrics.inputTokens equals `0`
   - Expected: nonInteractive.metrics.outputTokens equals `0`
   - Expected: nonInteractive.metrics.totalTokens equals `0`
   - Expected: nonInteractive.metrics.filesTouched equals `0`
   - Expected: nonInteractive.metrics.toolCalls equals `0`
   - Expected: nonInteractive.metrics.firstAttemptSuccesses equals `0`
   - Expected: nonInteractive.metrics.firstAttemptFailures equals `0`
   - Expected: nonInteractive.metrics.topTaskKind equals ``
   - Expected: writeFailure.typeName equals `message`
   - Expected: writeFailure.reportPath equals ``
   - Expected: writeFailure.html equals ``
   - Expected: writeFailure.metrics.sessionsAnalyzed equals `2`
   - Expected: writeFailure.metrics.messages equals `20`
   - Expected: writeFailure.metrics.inputTokens equals `13200`
   - Expected: writeFailure.metrics.outputTokens equals `2100`
   - Expected: writeFailure.metrics.totalTokens equals `15300`
   - Expected: writeFailure.metrics.filesTouched equals `8`
   - Expected: writeFailure.metrics.toolCalls equals `24`
   - Expected: writeFailure.metrics.firstAttemptSuccesses equals `1`
   - Expected: writeFailure.metrics.firstAttemptFailures equals `1`
   - Expected: writeFailure.metrics.topTaskKind equals `debugging`


<details>
<summary>Executable SSpec</summary>

Runnable source: 57 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should reject no-data noninteractive and write-failure states")
step("Reject no-data noninteractive and write-failure states")
val noData = runInsights(InsightsState.empty())
expect(noData.typeName).to_equal("message")
expect(noData.message).to_contain("No Claude Code sessions")
expect(noData.reportPath).to_equal("")
expect(noData.html).to_equal("")
expect(noData.openedBrowser).to_be(false)
expect(noData.metrics.sessionsAnalyzed).to_equal(0)
expect(noData.metrics.messages).to_equal(0)
expect(noData.metrics.inputTokens).to_equal(0)
expect(noData.metrics.outputTokens).to_equal(0)
expect(noData.metrics.totalTokens).to_equal(0)
expect(noData.metrics.filesTouched).to_equal(0)
expect(noData.metrics.toolCalls).to_equal(0)
expect(noData.metrics.firstAttemptSuccesses).to_equal(0)
expect(noData.metrics.firstAttemptFailures).to_equal(0)
expect(noData.metrics.topTaskKind).to_equal("")

var state = InsightsState.sample()
state.nonInteractive = true
val nonInteractive = runInsights(state)
expect(nonInteractive.typeName).to_equal("message")
expect(nonInteractive.message).to_contain("interactive")
expect(nonInteractive.reportPath).to_equal("")
expect(nonInteractive.html).to_equal("")
expect(nonInteractive.openedBrowser).to_be(false)
expect(nonInteractive.metrics.sessionsAnalyzed).to_equal(0)
expect(nonInteractive.metrics.messages).to_equal(0)
expect(nonInteractive.metrics.inputTokens).to_equal(0)
expect(nonInteractive.metrics.outputTokens).to_equal(0)
expect(nonInteractive.metrics.totalTokens).to_equal(0)
expect(nonInteractive.metrics.filesTouched).to_equal(0)
expect(nonInteractive.metrics.toolCalls).to_equal(0)
expect(nonInteractive.metrics.firstAttemptSuccesses).to_equal(0)
expect(nonInteractive.metrics.firstAttemptFailures).to_equal(0)
expect(nonInteractive.metrics.topTaskKind).to_equal("")

state = InsightsState.sample()
state.writeReportFails = true
val writeFailure = runInsights(state)
expect(writeFailure.typeName).to_equal("message")
expect(writeFailure.message).to_contain("Failed to write")
expect(writeFailure.reportPath).to_equal("")
expect(writeFailure.html).to_equal("")
expect(writeFailure.openedBrowser).to_be(false)
expect(writeFailure.metrics.sessionsAnalyzed).to_equal(2)
expect(writeFailure.metrics.messages).to_equal(20)
expect(writeFailure.metrics.inputTokens).to_equal(13200)
expect(writeFailure.metrics.outputTokens).to_equal(2100)
expect(writeFailure.metrics.totalTokens).to_equal(15300)
expect(writeFailure.metrics.filesTouched).to_equal(8)
expect(writeFailure.metrics.toolCalls).to_equal(24)
expect(writeFailure.metrics.firstAttemptSuccesses).to_equal(1)
expect(writeFailure.metrics.firstAttemptFailures).to_equal(1)
expect(writeFailure.metrics.topTaskKind).to_equal("debugging")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
- `REQ-LLM-CARET-HIDDEN-008`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `d3acee4e91b6c6b7ab42276a57d487f8f62eada986cc858f8b93c2fbb4b0d047`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `d3acee4e91b6c6b7ab42276a57d487f8f62eada986cc858f8b93c2fbb4b0d047`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `d3acee4e91b6c6b7ab42276a57d487f8f62eada986cc858f8b93c2fbb4b0d047`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **76/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/03_system/tools/llm/claude_full/commands/insights_command_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/commands/insights_command_spec.md (current)
findings: 12 blockers: 1
  narrative=100 structure=70 oracle=70
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=76; blocker cap makes effective=49
doc/06_spec/03_system/tools/llm/claude_full/commands/insights_command_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/commands/insights_command_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/commands/insights_command_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 40 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/tools/llm/claude_full/commands/insights_command_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/03_system/tools/llm/claude_full/commands/insights_command_spec.spl:37:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'should keep command metadata and source parity floor' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/03_system/tools/llm/claude_full/commands/insights_command_spec.spl:37:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should keep command metadata and source parity floor' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/commands/insights_command_spec.spl:59:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should summarize only the last thirty days of local sessions' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/commands/insights_command_spec.spl:59:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should summarize only the last thirty days of local sessions' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/commands/insights_command_spec.spl:85:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should generate report HTML and handle browser fallback' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/commands/insights_command_spec.spl:85:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should generate report HTML and handle browser fallback' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/commands/insights_command_spec.spl:105:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject no-data noninteractive and write-failure states' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/commands/insights_command_spec.spl:105:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should reject no-data noninteractive and write-failure states' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
