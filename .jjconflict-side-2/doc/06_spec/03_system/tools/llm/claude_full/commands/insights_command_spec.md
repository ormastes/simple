# Claude Full Insights Command

> Focused source-synchronized parity for the Claude-full insights command.

| Tests | Active | Skipped | Pending |
|---|---:|---:|---:|
| 4 | 4 | 0 | 0 |

## Status and scope

- Executable source: `test/03_system/tools/llm/claude_full/commands/insights_command_spec.spl`
- Requirement: `REQ-LLM-CARET-HIDDEN-008`, scoped only to scenario 1
  (descriptor and enablement) and scenario 4 (interactive-session admission
  and rejection behavior)
- Supporting parts-bin scope: scenarios 2–3 cover summary and report mechanics
  without claiming `REQ-LLM-CARET-HIDDEN-008`
- Execution in this tranche: **0 scenarios executed; no PASS is claimed**
- Runtime/docgen status: blocked until a qualified self-hosted Simple runtime is available
- Evidence boundary: function-level parts-bin behavior only; no shipped Caret
  CLI/TUI admission or browser-process execution is claimed

## Helper contract

`countLines(text_value)` is a test-local source-parity helper. It starts at
zero and adds one for each newline byte in the supplied text; it does not read
files, infer a trailing line, or participate in production insights behavior.

## Requirement group: REQ-LLM-CARET-HIDDEN-008 — descriptor and enablement

### Scenario: should keep command metadata and source parity floor

- Check insights command metadata and source parity.
- Expected: the descriptor is the visible, enabled, interactive-only
  `local-jsx` insights command with an empty argument hint.
- Expected: the report configuration retains a thirty-day lookback and the
  modeled source remains at its accepted 3,200-line floor.

<details>
<summary>Executable SSpec</summary>

```simple
it "should keep command metadata and source parity floor":
    step("Check insights command metadata and source parity")
    val command = insightsCommand(true)
    expect(command.typeName).to_equal("local-jsx")
    expect(command.name).to_equal("insights")
    expect(command.description).to_contain("usage")
    expect(command.argumentHint).to_equal("")
    expect(command.isHidden).to_equal(false)
    expect(command.enabled).to_equal(true)
    expect(command.supportsNonInteractive).to_equal(false)
    expect(insightsCommandName()).to_equal("insights")
    expect(insightsLookbackDays()).to_equal(30)
    expect(insightsReportPath()).to_contain("report.html")

    val source = file_read("src/app/llm_caret/claude_full/commands/insights.spl") ?? ""
    expect(countLines(source)).to_be_greater_than(3199)
    expect(insightsCommandSourceLinesModeled()).to_equal(3200)
```

</details>

## Supporting parts-bin group: summary and report mechanics

### Scenario: should summarize only the last thirty days of local sessions

- Summarize sessions from the last thirty days.
- Expected: only the two in-window fixture sessions contribute their exact
  message, token, file, tool-call, and first-attempt totals.
- Expected: day 30 is included, day 31 and negative ages are excluded, and
  the top task kind reflects only included sessions.

<details>
<summary>Executable SSpec</summary>

```simple
it "should summarize only the last thirty days of local sessions":
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

### Scenario: should generate report HTML and handle browser fallback

- Generate the insights report and handle browser fallback.
- Expected: report HTML contains the accepted core sections and metrics.
- Expected: browser-open failure preserves the report and returns the manual
  open guidance.

<details>
<summary>Executable SSpec</summary>

```simple
it "should generate report HTML and handle browser fallback":
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

## Requirement group: REQ-LLM-CARET-HIDDEN-008 — rejections and admission

### Scenario: should reject no-data noninteractive and write-failure states

- Reject no-data noninteractive and write-failure states.
- Expected: each rejected state returns a `message` diagnostic with no report
  path, HTML, or browser-open side effect.
- Expected: no-data and noninteractive rejection expose empty metrics;
  write failure retains only the already-computed in-window metrics.

<details>
<summary>Executable SSpec</summary>

```simple
it "should reject no-data noninteractive and write-failure states":
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
