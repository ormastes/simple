# Claude Full Effort, Export, Fallback, and Feedback Components

> Checks modern SSpec parity for small component helpers in the next parity slice.

<!-- sdn-diagram:id=effort_export_feedback_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=effort_export_feedback_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

effort_export_feedback_spec -> std
effort_export_feedback_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=effort_export_feedback_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full Effort, Export, Fallback, and Feedback Components

Checks modern SSpec parity for small component helpers in the next parity slice.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/components/effort_export_feedback_spec.spl` |
| Updated | 2026-07-05 |
| Generator | `simple spipe-docgen` (Simple) |

Checks modern SSpec parity for small component helpers in the next parity slice.

## Scenarios

### Claude full effort export fallback and feedback components

#### should render effort, exit, export, and fallback state

- Render effort and exit state
   - Expected: effortIndicatorLabel("high") equals `effort high`
   - Expected: effortIndicatorTone("low") equals `muted`
   - Expected: exitFlowCanExit(exitState) is false
   - Expected: exitFlowActionLabel(exitState) equals `Confirm exit`
- Render export and fallback state
   - Expected: exportDialogCanSubmit(exportState) is true
   - Expected: fallbackToolUseErrorAction(err) equals `Retry`
   - Expected: fallbackToolUseRejectedMessage("grep") equals `Tool use rejected: grep`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Render effort and exit state")
expect(effortIndicatorLabel("high")).to_equal("effort high")
expect(effortIndicatorTone("low")).to_equal("muted")
val exitState = ExitFlowState.new(true, false, "")
expect(exitFlowCanExit(exitState)).to_equal(false)
expect(exitFlowActionLabel(exitState)).to_equal("Confirm exit")

step("Render export and fallback state")
val exportState = ExportDialogState.new(true, "json", "out.json", true)
expect(exportDialogCanSubmit(exportState)).to_equal(true)
expect(exportDialogSummary(exportState)).to_contain("metadata")
val err = FallbackToolUseErrorState.new("grep", "denied", true)
expect(fallbackToolUseErrorAction(err)).to_equal("Retry")
expect(fallbackToolUseRejectedMessage("grep")).to_equal("Tool use rejected: grep")
```

</details>

#### should render fast icon and feedback survey state

- Render icon state
   - Expected: fastIconName("") equals `spark`
   - Expected: fastIconTone(false, true) equals `active`
- Render feedback state
   - Expected: feedbackSurveyCanSubmit(survey) is true
   - Expected: submitFeedbackSurvey(survey).submitted is true
   - Expected: feedbackSurveyViewVisible(view) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Render icon state")
expect(fastIconName("")).to_equal("spark")
expect(fastIconTone(false, true)).to_equal("active")

step("Render feedback state")
val survey = FeedbackSurveyState.new(5, "great", "a@example.com", false)
expect(feedbackSurveyCanSubmit(survey)).to_equal(true)
expect(submitFeedbackSurvey(survey).submitted).to_equal(true)
val view = FeedbackSurveyViewState.new("", true, true, "")
expect(feedbackSurveyViewVisible(view)).to_equal(true)
expect(feedbackSurveyViewSummary(view)).to_contain("submitting")
```

</details>

#### should check modeled TypeScript source floors

- Read source line helpers
   - Expected: effortIndicatorSourceLinesModeled() equals `42`
   - Expected: exitFlowSourceLinesModeled() equals `47`
   - Expected: exportDialogSourceLinesModeled() equals `127`
   - Expected: fallbackToolUseErrorSourceLinesModeled() equals `115`
   - Expected: fallbackToolUseRejectedSourceLinesModeled() equals `15`
   - Expected: fastIconSourceLinesModeled() equals `45`
   - Expected: feedbackSurveySourceLinesModeled() equals `173`
   - Expected: feedbackSurveyViewSourceLinesModeled() equals `107`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Read source line helpers")
expect(effortIndicatorSourceLinesModeled()).to_equal(42)
expect(exitFlowSourceLinesModeled()).to_equal(47)
expect(exportDialogSourceLinesModeled()).to_equal(127)
expect(fallbackToolUseErrorSourceLinesModeled()).to_equal(115)
expect(fallbackToolUseRejectedSourceLinesModeled()).to_equal(15)
expect(fastIconSourceLinesModeled()).to_equal(45)
expect(feedbackSurveySourceLinesModeled()).to_equal(173)
expect(feedbackSurveyViewSourceLinesModeled()).to_equal(107)
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
