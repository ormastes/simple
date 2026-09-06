# Claude Full Feedback Survey Helpers and File Edit Components

> Checks modern SSpec parity for feedback survey helper hooks and file edit messages.

<!-- sdn-diagram:id=feedback_file_edit_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=feedback_file_edit_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

feedback_file_edit_spec -> std
feedback_file_edit_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=feedback_file_edit_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full Feedback Survey Helpers and File Edit Components

Checks modern SSpec parity for feedback survey helper hooks and file edit messages.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/components/feedback_file_edit_spec.spl` |
| Updated | 2026-07-05 |
| Generator | `simple spipe-docgen` (Simple) |

Checks modern SSpec parity for feedback survey helper hooks and file edit messages.

## Scenarios

### Claude full feedback helpers and file edit components

#### should handle transcript sharing and survey state

- Render transcript share helpers
   - Expected: transcriptShareCanSubmit(submission) is true
   - Expected: transcriptSharePromptVisible(prompt) is true
   - Expected: transcriptSharePromptToggle(prompt).checked is true
- Render survey state
   - Expected: surveyStateCanSubmit(rated) is true
   - Expected: surveyStateSubmit(rated).submitted is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Render transcript share helpers")
val submission = TranscriptShareSubmission.new(true, "abc", "user@example.com", "")
expect(transcriptShareCanSubmit(submission)).to_equal(true)
expect(transcriptSharePayload(submission)).to_contain("abc")
val prompt = TranscriptSharePromptState.new(true, false, "abc")
expect(transcriptSharePromptVisible(prompt)).to_equal(true)
expect(transcriptSharePromptToggle(prompt).checked).to_equal(true)

step("Render survey state")
val survey = SurveyState.new(true, 0, "", false)
val rated = surveyStateWithRating(survey, 4)
expect(surveyStateCanSubmit(rated)).to_equal(true)
expect(surveyStateSubmit(rated).submitted).to_equal(true)
```

</details>

#### should handle debounced digits, memory, and post compact surveys

- Commit debounced digits
   - Expected: input.value equals `1`
   - Expected: debouncedDigitInputCommit(input).value equals `23`
   - Expected: input.delay_ms equals `5000`
- Render memory and post compact surveys
   - Expected: memorySurveyVisible(memory) is true
   - Expected: memorySurveySubmit(memory).dismissed is true
   - Expected: postCompactSurveyCanSubmit(compact) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Commit debounced digits")
val input = DebouncedDigitInputState.new("a1", "b23", 9000)
expect(input.value).to_equal("1")
expect(debouncedDigitInputCommit(input).value).to_equal("23")
expect(input.delay_ms).to_equal(5000)

step("Render memory and post compact surveys")
val memory = MemorySurveyState.new(true, 2, false, 5, "good")
expect(memorySurveyVisible(memory)).to_equal(true)
expect(memorySurveySubmit(memory).dismissed).to_equal(true)
val compact = PostCompactSurveyState.new(true, 1200, false, 3)
expect(postCompactSurveyCanSubmit(compact)).to_equal(true)
expect(postCompactSurveySummary(compact)).to_contain("1200")
```

</details>

#### should render file edit diff and update messages

- Render file edit diff
   - Expected: fileEditDiffChanged(diff) is true
   - Expected: fileEditDiffLineCount(diff.after_text) equals `2`
- Render file edit updated message
   - Expected: fileEditUpdatedTone(updated) equals `success`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Render file edit diff")
val diff = FileEditDiffState.new("a.spl", "one", "one\ntwo", true)
expect(fileEditDiffChanged(diff)).to_equal(true)
expect(fileEditDiffLineCount(diff.after_text)).to_equal(2)
expect(fileEditDiffRender(diff)).to_contain("+++ a.spl")

step("Render file edit updated message")
val updated = FileEditUpdatedMessageState.new("a.spl", true, 2)
expect(fileEditUpdatedTone(updated)).to_equal("success")
expect(fileEditUpdatedSummary(updated)).to_contain("lines=2")
```

</details>

#### should check modeled TypeScript source floors

- Read source line helpers
   - Expected: submitTranscriptShareSourceLinesModeled() equals `112`
   - Expected: transcriptSharePromptSourceLinesModeled() equals `87`
   - Expected: useDebouncedDigitInputSourceLinesModeled() equals `82`
   - Expected: useMemorySurveySourceLinesModeled() equals `212`
   - Expected: usePostCompactSurveySourceLinesModeled() equals `205`
   - Expected: useSurveyStateSourceLinesModeled() equals `99`
   - Expected: fileEditToolDiffSourceLinesModeled() equals `180`
   - Expected: fileEditToolUpdatedMessageSourceLinesModeled() equals `123`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Read source line helpers")
expect(submitTranscriptShareSourceLinesModeled()).to_equal(112)
expect(transcriptSharePromptSourceLinesModeled()).to_equal(87)
expect(useDebouncedDigitInputSourceLinesModeled()).to_equal(82)
expect(useMemorySurveySourceLinesModeled()).to_equal(212)
expect(usePostCompactSurveySourceLinesModeled()).to_equal(205)
expect(useSurveyStateSourceLinesModeled()).to_equal(99)
expect(fileEditToolDiffSourceLinesModeled()).to_equal(180)
expect(fileEditToolUpdatedMessageSourceLinesModeled()).to_equal(123)
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
