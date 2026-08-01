# Claude Full Review Remote Command

> Checks reviewRemote command parity for remote-only code review.

<!-- sdn-diagram:id=review_remote_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=review_remote_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

review_remote_spec -> std
review_remote_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=review_remote_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full Review Remote Command

Checks reviewRemote command parity for remote-only code review.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/commands/review_remote_spec.spl` |
| Updated | 2026-07-05 |
| Generator | `simple spipe-docgen` (Simple) |

Checks reviewRemote command parity for remote-only code review.

## Scenarios

### Claude full reviewRemote command

#### exposes hidden remote review command metadata

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val command = reviewRemoteCommand()
expect(command.typeName).to_equal("local-jsx")
expect(command.name).to_equal("review")
expect(command.argumentHint).to_equal("[pull-request-url-or-number]")
expect(command.loadPath).to_equal("./reviewRemote.js")
expect(command.immediate).to_equal(true)
expect(command.hidden).to_equal(true)
expect(reviewRemoteCommandName()).to_equal("review")
expect(reviewRemoteLoadPath()).to_equal("./reviewRemote.js")
```

</details>

#### maps setup gates before starting review

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(reviewRemoteNextStep(ReviewRemoteState.new(false, "sess", "12", "main", "feature", "diff", 1, false, false))).to_equal("signin")
expect(reviewRemoteNextStep(ReviewRemoteState.new(true, "", "12", "main", "feature", "diff", 1, false, false))).to_equal("remote-session")
expect(reviewRemoteNextStep(ReviewRemoteState.new(true, "sess", "", "main", "feature", "diff", 1, false, false))).to_equal("pull-request")
expect(reviewRemoteNextStep(ReviewRemoteState.new(true, "sess", "12", "main", "feature", "", 0, false, false))).to_equal("load-diff")
expect(reviewRemoteStatusLabel(ReviewRemoteState.new(true, "sess", "12", "main", "feature", "diff", 1, false, false))).to_equal("Ready to review")
```

</details>

#### builds the review prompt and respects viewer-only mode

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val state = ReviewRemoteState.new(true, "sess", "https://github.com/acme/repo/pull/12", "main", "feature", "3 files changed", 3, false, true)
val result = callReviewRemote(state)
expect(result.ok).to_equal(true)
expect(result.stepName).to_equal("review")
expect(result.shouldStartRemote).to_equal(true)
expect(result.allowMutationTools).to_equal(false)
expect(result.prompt).to_contain("main...feature")
expect(result.prompt).to_contain("3 files changed")
expect(result.prompt).to_contain("bugs, risks, regressions, and missing tests")
```

</details>

#### reports network failures and source coverage

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val failure = callReviewRemote(ReviewRemoteState.new(true, "sess", "12", "main", "feature", "diff", 1, true, false))
expect(failure.ok).to_equal(false)
expect(failure.stepName).to_equal("network")
expect(failure.shouldStartRemote).to_equal(false)
expect(reviewRemoteSourceLinesModeled()).to_equal(316)
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
