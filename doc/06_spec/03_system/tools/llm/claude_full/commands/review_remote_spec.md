# Claude Full Review Remote Command

> Checks reviewRemote command parity for remote-only code review.

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
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Checks reviewRemote command parity for remote-only code review.

## Scenarios

### Claude full reviewRemote command

#### exposes hidden remote review command metadata

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- exposes hidden remote review command metadata
   - Expected: command.typeName equals `local-jsx`
   - Expected: command.name equals `review`
   - Expected: command.argumentHint equals `[pull-request-url-or-number]`
   - Expected: command.loadPath equals `./reviewRemote.js`
   - Expected: command.immediate is true
   - Expected: command.hidden is true
   - Expected: reviewRemoteCommandName() equals `review`
   - Expected: reviewRemoteLoadPath() equals `./reviewRemote.js`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("exposes hidden remote review command metadata")
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

- maps setup gates before starting review
   - Expected: reviewRemoteNextStep(ReviewRemoteState.new(false, "sess", "12", "main", "feature", "diff", 1, false, false)) equals `signin`
   - Expected: reviewRemoteNextStep(ReviewRemoteState.new(true, "", "12", "main", "feature", "diff", 1, false, false)) equals `remote-session`
   - Expected: reviewRemoteNextStep(ReviewRemoteState.new(true, "sess", "", "main", "feature", "diff", 1, false, false)) equals `pull-request`
   - Expected: reviewRemoteNextStep(ReviewRemoteState.new(true, "sess", "12", "main", "feature", "", 0, false, false)) equals `load-diff`
   - Expected: reviewRemoteStatusLabel(ReviewRemoteState.new(true, "sess", "12", "main", "feature", "diff", 1, false, false)) equals `Ready to review`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("maps setup gates before starting review")
expect(reviewRemoteNextStep(ReviewRemoteState.new(false, "sess", "12", "main", "feature", "diff", 1, false, false))).to_equal("signin")
expect(reviewRemoteNextStep(ReviewRemoteState.new(true, "", "12", "main", "feature", "diff", 1, false, false))).to_equal("remote-session")
expect(reviewRemoteNextStep(ReviewRemoteState.new(true, "sess", "", "main", "feature", "diff", 1, false, false))).to_equal("pull-request")
expect(reviewRemoteNextStep(ReviewRemoteState.new(true, "sess", "12", "main", "feature", "", 0, false, false))).to_equal("load-diff")
expect(reviewRemoteStatusLabel(ReviewRemoteState.new(true, "sess", "12", "main", "feature", "diff", 1, false, false))).to_equal("Ready to review")
```

</details>

#### builds the review prompt and respects viewer-only mode

- builds the review prompt and respects viewer-only mode
   - Expected: result.ok is true
   - Expected: result.stepName equals `review`
   - Expected: result.shouldStartRemote is true
   - Expected: result.allowMutationTools is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("builds the review prompt and respects viewer-only mode")
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

- reports network failures and source coverage
   - Expected: failure.ok is false
   - Expected: failure.stepName equals `network`
   - Expected: failure.shouldStartRemote is false
   - Expected: reviewRemoteSourceLinesModeled() equals `316`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("reports network failures and source coverage")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `fd325d93f28c705c3a3a8622f4b5c045af2cd3324c41de2dfedc223bd5d9b488`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `fd325d93f28c705c3a3a8622f4b5c045af2cd3324c41de2dfedc223bd5d9b488`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `fd325d93f28c705c3a3a8622f4b5c045af2cd3324c41de2dfedc223bd5d9b488`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/03_system/tools/llm/claude_full/commands/review_remote_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/commands/review_remote_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/commands/review_remote_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/commands/review_remote_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/commands/review_remote_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/tools/llm/claude_full/commands/review_remote_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'exposes hidden remote review command metadata' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/commands/review_remote_spec.spl:31:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'maps setup gates before starting review' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/commands/review_remote_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'builds the review prompt and respects viewer-only mode' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
