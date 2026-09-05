# Claude Full GitHub PR status

> Pure Simple coverage for PR review-state derivation.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full GitHub PR status

Pure Simple coverage for PR review-state derivation.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/utils/gh_pr_status_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Pure Simple coverage for PR review-state derivation.

## Scenarios

### Claude full GitHub PR status

#### lets draft status override review decisions

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- lets draft status override review decisions
- Check draft precedence
   - Expected: deriveReviewState(true, "") equals `draft`
   - Expected: deriveReviewState(true, "APPROVED") equals `draft`
   - Expected: deriveReviewState(true, "CHANGES_REQUESTED") equals `draft`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("lets draft status override review decisions")
step("Check draft precedence")
expect(deriveReviewState(true, "")).to_equal("draft")
expect(deriveReviewState(true, "APPROVED")).to_equal("draft")
expect(deriveReviewState(true, "CHANGES_REQUESTED")).to_equal("draft")
```

</details>

#### maps known review decisions

- maps known review decisions
- Check known decisions
   - Expected: deriveReviewState(false, "APPROVED") equals `approved`
   - Expected: deriveReviewState(false, "CHANGES_REQUESTED") equals `changes_requested`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("maps known review decisions")
step("Check known decisions")
expect(deriveReviewState(false, "APPROVED")).to_equal("approved")
expect(deriveReviewState(false, "CHANGES_REQUESTED")).to_equal("changes_requested")
```

</details>

#### uses pending for unknown or empty decisions

- uses pending for unknown or empty decisions
- Check pending fallback
   - Expected: deriveReviewState(false, "") equals `pending`
   - Expected: deriveReviewState(false, "REVIEW_REQUIRED") equals `pending`
   - Expected: deriveReviewState(false, "SOMETHING_ELSE") equals `pending`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("uses pending for unknown or empty decisions")
step("Check pending fallback")
expect(deriveReviewState(false, "")).to_equal("pending")
expect(deriveReviewState(false, "REVIEW_REQUIRED")).to_equal("pending")
expect(deriveReviewState(false, "SOMETHING_ELSE")).to_equal("pending")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `2d61c3b5b5f099558a8a27a5c4970baa6d09d31b5caf584869dbdc6eb665d428`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `2d61c3b5b5f099558a8a27a5c4970baa6d09d31b5caf584869dbdc6eb665d428`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `2d61c3b5b5f099558a8a27a5c4970baa6d09d31b5caf584869dbdc6eb665d428`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/tools/llm/claude_full/utils/gh_pr_status_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/utils/gh_pr_status_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/utils/gh_pr_status_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/utils/gh_pr_status_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/utils/gh_pr_status_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'lets draft status override review decisions' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/utils/gh_pr_status_spec.spl:26:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'maps known review decisions' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/utils/gh_pr_status_spec.spl:33:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'uses pending for unknown or empty decisions' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
