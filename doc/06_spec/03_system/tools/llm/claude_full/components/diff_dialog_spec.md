# Claude Full DiffDialog

> Focused parity checks for the Claude full diff dialog helper state.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full DiffDialog

Focused parity checks for the Claude full diff dialog helper state.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/components/diff_dialog_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Focused parity checks for the Claude full diff dialog helper state.

## Scenarios

### Claude full DiffDialog component

#### should summarize open, loading, empty, and error states

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should summarize open, loading, empty, and error states
   - Expected: diffDialogVisible(open) is true
   - Expected: diffDialogTitle(open) equals `Review patch`
   - Expected: diffDialogStatus(loading) equals `loading`
   - Expected: diffDialogStatus(empty) equals `empty`
   - Expected: diffDialogEmptySummary(empty) equals `No changes to review`
   - Expected: diffDialogStatus(failed) equals `error`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should summarize open, loading, empty, and error states")
val open = diffDialogOpen("Review patch", 2, 2, 10, 3)
expect(diffDialogVisible(open)).to_equal(true)
expect(diffDialogTitle(open)).to_equal("Review patch")
expect(diffDialogChangeSummary(open)).to_contain("2 files")
expect(diffDialogChangeSummary(open)).to_contain("+10 -3")

val loading = diffDialogWithLoading(open, true)
expect(diffDialogStatus(loading)).to_equal("loading")
expect(diffDialogLoadingSummary(loading)).to_contain("Loading")

val empty = diffDialogOpen("", 0, 0, 0, 0)
expect(diffDialogStatus(empty)).to_equal("empty")
expect(diffDialogEmptySummary(empty)).to_equal("No changes to review")

val failed = diffDialogWithError(open, "missing patch")
expect(diffDialogStatus(failed)).to_equal("error")
expect(diffDialogErrorSummary(failed)).to_contain("missing patch")
```

</details>

#### should expose selection, actions, keyboard labels, and source floor

- should expose selection, actions, keyboard labels, and source floor
   - Expected: diffDialogSelectedFileLabel(selected) equals `src/app/main.spl`
   - Expected: diffDialogCanAcceptSelected(selected) is true
   - Expected: diffDialogAcceptSelected(selected).kind equals `accept_file`
   - Expected: diffDialogRejectAll(selected).closed is true
   - Expected: diffDialogToggleViewMode(selected).viewMode equals `unified`
   - Expected: diffDialogSourceLinesModeled() equals `382`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should expose selection, actions, keyboard labels, and source floor")
val selected = diffDialogWithSelection(diffDialogOpen("", 3, 3, 7, 2), "src/app/main.spl")
expect(diffDialogSelectedFileLabel(selected)).to_equal("src/app/main.spl")
expect(diffDialogCanAcceptSelected(selected)).to_equal(true)
expect(diffDialogAcceptSelected(selected).kind).to_equal("accept_file")
expect(diffDialogRejectAll(selected).closed).to_equal(true)
expect(diffDialogToggleViewMode(selected).viewMode).to_equal("unified")
expect(diffDialogKeyboardLabel("reject_all")).to_contain("Reject all")
expect(diffDialogFooterLabel(selected)).to_contain("Esc Close")
expect(diffDialogSourceLinesModeled()).to_equal(382)
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

- Canonical SPipe generation for source `79c5592c6cea7f8fa42895aa10eff8e30997a94bdf71bfda0bd1d20e420d6792`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `79c5592c6cea7f8fa42895aa10eff8e30997a94bdf71bfda0bd1d20e420d6792`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `79c5592c6cea7f8fa42895aa10eff8e30997a94bdf71bfda0bd1d20e420d6792`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/03_system/tools/llm/claude_full/components/diff_dialog_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/components/diff_dialog_spec.md (current)
findings: 7 blockers: 0
  narrative=100 structure=90 oracle=90
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/components/diff_dialog_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/components/diff_dialog_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/components/diff_dialog_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/tools/llm/claude_full/components/diff_dialog_spec.spl:18:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should summarize open, loading, empty, and error states' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/components/diff_dialog_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should summarize open, loading, empty, and error states' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/components/diff_dialog_spec.spl:39:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should expose selection, actions, keyboard labels, and source floor' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/components/diff_dialog_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should expose selection, actions, keyboard labels, and source floor' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
