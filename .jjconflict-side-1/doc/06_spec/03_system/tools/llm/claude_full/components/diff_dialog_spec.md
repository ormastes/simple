# Claude Full DiffDialog

> Focused parity checks for the Claude full diff dialog helper state.

<!-- sdn-diagram:id=diff_dialog_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=diff_dialog_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

diff_dialog_spec -> std
diff_dialog_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=diff_dialog_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

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
| Updated | 2026-07-05 |
| Generator | `simple spipe-docgen` (Simple) |

Focused parity checks for the Claude full diff dialog helper state.

## Scenarios

### Claude full DiffDialog component

#### should summarize open, loading, empty, and error states

<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
