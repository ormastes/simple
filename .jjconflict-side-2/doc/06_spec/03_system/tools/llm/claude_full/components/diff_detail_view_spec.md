# Claude Full DiffDetailView Component

> Checks diff detail file headers, hunk rendering, line numbering, selection,

<!-- sdn-diagram:id=diff_detail_view_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=diff_detail_view_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

diff_detail_view_spec -> std
diff_detail_view_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=diff_detail_view_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full DiffDetailView Component

Checks diff detail file headers, hunk rendering, line numbering, selection,

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/components/diff_detail_view_spec.spl` |
| Updated | 2026-07-05 |
| Generator | `simple spipe-docgen` (Simple) |

Checks diff detail file headers, hunk rendering, line numbering, selection,
collapse state, and empty/loading/error summaries.

## Scenarios

### Claude full DiffDetailView component

#### should render file header, hunks, additions, and deletions

- Render sample diff detail
   - Expected: model.file.additions() equals `3`
   - Expected: model.file.deletions() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Render sample diff detail")
val model = sampleDiffDetailView()
val output = model.render()

expect(output).to_contain("Diff detail | src/app/App.spl | Modified | +3 -2 | simple")
expect(output).to_contain("Hunks 1/2 | expanded 1/2")
expect(output).to_contain("> [-] @@ -1,3 +1,4 @@ +2 -1 context 2")
expect(output).to_contain("+new line")
expect(output).to_contain("-old line")
expect(output).to_contain("collapsed 3 lines")
expect(model.file.additions()).to_equal(3)
expect(model.file.deletions()).to_equal(2)
```

</details>

#### should navigate selected hunks and toggle expansion

- Move selected hunk and collapse it
   - Expected: next.state.selectedHunkIndex equals `1`
   - Expected: diffDetailHunkExpanded(opened.file, 1) is true
   - Expected: previous.state.selectedHunkIndex equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Move selected hunk and collapse it")
val model = sampleDiffDetailView()
val next = handleDiffDetailKey(model.file, model.state, "j")
expect(next.state.selectedHunkIndex).to_equal(1)

val opened = handleDiffDetailKey(next.file, next.state, "enter")
expect(diffDetailHunkExpanded(opened.file, 1)).to_equal(true)
expect(opened.render()).to_contain("> [-] @@ -20,2 +21,2 @@")

val previous = handleDiffDetailKey(opened.file, opened.state, "k")
expect(previous.state.selectedHunkIndex).to_equal(0)
```

</details>

#### should expose collapse helpers and state summaries

- Collapse and expand all hunks
   - Expected: collapsed.expandedCount() equals `0`
   - Expected: expanded.expandedCount() equals `2`
- Render empty, loading, and error summaries
   - Expected: renderDiffDetailView(emptyFile, DiffDetailViewState.ready()) equals `No diff hunks for README.md`
   - Expected: renderDiffDetailView(emptyFile, DiffDetailViewState.loading("patch")) equals `Loading diff detail: patch`
   - Expected: renderDiffDetailView(emptyFile, DiffDetailViewState.error("missing patch")) equals `Diff detail error: missing patch`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Collapse and expand all hunks")
val model = sampleDiffDetailView()
val collapsed = collapseAllDiffDetailHunks(model.file)
expect(collapsed.expandedCount()).to_equal(0)
val expanded = expandAllDiffDetailHunks(collapsed)
expect(expanded.expandedCount()).to_equal(2)

step("Render empty, loading, and error summaries")
val emptyHunks: [DiffDetailHunk] = []
val emptyFile = DiffDetailFile.fromPath("README.md", "modified", emptyHunks)
expect(renderDiffDetailView(emptyFile, DiffDetailViewState.ready())).to_equal("No diff hunks for README.md")
expect(renderDiffDetailView(emptyFile, DiffDetailViewState.loading("patch"))).to_equal("Loading diff detail: patch")
expect(renderDiffDetailView(emptyFile, DiffDetailViewState.error("missing patch"))).to_equal("Diff detail error: missing patch")
```

</details>

#### should expose source parity helpers

- Pin modeled source helper names
   - Expected: diffDetailModeledSourceFile() equals `src/components/diff/DiffDetailView.tsx`
   - Expected: diffDetailModeledStateHelper() equals `useDiffDetailViewState`
   - Expected: diffDetailModeledHunkHelper() equals `renderDiffHunk`
   - Expected: diffDetailModeledLineHelper() equals `renderDiffLine`
   - Expected: diffDetailSourceLinesModeled() equals `280`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Pin modeled source helper names")
expect(diffDetailModeledSourceFile()).to_equal("src/components/diff/DiffDetailView.tsx")
expect(diffDetailModeledStateHelper()).to_equal("useDiffDetailViewState")
expect(diffDetailModeledHunkHelper()).to_equal("renderDiffHunk")
expect(diffDetailModeledLineHelper()).to_equal("renderDiffLine")
expect(diffDetailSourceLinesModeled()).to_equal(280)
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
