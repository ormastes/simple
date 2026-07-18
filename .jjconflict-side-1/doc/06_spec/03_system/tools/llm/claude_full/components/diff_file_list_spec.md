# Claude Full DiffFileList Component

> Checks modern SSpec parity for diff file list filtering, navigation, and rendering.

<!-- sdn-diagram:id=diff_file_list_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=diff_file_list_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

diff_file_list_spec -> std
diff_file_list_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=diff_file_list_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full DiffFileList Component

Checks modern SSpec parity for diff file list filtering, navigation, and rendering.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/components/diff_file_list_spec.spl` |
| Updated | 2026-07-05 |
| Generator | `simple spipe-docgen` (Simple) |

Checks modern SSpec parity for diff file list filtering, navigation, and rendering.

## Scenarios

### Claude full DiffFileList component

#### should filter and render changed files

- Create sample diff file list
   - Expected: visible.len() equals `1`
   - Expected: visible[0].path equals `src/app/App.spl`
- Render filtered rows


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Create sample diff file list")
val files = sampleDiffFileItems()
val state = DiffFileListState.new("app", "modified", "", false)
val visible = visibleDiffFiles(files, state)
expect(visible.len()).to_equal(1)
expect(visible[0].path).to_equal("src/app/App.spl")

step("Render filtered rows")
val output = renderDiffFileList(files, state)
expect(output).to_contain("Diff files")
expect(output).to_contain("src/app/App.spl")
expect(output).to_contain("+12 -3")
```

</details>

#### should handle keyboard navigation and grouped summaries

- Navigate through diff files
   - Expected: handleDiffFileListKey(files, state, "down").selectedPath equals `src/app/App.spl`
   - Expected: handleDiffFileListKey(files, state, "end").selectedPath equals `test/old_spec.spl`
- Render grouped file list


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Navigate through diff files")
val files = sampleDiffFileItems()
val state = DiffFileListState.new("", "all", "README.md", true)
expect(handleDiffFileListKey(files, state, "down").selectedPath).to_equal("src/app/App.spl")
expect(handleDiffFileListKey(files, state, "end").selectedPath).to_equal("test/old_spec.spl")

step("Render grouped file list")
val grouped = renderDiffFileList(files, state)
expect(grouped).to_contain("[src/app]")
expect(grouped).to_contain("grouped")
```

</details>

#### should expose empty state and modeled source floor

- Render empty states
   - Expected: renderDiffFileList(emptyFiles, DiffFileListState.empty()) equals `No changed files`
- Check modeled TypeScript source floor
   - Expected: diffFileListSourceLinesModeled() equals `291`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Render empty states")
val emptyFiles: [DiffFileItem] = []
expect(renderDiffFileList(emptyFiles, DiffFileListState.empty())).to_equal("No changed files")
expect(renderDiffFileList(emptyFiles, DiffFileListState.new("missing", "added", "", false))).to_contain("missing")

step("Check modeled TypeScript source floor")
expect(diffFileListSourceLinesModeled()).to_equal(291)
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
