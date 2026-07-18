# Claude Full CustomSelect Multi State

> Checks source-backed parity for the hyphenated use-multi-select-state file.

<!-- sdn-diagram:id=custom_select_multi_state_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=custom_select_multi_state_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

custom_select_multi_state_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=custom_select_multi_state_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full CustomSelect Multi State

Checks source-backed parity for the hyphenated use-multi-select-state file.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/components/custom_select_multi_state_spec.spl` |
| Updated | 2026-07-05 |
| Generator | `simple spipe-docgen` (Simple) |

Checks source-backed parity for the hyphenated use-multi-select-state file.

## Scenarios

### Claude full custom select multi state

#### keeps the requested hyphenated parity file at the source floor

- Check exact path and minimum LOC
   - Expected: file_exists("src/app/llm_caret/claude_full/components/CustomSelect/use-multi-select-state.spl") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Check exact path and minimum LOC")
expect(file_exists("src/app/llm_caret/claude_full/components/CustomSelect/use-multi-select-state.spl")).to_equal(true)
expect(multiSelectStateSourceLineCount()).to_be_greater_than(413)
```

</details>

#### models selected values and mutation helpers in the source

- Check real state surface symbols


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Check real state surface symbols")
val source = multiSelectStateSourceText()
expect(source).to_contain("class MultiSelectState:")
expect(source).to_contain("selectedValues: [text]")
expect(source).to_contain("fn useMultiSelectState(initialSelected: [text], maxSelection: i64, source: text) -> MultiSelectState:")
expect(source).to_contain("fn add(value: text) -> MultiSelectState:")
expect(source).to_contain("fn remove(value: text) -> MultiSelectState:")
expect(source).to_contain("fn toggle(value: text) -> MultiSelectState:")
expect(source).to_contain("fn clear() -> MultiSelectState:")
```

</details>

#### models max selection and summary/source helpers in the source

- Check behavior gates and helper names


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Check behavior gates and helper names")
val source = multiSelectStateSourceText()
expect(source).to_contain("if self.maxSelection > 0 and self.selectedValues.len() >= self.maxSelection:")
expect(source).to_contain("fn multiSelectSummary(values: [text], maxSelection: i64) -> text:")
expect(source).to_contain("fn multiSelectSourceSummary(source: text, values: [text], maxSelection: i64) -> text:")
expect(source).to_contain("fn multiSelectSourceLinesModeled() -> i64:")
expect(source).to_contain("414")
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
