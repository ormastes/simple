# Claude Full Context and Custom Select Components

> Checks modern SSpec parity for context suggestions and select controls.

<!-- sdn-diagram:id=context_custom_select_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=context_custom_select_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

context_custom_select_spec -> std
context_custom_select_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=context_custom_select_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full Context and Custom Select Components

Checks modern SSpec parity for context suggestions and select controls.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/components/context_custom_select_spec.spl` |
| Updated | 2026-07-05 |
| Generator | `simple spipe-docgen` (Simple) |

Checks modern SSpec parity for context suggestions and select controls.

## Scenarios

### Claude full context and custom select components

#### should render context and threshold helpers

- Render context suggestions
   - Expected: contextSuggestionVisible("README.md") is true
- Render cost and expand helpers
   - Expected: costThresholdExceeded(10.0, 10.0) is true
   - Expected: ctrlOToExpandVisible(true) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Render context suggestions")
expect(contextSuggestionVisible("README.md")).to_equal(true)
expect(contextSuggestionLabel("README.md")).to_contain("README.md")

step("Render cost and expand helpers")
expect(costThresholdExceeded(10.0, 10.0)).to_equal(true)
expect(costThresholdMessage(1.0, 10.0)).to_contain("below")
expect(ctrlOToExpandVisible(true)).to_equal(true)
expect(ctrlOToExpandLabel(false)).to_contain("expand")
```

</details>

#### should render custom select options

- Map a select option
   - Expected: optionLabel(option) equals `v1`
- Render input option state
   - Expected: selectInputOptionCanChoose(state) is true
- Render multi-select state
   - Expected: selectMultiCanClear(["a"]) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Map a select option")
val option = SelectOption.new("v1", "")
expect(optionLabel(option)).to_equal("v1")

step("Render input option state")
val state = SelectInputOptionState.new("v1", "Version 1", true, false)
expect(selectInputOptionDisplay(state)).to_contain("[x]")
expect(selectInputOptionCanChoose(state)).to_equal(true)

step("Render multi-select state")
expect(selectMultiSummary([])).to_contain("No options")
expect(selectMultiSummary(["a", "b"])).to_contain("2")
expect(selectMultiCanClear(["a"])).to_equal(true)
```

</details>

#### should check modeled TypeScript source floors

- Read source line helpers
   - Expected: contextSuggestionsSourceLinesModeled() equals `46`
   - Expected: costThresholdDialogSourceLinesModeled() equals `49`
   - Expected: ctrlOToExpandSourceLinesModeled() equals `50`
   - Expected: customSelectIndexSourceLinesModeled() equals `3`
   - Expected: optionMapSourceLinesModeled() equals `50`
   - Expected: selectInputOptionSourceLinesModeled() equals `487`
   - Expected: selectMultiSourceLinesModeled() equals `212`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Read source line helpers")
expect(contextSuggestionsSourceLinesModeled()).to_equal(46)
expect(costThresholdDialogSourceLinesModeled()).to_equal(49)
expect(ctrlOToExpandSourceLinesModeled()).to_equal(50)
expect(customSelectIndexSourceLinesModeled()).to_equal(3)
expect(optionMapSourceLinesModeled()).to_equal(50)
expect(selectInputOptionSourceLinesModeled()).to_equal(487)
expect(selectMultiSourceLinesModeled()).to_equal(212)
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
