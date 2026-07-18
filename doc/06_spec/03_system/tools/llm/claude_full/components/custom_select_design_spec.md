# Claude Full Custom Select and Design System Components

> Checks modern SSpec parity for select state and design-system helpers.

<!-- sdn-diagram:id=custom_select_design_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=custom_select_design_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

custom_select_design_spec -> std
custom_select_design_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=custom_select_design_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full Custom Select and Design System Components

Checks modern SSpec parity for select state and design-system helpers.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/components/custom_select_design_spec.spl` |
| Updated | 2026-07-05 |
| Generator | `simple spipe-docgen` (Simple) |

Checks modern SSpec parity for select state and design-system helpers.

## Scenarios

### Claude full custom select design components

#### should render select option and input state

- Render option row
- Update input query
   - Expected: updateSelectInputQuery(input, "ver").open is true
   - Expected: clearSelectInput(updateSelectInputQuery(input, "ver")).query equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Render option row")
val row = SelectOptionRow.new("v1", "Version 1", true)
expect(selectOptionRowLabel(row)).to_contain("Version 1")

step("Update input query")
val input = SelectInputState.new("", false)
expect(updateSelectInputQuery(input, "ver").open).to_equal(true)
expect(selectInputSummary(updateSelectInputQuery(input, "ver"))).to_contain("ver")
expect(clearSelectInput(updateSelectInputQuery(input, "ver")).query).to_equal("")
```

</details>

#### should render select state and design helpers

- Choose select state
   - Expected: openSelectState(state).open is true
   - Expected: chooseSelectState(state, "v1").selected equals `v1`
- Render design-system helpers
   - Expected: bylineVisible("Claude") is true
   - Expected: designColorToken("Accent") equals `color.accent`
   - Expected: dialogVisible(dialog) is true
   - Expected: dialogHeader(dialog) equals `Settings`
   - Expected: dividerLine(3) equals `---`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Choose select state")
val state = SelectState.new(false, "")
expect(openSelectState(state).open).to_equal(true)
expect(chooseSelectState(state, "v1").selected).to_equal("v1")
expect(selectStateSummary(chooseSelectState(state, "v1"))).to_contain("v1")

step("Render design-system helpers")
expect(bylineVisible("Claude")).to_equal(true)
expect(bylineText("Claude", "Code")).to_contain("Code")
expect(designColorToken("Accent")).to_equal("color.accent")
val dialog = DialogState.new("Settings", true)
expect(dialogVisible(dialog)).to_equal(true)
expect(dialogHeader(dialog)).to_equal("Settings")
expect(dividerLine(3)).to_equal("---")
```

</details>

#### should check modeled TypeScript source floors

- Read source line helpers
   - Expected: selectOptionSourceLinesModeled() equals `67`
   - Expected: useSelectInputSourceLinesModeled() equals `287`
   - Expected: useSelectStateSourceLinesModeled() equals `157`
   - Expected: bylineSourceLinesModeled() equals `76`
   - Expected: colorSourceLinesModeled() equals `30`
   - Expected: dialogSourceLinesModeled() equals `137`
   - Expected: dividerSourceLinesModeled() equals `148`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Read source line helpers")
expect(selectOptionSourceLinesModeled()).to_equal(67)
expect(useSelectInputSourceLinesModeled()).to_equal(287)
expect(useSelectStateSourceLinesModeled()).to_equal(157)
expect(bylineSourceLinesModeled()).to_equal(76)
expect(colorSourceLinesModeled()).to_equal(30)
expect(dialogSourceLinesModeled()).to_equal(137)
expect(dividerSourceLinesModeled()).to_equal(148)
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
