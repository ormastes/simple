# Claude Full CustomSelect Select

> This spec covers the imported Simple parity model for the Claude full CustomSelect single-select component. It verifies user-visible state transitions instead of rendering a placeholder shell.

<!-- sdn-diagram:id=custom_select_select_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=custom_select_select_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

custom_select_select_spec -> std
custom_select_select_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=custom_select_select_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full CustomSelect Select

This spec covers the imported Simple parity model for the Claude full CustomSelect single-select component. It verifies user-visible state transitions instead of rendering a placeholder shell.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Requirements | N/A - direct Claude full parity lane. |
| Plan | N/A - scoped implementation request. |
| Design | N/A - state model mirrors the requested component behavior. |
| Research | N/A - local adjacent CustomSelect parity files used. |
| Source | `test/03_system/tools/llm/claude_full/components/custom_select_select_spec.spl` |
| Updated | 2026-07-05 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

This spec covers the imported Simple parity model for the Claude full
CustomSelect single-select component. It verifies user-visible state transitions
instead of rendering a placeholder shell.

## Examples

The scenarios open the menu, move the highlighted option, select a value, filter
available choices, block disabled choices, block disabled select mutation, and
read the source-line helper used by the parity ledger.

**Requirements:** N/A - direct Claude full parity lane.
**Plan:** N/A - scoped implementation request.
**Design:** N/A - state model mirrors the requested component behavior.
**Research:** N/A - local adjacent CustomSelect parity files used.

## Scenarios

### Claude full CustomSelect select

#### models opening highlighting selecting and closing

- Open selects the first enabled option
- state open menu
   - Expected: state.open is true
   - Expected: state.highlighted_label() equals `Claude Opus`
- Move highlight and select the visible option
- state move highlight
   - Expected: state.highlighted_value() equals `sonnet`
   - Expected: state.select_highlighted() is true
   - Expected: state.open is false
   - Expected: state.selected_value equals `sonnet`
   - Expected: state.display_label() equals `Claude Sonnet`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val state = customSelectFixture()

step("Open selects the first enabled option")
state.open_menu()
expect(state.open).to_equal(true)
expect(state.highlighted_label()).to_equal("Claude Opus")

step("Move highlight and select the visible option")
state.move_highlight(1)
expect(state.highlighted_value()).to_equal("sonnet")
expect(state.select_highlighted()).to_equal(true)
expect(state.open).to_equal(false)
expect(state.selected_value).to_equal("sonnet")
expect(state.display_label()).to_equal("Claude Sonnet")
```

</details>

#### filters options and blocks disabled choices

- Filter by label
- state open menu
- state set filter
   - Expected: state.filtered_count() equals `1`
   - Expected: state.highlighted_label() equals `Claude Sonnet`
- Disabled options cannot be selected
   - Expected: state.select_value("legacy") is false
   - Expected: state.select_value("opus") is true
   - Expected: state.display_label() equals `Claude Opus`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val state = customSelectFixture()

step("Filter by label")
state.open_menu()
state.set_filter("son")
expect(state.filtered_count()).to_equal(1)
expect(state.highlighted_label()).to_equal("Claude Sonnet")

step("Disabled options cannot be selected")
expect(state.select_value("legacy")).to_equal(false)
expect(state.select_value("opus")).to_equal(true)
expect(state.display_label()).to_equal("Claude Opus")
```

</details>

#### models disabled state placeholder and source helper

- Placeholder is shown before selection
   - Expected: state.display_label() equals `Pick a model`
   - Expected: state.option_count() equals `3`
- Disabled select ignores mutations
- state set disabled
- state open menu
- state set filter
   - Expected: state.open is false
   - Expected: state.filtered_count() equals `3`
   - Expected: state.select_value("opus") is false
- Source helper records TypeScript parity floor
   - Expected: customSelectSelectSourceLinesModeled() equals `689`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val state = customSelectFixture()

step("Placeholder is shown before selection")
expect(state.display_label()).to_equal("Pick a model")
expect(state.option_count()).to_equal(3)

step("Disabled select ignores mutations")
state.set_disabled(true)
state.open_menu()
state.set_filter("opus")
expect(state.open).to_equal(false)
expect(state.filtered_count()).to_equal(3)
expect(state.select_value("opus")).to_equal(false)

step("Source helper records TypeScript parity floor")
expect(customSelectSelectSourceLinesModeled()).to_equal(689)
expect(customSelectSelectSourceSummary()).to_contain("single select")
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


## Related Documentation

- **Requirements:** [N/A - direct Claude full parity lane.](N/A - direct Claude full parity lane.)
- **Plan:** [N/A - scoped implementation request.](N/A - scoped implementation request.)
- **Design:** [N/A - state model mirrors the requested component behavior.](N/A - state model mirrors the requested component behavior.)
- **Research:** [N/A - local adjacent CustomSelect parity files used.](N/A - local adjacent CustomSelect parity files used.)


</details>
