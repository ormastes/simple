# Claude Full CustomSelect useSelectNavigation

> Checks real navigation parity for wrapping, disabled options, home/end, empty lists, and source helpers.

<!-- sdn-diagram:id=custom_select_navigation_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=custom_select_navigation_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

custom_select_navigation_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=custom_select_navigation_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full CustomSelect useSelectNavigation

Checks real navigation parity for wrapping, disabled options, home/end, empty lists, and source helpers.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/components/custom_select_navigation_spec.spl` |
| Updated | 2026-07-05 |
| Generator | `simple spipe-docgen` (Simple) |

Checks real navigation parity for wrapping, disabled options, home/end, empty lists, and source helpers.

## Scenarios

### Claude full CustomSelect useSelectNavigation

#### wraps next and previous while skipping disabled options

- Navigate over the sample list
   - Expected: nextSelectNavigationIndex(options, 0) equals `2`
   - Expected: nextSelectNavigationIndex(options, 2) equals `4`
   - Expected: nextSelectNavigationIndex(options, 4) equals `0`
   - Expected: previousSelectNavigationIndex(options, 0) equals `4`
   - Expected: previousSelectNavigationIndex(options, 4) equals `2`
   - Expected: previousSelectNavigationIndex(options, 2) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Navigate over the sample list")
val options = sampleSelectNavigationOptions()
expect(nextSelectNavigationIndex(options, 0)).to_equal(2)
expect(nextSelectNavigationIndex(options, 2)).to_equal(4)
expect(nextSelectNavigationIndex(options, 4)).to_equal(0)
expect(previousSelectNavigationIndex(options, 0)).to_equal(4)
expect(previousSelectNavigationIndex(options, 4)).to_equal(2)
expect(previousSelectNavigationIndex(options, 2)).to_equal(0)
```

</details>

#### uses home and end for first and last enabled options

- Resolve boundary navigation
   - Expected: homeSelectNavigationIndex(options) equals `0`
   - Expected: endSelectNavigationIndex(options) equals `4`
   - Expected: firstEnabledSelectNavigationIndex(options) equals `0`
   - Expected: lastEnabledSelectNavigationIndex(options) equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Resolve boundary navigation")
val options = sampleSelectNavigationOptions()
expect(homeSelectNavigationIndex(options)).to_equal(0)
expect(endSelectNavigationIndex(options)).to_equal(4)
expect(firstEnabledSelectNavigationIndex(options)).to_equal(0)
expect(lastEnabledSelectNavigationIndex(options)).to_equal(4)
```

</details>

#### handles empty and all-disabled option lists

- Return no active index for empty data
   - Expected: nextSelectNavigationIndex(empty, 0) equals `-1`
   - Expected: previousSelectNavigationIndex(empty, 0) equals `-1`
   - Expected: homeSelectNavigationIndex(empty) equals `-1`
   - Expected: endSelectNavigationIndex(empty) equals `-1`
   - Expected: selectNavigationValueAt(empty, 0) equals ``
- Return no active index when every option is disabled
   - Expected: nextSelectNavigationIndex(disabled, 0) equals `-1`
   - Expected: previousSelectNavigationIndex(disabled, 1) equals `-1`
   - Expected: createSelectNavigationState(disabled, "a").isEmpty() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Return no active index for empty data")
val empty: [SelectNavigationOption] = []
expect(nextSelectNavigationIndex(empty, 0)).to_equal(-1)
expect(previousSelectNavigationIndex(empty, 0)).to_equal(-1)
expect(homeSelectNavigationIndex(empty)).to_equal(-1)
expect(endSelectNavigationIndex(empty)).to_equal(-1)
expect(selectNavigationValueAt(empty, 0)).to_equal("")

step("Return no active index when every option is disabled")
val disabled = [SelectNavigationOption.unavailable("a", "A"), SelectNavigationOption.unavailable("b", "B")]
expect(nextSelectNavigationIndex(disabled, 0)).to_equal(-1)
expect(previousSelectNavigationIndex(disabled, 1)).to_equal(-1)
expect(createSelectNavigationState(disabled, "a").isEmpty()).to_equal(true)
```

</details>

#### creates state from values and normalizes disabled selections

- Keep enabled values and fall back from disabled ones
   - Expected: selected.activeIndex equals `2`
   - Expected: selected.activeValue() equals `gamma`
   - Expected: selected.next().activeValue() equals `epsilon`
   - Expected: selected.previous().activeValue() equals `alpha`
   - Expected: createSelectNavigationState(options, "beta").activeIndex equals `0`
   - Expected: selectNavigationIndexByValue(options, "missing") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Keep enabled values and fall back from disabled ones")
val options = sampleSelectNavigationOptions()
val selected = createSelectNavigationState(options, "gamma")
expect(selected.activeIndex).to_equal(2)
expect(selected.activeValue()).to_equal("gamma")
expect(selected.next().activeValue()).to_equal("epsilon")
expect(selected.previous().activeValue()).to_equal("alpha")
expect(createSelectNavigationState(options, "beta").activeIndex).to_equal(0)
expect(selectNavigationIndexByValue(options, "missing")).to_equal(0)
```

</details>

#### exports source helper parity

- Pin upstream source helpers
   - Expected: useSelectNavigationModeledSourceFile() equals `src/components/CustomSelect/use-select-navigation.ts`
   - Expected: useSelectNavigationModeledHookName() equals `useSelectNavigation`
   - Expected: useSelectNavigationModeledSourceHelper() equals `getNextSelectableOption`
   - Expected: useSelectNavigationSourceLinesModeled() equals `653`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Pin upstream source helpers")
expect(useSelectNavigationModeledSourceFile()).to_equal("src/components/CustomSelect/use-select-navigation.ts")
expect(useSelectNavigationModeledHookName()).to_equal("useSelectNavigation")
expect(useSelectNavigationModeledSourceHelper()).to_equal("getNextSelectableOption")
expect(useSelectNavigationSourceLinesModeled()).to_equal(653)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
