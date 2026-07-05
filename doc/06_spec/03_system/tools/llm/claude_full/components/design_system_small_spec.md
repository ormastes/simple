# Claude Full Design System Small Components

> Checks modern SSpec parity for the smaller design-system helper surfaces.

<!-- sdn-diagram:id=design_system_small_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=design_system_small_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

design_system_small_spec -> std
design_system_small_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=design_system_small_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full Design System Small Components

Checks modern SSpec parity for the smaller design-system helper surfaces.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/components/design_system_small_spec.spl` |
| Updated | 2026-07-05 |
| Generator | `simple spipe-docgen` (Simple) |

Checks modern SSpec parity for the smaller design-system helper surfaces.

## Scenarios

### Claude full design-system small components

#### should render shortcut, loading, and pane states

- Render shortcut hints
   - Expected: shortcutHintVisible("Accept", "enter") is true
   - Expected: shortcutHintLabel("Accept", "enter") equals `Accept [Enter]`
   - Expected: shortcutHintAria("", "") equals `shortcut unavailable`
- Render loading state
   - Expected: loadingStateBusy(loading) is true
   - Expected: loadingStateSummary(loading) equals `Loading: Fetching`
   - Expected: loadingStateTone(loading) equals `muted`
- Render pane state
   - Expected: paneVisible(pane) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Render shortcut hints")
expect(shortcutHintVisible("Accept", "enter")).to_equal(true)
expect(shortcutHintLabel("Accept", "enter")).to_equal("Accept [Enter]")
expect(shortcutHintAria("", "")).to_equal("shortcut unavailable")

step("Render loading state")
val loading = LoadingStateView.new(true, "", "Fetching")
expect(loadingStateBusy(loading)).to_equal(true)
expect(loadingStateSummary(loading)).to_equal("Loading: Fetching")
expect(loadingStateTone(loading)).to_equal("muted")

step("Render pane state")
val pane = PaneState.new("Tools", true, true)
expect(paneVisible(pane)).to_equal(true)
expect(paneSummary(pane)).to_contain("compact")
```

</details>

#### should render progress, ratchet, status, and themed box states

- Render progress state
   - Expected: progressBarPercent(5, 10) equals `50`
   - Expected: progressBarLabel(12, 10) equals `100%`
   - Expected: progressBarTone(12, 10) equals `success`
- Render ratchet state
   - Expected: ratchetNext(ratchet) equals `5`
   - Expected: ratchetPrevious(ratchet) equals `2`
   - Expected: ratchetLabel(ratchet) equals `4`
- Render status and themed box state
   - Expected: statusIconGlyph("warning") equals `alert`
   - Expected: statusIconTone("error") equals `red`
   - Expected: themedBoxSummary(box) equals `box-accent outlined p8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Render progress state")
expect(progressBarPercent(5, 10)).to_equal(50)
expect(progressBarLabel(12, 10)).to_equal("100%")
expect(progressBarTone(12, 10)).to_equal("success")

step("Render ratchet state")
val ratchet = RatchetState.new(4, 0, 5, 2)
expect(ratchetNext(ratchet)).to_equal(5)
expect(ratchetPrevious(ratchet)).to_equal(2)
expect(ratchetLabel(ratchet)).to_equal("4")

step("Render status and themed box state")
expect(statusIconGlyph("warning")).to_equal("alert")
expect(statusIconTone("error")).to_equal("red")
val box = ThemedBoxState.new("accent", 12, true)
expect(themedBoxSummary(box)).to_equal("box-accent outlined p8")
```

</details>

#### should update list item state and check modeled source floors

- Render list item state
   - Expected: listItemChecked(toggleListItem(item)) is true
   - Expected: listItemFocusRing(focusListItem(item)) equals `focus-visible`
- Check modeled TypeScript source floors
   - Expected: keyboardShortcutHintSourceLinesModeled() equals `80`
   - Expected: listItemSourceLinesModeled() equals `243`
   - Expected: loadingStateSourceLinesModeled() equals `93`
   - Expected: paneSourceLinesModeled() equals `76`
   - Expected: progressBarSourceLinesModeled() equals `85`
   - Expected: ratchetSourceLinesModeled() equals `79`
   - Expected: statusIconSourceLinesModeled() equals `94`
   - Expected: themedBoxSourceLinesModeled() equals `155`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Render list item state")
val item = ListItemState.new("one", "First", "Primary row", false, false, false)
expect(listItemSummary(item)).to_contain("Primary row")
expect(listItemChecked(toggleListItem(item))).to_equal(true)
expect(listItemFocusRing(focusListItem(item))).to_equal("focus-visible")

step("Check modeled TypeScript source floors")
expect(keyboardShortcutHintSourceLinesModeled()).to_equal(80)
expect(listItemSourceLinesModeled()).to_equal(243)
expect(loadingStateSourceLinesModeled()).to_equal(93)
expect(paneSourceLinesModeled()).to_equal(76)
expect(progressBarSourceLinesModeled()).to_equal(85)
expect(ratchetSourceLinesModeled()).to_equal(79)
expect(statusIconSourceLinesModeled()).to_equal(94)
expect(themedBoxSourceLinesModeled()).to_equal(155)
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
