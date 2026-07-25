# Claude Full Click Event

> Mirrors the Ink mouse click event payload and immediate propagation flag.

<!-- sdn-diagram:id=click-event_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=click-event_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

click-event_spec -> std
click-event_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=click-event_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full Click Event

Mirrors the Ink mouse click event payload and immediate propagation flag.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/ink/events/click-event_spec.spl` |
| Updated | 2026-07-05 |
| Generator | `simple spipe-docgen` (Simple) |

Mirrors the Ink mouse click event payload and immediate propagation flag.

## Scenarios

### Claude full click event

#### should preserve screen coordinates and blank-cell state

- Create a click event at absolute screen coordinates
   - Expected: event.col equals `12`
   - Expected: event.row equals `7`
   - Expected: event.localCol equals `0`
   - Expected: event.localRow equals `0`
   - Expected: event.isBlankCellClick() is true
   - Expected: event.positionText() equals `12,7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Create a click event at absolute screen coordinates")
val event = clickEventNew(12, 7, true)
expect(event.col).to_equal(12)
expect(event.row).to_equal(7)
expect(event.localCol).to_equal(0)
expect(event.localRow).to_equal(0)
expect(event.isBlankCellClick()).to_equal(true)
expect(event.positionText()).to_equal("12,7")
```

</details>

#### should recompute local coordinates for each handler box

- Compute coordinates relative to a parent box
- event setLocalFromBox
   - Expected: event.localCol equals `2`
   - Expected: event.localRow equals `4`
   - Expected: event.isBlankCellClick() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Compute coordinates relative to a parent box")
val event = clickEventNew(12, 7, false)
event.setLocalFromBox(10, 3)
expect(event.localCol).to_equal(2)
expect(event.localRow).to_equal(4)
expect(event.isBlankCellClick()).to_equal(false)
```

</details>

#### should stop immediate propagation like the base event

- Stop bubbling to ancestor click handlers
   - Expected: event.didStopImmediatePropagation() is false
- event stopImmediatePropagation
   - Expected: event.didStopImmediatePropagation() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Stop bubbling to ancestor click handlers")
val event = clickEventNew(1, 2, false)
expect(event.didStopImmediatePropagation()).to_equal(false)
event.stopImmediatePropagation()
expect(event.didStopImmediatePropagation()).to_equal(true)
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
