# Claude Full Focus Event

> Mirrors Ink focus and blur events: bubbling, non-cancelable, and carrying the

<!-- sdn-diagram:id=focus-event_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=focus-event_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

focus-event_spec -> std
focus-event_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=focus-event_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full Focus Event

Mirrors Ink focus and blur events: bubbling, non-cancelable, and carrying the

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/ink/events/focus-event_spec.spl` |
| Updated | 2026-07-05 |
| Generator | `simple spipe-docgen` (Simple) |

Mirrors Ink focus and blur events: bubbling, non-cancelable, and carrying the
related target from the previous or next focused element.

## Scenarios

### Claude full focus event

#### should preserve focus and blur event types with related target

- Create focus and blur events
   - Expected: focus.type equals `focus`
   - Expected: focus.relatedTarget equals `previous-node`
   - Expected: focus.isFocus() is true
   - Expected: focus.isBlur() is false
   - Expected: blur.type equals `blur`
   - Expected: blur.relatedTarget equals `next-node`
   - Expected: blur.isFocus() is false
   - Expected: blur.isBlur() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Create focus and blur events")
val focus = focusEventNew("focus", "previous-node")
val blur = focusEventNew("blur", "next-node")
expect(focus.type).to_equal("focus")
expect(focus.relatedTarget).to_equal("previous-node")
expect(focus.isFocus()).to_equal(true)
expect(focus.isBlur()).to_equal(false)
expect(blur.type).to_equal("blur")
expect(blur.relatedTarget).to_equal("next-node")
expect(blur.isFocus()).to_equal(false)
expect(blur.isBlur()).to_equal(true)
```

</details>

#### should bubble but remain non-cancelable

- Create a focus event and try to prevent default
   - Expected: event.bubbles is true
   - Expected: event.cancelable is false
- event preventDefault
   - Expected: event.defaultPrevented is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Create a focus event and try to prevent default")
val event = focusEventNew("focus", "")
expect(event.bubbles).to_equal(true)
expect(event.cancelable).to_equal(false)
event.preventDefault()
expect(event.defaultPrevented).to_equal(false)
```

</details>

#### should normalize unknown focus input and stop immediate propagation

- Normalize a defensive event type and stop propagation
   - Expected: normalizeFocusEventType("other") equals `focus`
   - Expected: event.didStopImmediatePropagation() is false
- event stopImmediatePropagation
   - Expected: event.didStopImmediatePropagation() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Normalize a defensive event type and stop propagation")
expect(normalizeFocusEventType("other")).to_equal("focus")
val event = focusEventNew("other", "")
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
