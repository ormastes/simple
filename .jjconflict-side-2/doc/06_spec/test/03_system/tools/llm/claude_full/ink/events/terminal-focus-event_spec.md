# Claude Full Terminal Focus Event

> Mirrors the terminal focus/blur event emitted from DECSET 1004 focus reporting.

<!-- sdn-diagram:id=terminal-focus-event_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=terminal-focus-event_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

terminal-focus-event_spec -> std
terminal-focus-event_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=terminal-focus-event_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full Terminal Focus Event

Mirrors the terminal focus/blur event emitted from DECSET 1004 focus reporting.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/ink/events/terminal-focus-event_spec.spl` |
| Updated | 2026-07-05 |
| Generator | `simple spipe-docgen` (Simple) |

Mirrors the terminal focus/blur event emitted from DECSET 1004 focus reporting.

## Scenarios

### Claude full terminal focus event

#### should preserve terminal focus and blur types

- Create focus and blur events
- Check the event type helpers
   - Expected: focus.type equals `terminalfocus`
   - Expected: focus.isFocus() is true
   - Expected: focus.isBlur() is false
   - Expected: blur.type equals `terminalblur`
   - Expected: blur.isFocus() is false
   - Expected: blur.isBlur() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Create focus and blur events")
val focus = terminalFocusEventNew("terminalfocus")
val blur = terminalFocusEventNew("terminalblur")

step("Check the event type helpers")
expect(focus.type).to_equal("terminalfocus")
expect(focus.isFocus()).to_equal(true)
expect(focus.isBlur()).to_equal(false)
expect(blur.type).to_equal("terminalblur")
expect(blur.isFocus()).to_equal(false)
expect(blur.isBlur()).to_equal(true)
```

</details>

#### should inherit immediate propagation stop behavior

- Create a focus event and stop immediate propagation
   - Expected: event.didStopImmediatePropagation() is false
- event stopImmediatePropagation
   - Expected: event.didStopImmediatePropagation() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Create a focus event and stop immediate propagation")
val event = terminalFocusEventNew("terminalfocus")
expect(event.didStopImmediatePropagation()).to_equal(false)
event.stopImmediatePropagation()
expect(event.didStopImmediatePropagation()).to_equal(true)
```

</details>

#### should normalize unknown terminal focus input to focus

- Normalize a defensive fallback value
   - Expected: normalizeTerminalFocusEventType("other") equals `terminalfocus`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Normalize a defensive fallback value")
expect(normalizeTerminalFocusEventType("other")).to_equal("terminalfocus")
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
