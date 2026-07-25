# Claude Full Terminal Event

> Mirrors DOM-style terminal event propagation state.

<!-- sdn-diagram:id=terminal-event_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=terminal-event_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

terminal-event_spec -> std
terminal-event_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=terminal-event_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full Terminal Event

Mirrors DOM-style terminal event propagation state.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/ink/events/terminal-event_spec.spl` |
| Updated | 2026-07-05 |
| Generator | `simple spipe-docgen` (Simple) |

Mirrors DOM-style terminal event propagation state.

## Scenarios

### Claude full terminal event

#### should default to bubbling cancelable none-phase events

- Create a base terminal event
   - Expected: event.type equals `keydown`
   - Expected: event.bubbles is true
   - Expected: event.cancelable is true
   - Expected: event.eventPhase equals `none`
   - Expected: event.defaultPrevented is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Create a base terminal event")
val event = terminalEventNew("keydown")
expect(event.type).to_equal("keydown")
expect(event.bubbles).to_equal(true)
expect(event.cancelable).to_equal(true)
expect(event.eventPhase).to_equal("none")
expect(event.defaultPrevented).to_equal(false)
```

</details>

#### should honor explicit init flags

- Create a non-bubbling non-cancelable event
- event preventDefault
   - Expected: event.bubbles is false
   - Expected: event.cancelable is false
   - Expected: event.defaultPrevented is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Create a non-bubbling non-cancelable event")
val event = terminalEventWithInit("focus", false, false)
event.preventDefault()
expect(event.bubbles).to_equal(false)
expect(event.cancelable).to_equal(false)
expect(event.defaultPrevented).to_equal(false)
```

</details>

#### should prevent defaults only when cancelable

- Create a cancelable event and prevent its default
- event preventDefault
   - Expected: event.defaultPrevented is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Create a cancelable event and prevent its default")
val event = terminalEventWithInit("input", true, true)
event.preventDefault()
expect(event.defaultPrevented).to_equal(true)
```

</details>

#### should track targets and event phases

- Move an event through capture and target phases
- event setTarget
- event setCurrentTarget
- event setEventPhase
   - Expected: event.target equals `leaf`
   - Expected: event.currentTarget equals `parent`
   - Expected: event.phaseIsCapturing() is true
- event setEventPhase
   - Expected: event.phaseIsAtTarget() is true
- event clearCurrentTarget
   - Expected: event.currentTarget equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Move an event through capture and target phases")
val event = terminalEventNew("click")
event.setTarget("leaf")
event.setCurrentTarget("parent")
event.setEventPhase("capturing")
expect(event.target).to_equal("leaf")
expect(event.currentTarget).to_equal("parent")
expect(event.phaseIsCapturing()).to_equal(true)
event.setEventPhase("at_target")
expect(event.phaseIsAtTarget()).to_equal(true)
event.clearCurrentTarget()
expect(event.currentTarget).to_equal("")
```

</details>

#### should stop propagation and immediate propagation

- Stop normal propagation
- event stopPropagation
   - Expected: event.isPropagationStopped() is true
   - Expected: event.isImmediatePropagationStopped() is false
- event stopImmediatePropagation
   - Expected: event.isImmediatePropagationStopped() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Stop normal propagation")
val event = terminalEventNew("keydown")
event.stopPropagation()
expect(event.isPropagationStopped()).to_equal(true)
expect(event.isImmediatePropagationStopped()).to_equal(false)
event.stopImmediatePropagation()
expect(event.isImmediatePropagationStopped()).to_equal(true)
```

</details>

#### should normalize invalid phases and prepare per target

- Normalize a defensive phase input
   - Expected: normalizeEventPhase("other") equals `none`
- event setEventPhase
- event prepareForTarget
   - Expected: event.phaseIsBubbling() is true
   - Expected: event.preparedTarget equals `child`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Normalize a defensive phase input")
expect(normalizeEventPhase("other")).to_equal("none")
val event = terminalEventNew("keydown")
event.setEventPhase("bubbling")
event.prepareForTarget("child")
expect(event.phaseIsBubbling()).to_equal(true)
expect(event.preparedTarget).to_equal("child")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
