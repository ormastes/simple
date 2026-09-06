# Claude Full Keyboard Event

> Mirrors Ink keyboard events as DOM-like keydown payloads.

<!-- sdn-diagram:id=keyboard-event_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=keyboard-event_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

keyboard-event_spec -> std
keyboard-event_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=keyboard-event_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full Keyboard Event

Mirrors Ink keyboard events as DOM-like keydown payloads.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/ink/events/keyboard-event_spec.spl` |
| Updated | 2026-07-05 |
| Generator | `simple spipe-docgen` (Simple) |

Mirrors Ink keyboard events as DOM-like keydown payloads.

## Scenarios

### Claude full keyboard event

#### should expose keydown event defaults

- Create an event from a printable key
   - Expected: event.type equals `keydown`
   - Expected: event.bubbles is true
   - Expected: event.cancelable is true
   - Expected: event.key equals `a`
   - Expected: event.printableChar() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Create an event from a printable key")
val parsed = parsedKeyboardKeyNew("", "a")
val event = keyboardEventNew(parsed)
expect(event.type).to_equal("keydown")
expect(event.bubbles).to_equal(true)
expect(event.cancelable).to_equal(true)
expect(event.key).to_equal("a")
expect(event.printableChar()).to_equal(true)
```

</details>

#### should use parsed names for ctrl combinations

- Create a ctrl+c event whose sequence is a control byte
   - Expected: event.key equals `c`
   - Expected: event.ctrl is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Create a ctrl+c event whose sequence is a control byte")
val parsed = parsedKeyboardKeyNew("c", "\u0003")
parsed.ctrl = true
val event = keyboardEventNew(parsed)
expect(event.key).to_equal("c")
expect(event.ctrl).to_equal(true)
```

</details>

#### should use parsed names for terminal escape sequences

- Create an arrow-key event from a terminal sequence
   - Expected: event.key equals `down`
   - Expected: event.printableChar() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Create an arrow-key event from a terminal sequence")
val parsed = parsedKeyboardKeyNew("down", "\u001B[B")
val event = keyboardEventNew(parsed)
expect(event.key).to_equal("down")
expect(event.printableChar()).to_equal(false)
```

</details>

#### should propagate option as meta and preserve super and function flags

- Create an event with terminal modifier flags
   - Expected: event.meta is true
   - Expected: event.superKey is true
   - Expected: event.functionKey is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Create an event with terminal modifier flags")
val parsed = parsedKeyboardKeyNew("f1", "\u001BOP")
parsed.option = true
parsed.superKey = true
parsed.functionKey = true
val event = keyboardEventNew(parsed)
expect(event.meta).to_equal(true)
expect(event.superKey).to_equal(true)
expect(event.functionKey).to_equal(true)
```

</details>

#### should stop immediate propagation

- Stop propagation on the keyboard event
   - Expected: event.didStopImmediatePropagation() is false
- event stopImmediatePropagation
   - Expected: event.didStopImmediatePropagation() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Stop propagation on the keyboard event")
val parsed = parsedKeyboardKeyNew("return", "\r")
val event = keyboardEventNew(parsed)
expect(event.didStopImmediatePropagation()).to_equal(false)
event.stopImmediatePropagation()
expect(event.didStopImmediatePropagation()).to_equal(true)
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
