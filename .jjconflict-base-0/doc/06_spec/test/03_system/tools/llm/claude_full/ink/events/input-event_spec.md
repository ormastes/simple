# Claude Full Ink InputEvent

> Checks terminal key parsing normalization for input events.

<!-- sdn-diagram:id=input-event_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=input-event_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

input-event_spec -> std
input-event_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=input-event_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full Ink InputEvent

Checks terminal key parsing normalization for input events.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/ink/events/input-event_spec.spl` |
| Updated | 2026-07-05 |
| Generator | `simple spipe-docgen` (Simple) |

Checks terminal key parsing normalization for input events.

## Scenarios

### Claude full ink InputEvent

#### maps named keys and modifiers

- Arrow, escape, option, and super flags are preserved
   - Expected: event.key.upArrow is true
   - Expected: event.key.meta is true
   - Expected: event.key.superKey is true
   - Expected: event.input equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Arrow, escape, option, and super flags are preserved")
val keypress = ParsedKey.new("up", "")
keypress.option = true
keypress.superKey = true
val event = InputEvent.new(keypress)
expect(event.key.upArrow).to_equal(true)
expect(event.key.meta).to_equal(true)
expect(event.key.superKey).to_equal(true)
expect(event.input).to_equal("")
```

</details>

#### normalizes ctrl space and uppercase shift

- Ctrl-space becomes a space and uppercase text implies shift
   - Expected: InputEvent.new(ctrlSpace).input equals ` `
   - Expected: upperEvent.input equals `A`
   - Expected: upperEvent.key.shift is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Ctrl-space becomes a space and uppercase text implies shift")
val ctrlSpace = ParsedKey.new("space", "")
ctrlSpace.ctrl = true
expect(InputEvent.new(ctrlSpace).input).to_equal(" ")
val upper = ParsedKey.new("", "A")
val upperEvent = InputEvent.new(upper)
expect(upperEvent.input).to_equal("A")
expect(upperEvent.key.shift).to_equal(true)
```

</details>

#### suppresses raw terminal fragments

- Unmapped function-key and SGR mouse fragments do not leak text
   - Expected: InputEvent.new(fnKey).input equals ``
   - Expected: InputEvent.new(mouse).input equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Unmapped function-key and SGR mouse fragments do not leak text")
val fnKey = ParsedKey.new("", "[25~")
fnKey.code = "[25~"
expect(InputEvent.new(fnKey).input).to_equal("")
val mouse = ParsedKey.new("", "[<64;74;16M")
expect(InputEvent.new(mouse).input).to_equal("")
```

</details>

#### normalizes special sequences

- Kitty, modifyOtherKeys, and application keypad use parsed names
   - Expected: InputEvent.new(kitty).input equals `b`
   - Expected: InputEvent.new(kittyEscape).input equals ``
   - Expected: InputEvent.new(modify).input equals `b`
   - Expected: InputEvent.new(keypad).input equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Kitty, modifyOtherKeys, and application keypad use parsed names")
val kitty = ParsedKey.new("b", "[98;3u")
expect(InputEvent.new(kitty).input).to_equal("b")
val kittyEscape = ParsedKey.new("escape", "[27u")
expect(InputEvent.new(kittyEscape).input).to_equal("")
val modify = ParsedKey.new("b", "[27;3;98~")
expect(InputEvent.new(modify).input).to_equal("b")
val keypad = ParsedKey.new("0", "Op")
expect(InputEvent.new(keypad).input).to_equal("0")
```

</details>

#### exports source-backed constants

- Pin parser edge-case contracts
   - Expected: ctrlSpaceNormalizesToSpace() is true
   - Expected: unmappedFunctionKeysAreSuppressed() is true
   - Expected: sgrMouseFragmentsAreSuppressed() is true
   - Expected: kittyCsiUSequencesUseParsedName() is true
   - Expected: modifyOtherKeysSequencesUseParsedName() is true
   - Expected: applicationKeypadUsesParsedDigit() is true
   - Expected: uppercaseInputSetsShift() is true
   - Expected: escapeCountsAsMeta() is true
   - Expected: optionCountsAsMeta() is true
   - Expected: superKeyDistinctFromMeta() is true
   - Expected: inputEventSourceLinesModeled() equals `218`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Pin parser edge-case contracts")
expect(ctrlSpaceNormalizesToSpace()).to_equal(true)
expect(unmappedFunctionKeysAreSuppressed()).to_equal(true)
expect(sgrMouseFragmentsAreSuppressed()).to_equal(true)
expect(kittyCsiUSequencesUseParsedName()).to_equal(true)
expect(modifyOtherKeysSequencesUseParsedName()).to_equal(true)
expect(applicationKeypadUsesParsedDigit()).to_equal(true)
expect(uppercaseInputSetsShift()).to_equal(true)
expect(escapeCountsAsMeta()).to_equal(true)
expect(optionCountsAsMeta()).to_equal(true)
expect(superKeyDistinctFromMeta()).to_equal(true)
expect(inputEventSourceLinesModeled()).to_equal(218)
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
