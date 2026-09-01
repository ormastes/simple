# Claude Full Ink InputEvent

> Checks terminal key parsing normalization for input events.

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
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Checks terminal key parsing normalization for input events.

## Scenarios

### Claude full ink InputEvent

#### maps named keys and modifiers

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- maps named keys and modifiers
- Arrow, escape, option, and super flags are preserved
   - Expected: event.key.upArrow is true
   - Expected: event.key.meta is true
   - Expected: event.key.superKey is true
   - Expected: event.input equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("maps named keys and modifiers")
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

- normalizes ctrl space and uppercase shift
- Ctrl-space becomes a space and uppercase text implies shift
   - Expected: InputEvent.new(ctrlSpace).input equals ` `
   - Expected: upperEvent.input equals `A`
   - Expected: upperEvent.key.shift is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("normalizes ctrl space and uppercase shift")
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

- suppresses raw terminal fragments
- Unmapped function-key and SGR mouse fragments do not leak text
   - Expected: InputEvent.new(fnKey).input equals ``
   - Expected: InputEvent.new(mouse).input equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("suppresses raw terminal fragments")
step("Unmapped function-key and SGR mouse fragments do not leak text")
val fnKey = ParsedKey.new("", "[25~")
fnKey.code = "[25~"
expect(InputEvent.new(fnKey).input).to_equal("")
val mouse = ParsedKey.new("", "[<64;74;16M")
expect(InputEvent.new(mouse).input).to_equal("")
```

</details>

#### normalizes special sequences

- normalizes special sequences
- Kitty, modifyOtherKeys, and application keypad use parsed names
   - Expected: InputEvent.new(kitty).input equals `b`
   - Expected: InputEvent.new(kittyEscape).input equals ``
   - Expected: InputEvent.new(modify).input equals `b`
   - Expected: InputEvent.new(keypad).input equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("normalizes special sequences")
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

- exports source-backed constants
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

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("exports source-backed constants")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `7ae4b338c503aafa78194b9bf3cd9622b21d5e97f9c36190ceb0a0cba39ab8e5`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `7ae4b338c503aafa78194b9bf3cd9622b21d5e97f9c36190ceb0a0cba39ab8e5`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `7ae4b338c503aafa78194b9bf3cd9622b21d5e97f9c36190ceb0a0cba39ab8e5`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/03_system/tools/llm/claude_full/ink/events/input-event_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/ink/events/input-event_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/ink/events/input-event_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/ink/events/input-event_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/ink/events/input-event_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/tools/llm/claude_full/ink/events/input-event_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'maps named keys and modifiers' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/ink/events/input-event_spec.spl:31:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'normalizes ctrl space and uppercase shift' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/ink/events/input-event_spec.spl:43:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'suppresses raw terminal fragments' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
