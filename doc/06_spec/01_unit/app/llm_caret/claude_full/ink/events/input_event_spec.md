# Input Event Specification

> Tests covering ink InputEvent.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 15 | 15 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Input Event Specification

## Scenarios

### ink InputEvent

#### passes a plain printable sequence through unchanged
#### clears input for non-alphanumeric named keys

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(inputFor("up", "\u{1b}[A")).to_equal("")
expect(inputFor("escape", "\u{1b}")).to_equal("")
expect(inputFor("tab", "\t")).to_equal("")
```

</details>

#### maps arrow names onto the corresponding key flags

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val up = InputEvent.new(ParsedKey.new("up", "\u{1b}[A"))
expect(up.key.upArrow).to_equal(true)
expect(up.key.downArrow).to_equal(false)
val right = InputEvent.new(ParsedKey.new("right", "\u{1b}[C"))
expect(right.key.rightArrow).to_equal(true)
expect(right.key.upArrow).to_equal(false)
```

</details>

#### treats escape as meta

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(InputEvent.new(ParsedKey.new("escape", "\u{1b}")).key.meta).to_equal(true)
```

</details>

#### treats option as meta but keeps super distinct

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var p = ParsedKey.new("a", "a")
p.option = true
p.superKey = true
val e = InputEvent.new(p)
expect(e.key.meta).to_equal(true)
expect(e.key.superKey).to_equal(true)
```

</details>

#### uses the key name as input when ctrl is held

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var p = ParsedKey.new("c", "\u{3}")
p.ctrl = true
val e = InputEvent.new(p)
expect(e.input).to_equal("c")
expect(e.key.ctrl).to_equal(true)
```

</details>

#### normalizes ctrl+space to an actual space

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var p = ParsedKey.new("space", "\u{0}")
p.ctrl = true
expect(InputEvent.new(p).input).to_equal(" ")
```

</details>

#### resolves a Kitty CSI-u sequence through the parsed name

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(inputFor("space", "\u{1b}[32;1u")).to_equal(" ")
```

</details>

#### resolves an application-keypad sequence to the parsed digit

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(inputFor("1", "\u{1b}O1")).to_equal("1")
```

</details>

#### suppresses SGR mouse fragments that arrive without a key name

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(inputFor("", "[<0;1;1M")).to_equal("")
expect(isSgrMouseFragment("[<0;1;1M")).to_equal(true)
expect(isSgrMouseFragment("[<0;1;1")).to_equal(false)
expect(isSgrMouseFragment("a")).to_equal(false)
```

</details>

#### suppresses a function-key code that carries no name

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var p = ParsedKey.new("", "\u{1b}[15~")
p.code = "[15~"
expect(InputEvent.new(p).input).to_equal("")
```

</details>

#### sets shift for a single uppercase character

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(InputEvent.new(ParsedKey.new("A", "A")).key.shift).to_equal(true)
expect(InputEvent.new(ParsedKey.new("a", "a")).key.shift).to_equal(false)
```

</details>

#### classifies non-alphanumeric key names

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(isNonAlphanumericKey("backspace")).to_equal(true)
expect(isNonAlphanumericKey("delete")).to_equal(true)
expect(isNonAlphanumericKey("a")).to_equal(false)
```

</details>

#### maps special sequence names to their input text

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(specialSequenceInput("space")).to_equal(" ")
expect(specialSequenceInput("escape")).to_equal("")
expect(specialSequenceInput("")).to_equal("")
expect(specialSequenceInput("f5")).to_equal("f5")
```

</details>

#### keeps the originating keypress on the event

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val e = InputEvent.new(ParsedKey.new("up", "\u{1b}[A"))
expect(e.keypress.name).to_equal("up")
expect(e.keypress.sequence).to_equal("\u{1b}[A")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/llm_caret/claude_full/ink/events/input_event_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering ink InputEvent.
- ink InputEvent

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 15 |
| Active scenarios | 15 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `839f796e5720d3f894ed1a7641de0907731f5e94317dc36bcb63f35800a45a51`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `839f796e5720d3f894ed1a7641de0907731f5e94317dc36bcb63f35800a45a51`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `839f796e5720d3f894ed1a7641de0907731f5e94317dc36bcb63f35800a45a51`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **83/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/app/llm_caret/claude_full/ink/events/input_event_spec.spl
mirror: doc/06_spec/01_unit/app/llm_caret/claude_full/ink/events/input_event_spec.md (current)
findings: 8 blockers: 1
  narrative=100 structure=60 oracle=100
  traceability=60 evidence=100 coverage=100 maintainability=55
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=83; blocker cap makes effective=49
doc/06_spec/01_unit/app/llm_caret/claude_full/ink/events/input_event_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/llm_caret/claude_full/ink/events/input_event_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/llm_caret/claude_full/ink/events/input_event_spec.spl:1:1: advice SSDOC-MNT-001 [maintainability] (-15): multiple scenarios form a flat, unfolded presentation
  why: Long flat dumps obscure the primary workflow.
  improve: Group secondary detail and keep the primary workflow visible.
test/01_unit/app/llm_caret/claude_full/ink/events/input_event_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/app/llm_caret/claude_full/ink/events/input_event_spec.spl:17:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'passes a plain printable sequence through unchanged' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/app/llm_caret/claude_full/ink/events/input_event_spec.spl:23:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'clears input for non-alphanumeric named keys' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/app/llm_caret/claude_full/ink/events/input_event_spec.spl:29:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'maps arrow names onto the corresponding key flags' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/app/llm_caret/claude_full/ink/events/input_event_spec.spl:38:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'treats escape as meta' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
<!-- sspec-maintain:scorecard:end -->
