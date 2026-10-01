# Keyboard Event Specification

> Tests covering ink KeyboardEvent.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Keyboard Event Specification

## Scenarios

### ink KeyboardEvent

#### uses a printable single-character sequence as the key
#### prefers the parsed name for named keys

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val e = KeyboardEvent.new(parsedKeyboardKeyNew("up", "[A"))
expect(e.key).to_equal("up")
expect(e.printableChar()).to_equal(false)
```

</details>

#### uses the name when ctrl is held even for a printable sequence

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var p = parsedKeyboardKeyNew("c", "\u{3}")
p.ctrl = true
val e = KeyboardEvent.new(p)
expect(e.key).to_equal("c")
expect(e.ctrl).to_equal(true)
```

</details>

#### does not treat DEL (127) as a printable key sequence

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(keyFromParsed(parsedKeyboardKeyNew("backspace", "\u{7f}"))).to_equal("backspace")
```

</details>

#### folds option into meta but keeps super separate

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var p = parsedKeyboardKeyNew("a", "a")
p.option = true
p.superKey = true
val e = KeyboardEvent.new(p)
expect(e.meta).to_equal(true)
expect(e.superKey).to_equal(true)
```

</details>

#### is a bubbling, cancelable keydown by construction

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val e = KeyboardEvent.new(parsedKeyboardKeyNew("a", "a"))
expect(e.type).to_equal("keydown")
expect(e.bubbles).to_equal(true)
expect(e.cancelable).to_equal(true)
```

</details>

#### latches immediate-propagation stop

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var e = KeyboardEvent.new(parsedKeyboardKeyNew("a", "a"))
expect(e.didStopImmediatePropagation()).to_equal(false)
e.stopImmediatePropagation()
expect(e.didStopImmediatePropagation()).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/llm_caret/claude_full/ink/events/keyboard_event_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering ink KeyboardEvent.
- ink KeyboardEvent

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
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

- Canonical SPipe generation for source `d949ba84f8d79b27af1687b17f8846fc435c0a2ad046a886a63344bb0e01330c`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `d949ba84f8d79b27af1687b17f8846fc435c0a2ad046a886a63344bb0e01330c`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `d949ba84f8d79b27af1687b17f8846fc435c0a2ad046a886a63344bb0e01330c`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **83/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/app/llm_caret/claude_full/ink/events/keyboard_event_spec.spl
mirror: doc/06_spec/01_unit/app/llm_caret/claude_full/ink/events/keyboard_event_spec.md (current)
findings: 8 blockers: 1
  narrative=100 structure=60 oracle=100
  traceability=60 evidence=100 coverage=100 maintainability=55
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=83; blocker cap makes effective=49
doc/06_spec/01_unit/app/llm_caret/claude_full/ink/events/keyboard_event_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/llm_caret/claude_full/ink/events/keyboard_event_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/llm_caret/claude_full/ink/events/keyboard_event_spec.spl:1:1: advice SSDOC-MNT-001 [maintainability] (-15): multiple scenarios form a flat, unfolded presentation
  why: Long flat dumps obscure the primary workflow.
  improve: Group secondary detail and keep the primary workflow visible.
test/01_unit/app/llm_caret/claude_full/ink/events/keyboard_event_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/app/llm_caret/claude_full/ink/events/keyboard_event_spec.spl:14:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'uses a printable single-character sequence as the key' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/app/llm_caret/claude_full/ink/events/keyboard_event_spec.spl:22:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'prefers the parsed name for named keys' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/app/llm_caret/claude_full/ink/events/keyboard_event_spec.spl:28:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'uses the name when ctrl is held even for a printable sequence' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/app/llm_caret/claude_full/ink/events/keyboard_event_spec.spl:36:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'does not treat DEL (127) as a printable key sequence' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
<!-- sspec-maintain:scorecard:end -->
