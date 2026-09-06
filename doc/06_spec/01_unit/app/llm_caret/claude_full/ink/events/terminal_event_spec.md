# Terminal Event Specification

> Tests covering ink TerminalEvent.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Terminal Event Specification

## Scenarios

### ink TerminalEvent

#### defaults to bubbling and cancelable with an empty target and none phase
#### honours an explicit init for bubbles and cancelable

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val e = terminalEventWithInit("click", false, false)
expect(e.bubbles).to_equal(false)
expect(e.cancelable).to_equal(false)
```

</details>

#### only marks defaultPrevented when the event is cancelable

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var cancelable = TerminalEvent.new("keydown")
cancelable.preventDefault()
expect(cancelable.defaultPrevented).to_equal(true)
var fixed = terminalEventWithInit("keydown", true, false)
fixed.preventDefault()
expect(fixed.defaultPrevented).to_equal(false)
```

</details>

#### stopImmediatePropagation also stops ordinary propagation

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var e = terminalEventNew("keydown")
expect(e.isPropagationStopped()).to_equal(false)
e.stopImmediatePropagation()
expect(e.isImmediatePropagationStopped()).to_equal(true)
expect(e.isPropagationStopped()).to_equal(true)
```

</details>

#### stopPropagation does not imply immediate stop

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var e = terminalEventNew("keydown")
e.stopPropagation()
expect(e.isPropagationStopped()).to_equal(true)
expect(e.isImmediatePropagationStopped()).to_equal(false)
```

</details>

#### tracks target, currentTarget and clears currentTarget

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var e = terminalEventNew("keydown")
e.setTarget("root")
e.setCurrentTarget("child")
expect(e.target).to_equal("root")
expect(e.currentTarget).to_equal("child")
e.clearCurrentTarget()
expect(e.currentTarget).to_equal("")
```

</details>

#### normalizes event phases and rejects unknown ones

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(normalizeEventPhase("capturing")).to_equal("capturing")
expect(normalizeEventPhase("at_target")).to_equal("at_target")
expect(normalizeEventPhase("bubbling")).to_equal("bubbling")
expect(normalizeEventPhase("sideways")).to_equal("none")
expect(terminalEventPhases().len()).to_equal(4)
```

</details>

#### answers exactly one phase predicate at a time

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var e = terminalEventNew("keydown")
e.setEventPhase("bubbling")
expect(e.phaseIsBubbling()).to_equal(true)
expect(e.phaseIsCapturing()).to_equal(false)
expect(e.phaseIsAtTarget()).to_equal(false)
```

</details>

#### records the prepared target

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var e = terminalEventNew("keydown")
e.prepareForTarget("box-1")
expect(e.preparedTarget).to_equal("box-1")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/llm_caret/claude_full/ink/events/terminal_event_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering ink TerminalEvent.
- ink TerminalEvent

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
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

- Canonical SPipe generation for source `ef063ffe431d4cdb3a7509817c3fc19e2ca4629626f56c9915bf57484835c732`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ef063ffe431d4cdb3a7509817c3fc19e2ca4629626f56c9915bf57484835c732`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ef063ffe431d4cdb3a7509817c3fc19e2ca4629626f56c9915bf57484835c732`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **81/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/app/llm_caret/claude_full/ink/events/terminal_event_spec.spl
mirror: doc/06_spec/01_unit/app/llm_caret/claude_full/ink/events/terminal_event_spec.md (current)
findings: 9 blockers: 1
  narrative=100 structure=60 oracle=90
  traceability=60 evidence=100 coverage=100 maintainability=55
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=81; blocker cap makes effective=49
doc/06_spec/01_unit/app/llm_caret/claude_full/ink/events/terminal_event_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/llm_caret/claude_full/ink/events/terminal_event_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/llm_caret/claude_full/ink/events/terminal_event_spec.spl:1:1: advice SSDOC-MNT-001 [maintainability] (-15): multiple scenarios form a flat, unfolded presentation
  why: Long flat dumps obscure the primary workflow.
  improve: Group secondary detail and keep the primary workflow visible.
test/01_unit/app/llm_caret/claude_full/ink/events/terminal_event_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/app/llm_caret/claude_full/ink/events/terminal_event_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/app/llm_caret/claude_full/ink/events/terminal_event_spec.spl:17:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'defaults to bubbling and cancelable with an empty target and none phase' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/app/llm_caret/claude_full/ink/events/terminal_event_spec.spl:28:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'honours an explicit init for bubbles and cancelable' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/app/llm_caret/claude_full/ink/events/terminal_event_spec.spl:34:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'only marks defaultPrevented when the event is cancelable' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/app/llm_caret/claude_full/ink/events/terminal_event_spec.spl:43:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'stopImmediatePropagation also stops ordinary propagation' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
<!-- sspec-maintain:scorecard:end -->
