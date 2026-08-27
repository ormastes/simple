# Focus Event Specification

> Tests covering ink FocusEvent.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Focus Event Specification

## Scenarios

### ink FocusEvent

#### keeps blur as blur and normalizes anything else to focus
#### round-trips the related target

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val e = FocusEvent.new("focus", "input-box")
expect(e.relatedTarget).to_equal("input-box")
```

</details>

#### bubbles but is not cancelable

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val e = FocusEvent.new("focus", "")
expect(e.bubbles).to_equal(true)
expect(e.cancelable).to_equal(false)
```

</details>

#### ignores preventDefault because the event is not cancelable

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var e = FocusEvent.new("blur", "")
e.preventDefault()
expect(e.defaultPrevented).to_equal(false)
```

</details>

#### answers isFocus/isBlur consistently with the normalized type

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val f = focusEventNew("focus", "")
val b = focusEventNew("blur", "")
expect(f.isFocus()).to_equal(true)
expect(f.isBlur()).to_equal(false)
expect(b.isBlur()).to_equal(true)
expect(b.isFocus()).to_equal(false)
```

</details>

#### latches immediate-propagation stop

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var e = FocusEvent.new("focus", "")
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
| Source | `test/01_unit/app/llm_caret/claude_full/ink/events/focus_event_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering ink FocusEvent.
- ink FocusEvent

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
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

- Canonical SPipe generation for source `9a1e8ed2eb021b7b35485a396d2311e671701da42b542474c8e2ab16e72bac47`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `9a1e8ed2eb021b7b35485a396d2311e671701da42b542474c8e2ab16e72bac47`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `9a1e8ed2eb021b7b35485a396d2311e671701da42b542474c8e2ab16e72bac47`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **83/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/app/llm_caret/claude_full/ink/events/focus_event_spec.spl
mirror: doc/06_spec/01_unit/app/llm_caret/claude_full/ink/events/focus_event_spec.md (current)
findings: 8 blockers: 1
  narrative=100 structure=60 oracle=100
  traceability=60 evidence=100 coverage=100 maintainability=55
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=83; blocker cap makes effective=49
doc/06_spec/01_unit/app/llm_caret/claude_full/ink/events/focus_event_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/llm_caret/claude_full/ink/events/focus_event_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/llm_caret/claude_full/ink/events/focus_event_spec.spl:1:1: advice SSDOC-MNT-001 [maintainability] (-15): multiple scenarios form a flat, unfolded presentation
  why: Long flat dumps obscure the primary workflow.
  improve: Group secondary detail and keep the primary workflow visible.
test/01_unit/app/llm_caret/claude_full/ink/events/focus_event_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/app/llm_caret/claude_full/ink/events/focus_event_spec.spl:14:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'keeps blur as blur and normalizes anything else to focus' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/app/llm_caret/claude_full/ink/events/focus_event_spec.spl:22:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'round-trips the related target' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/app/llm_caret/claude_full/ink/events/focus_event_spec.spl:27:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'bubbles but is not cancelable' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/app/llm_caret/claude_full/ink/events/focus_event_spec.spl:33:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'ignores preventDefault because the event is not cancelable' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
<!-- sspec-maintain:scorecard:end -->
