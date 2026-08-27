# focus_event_spec

> Purpose and audience: ink FocusEvent contract evidence for the llm_caret UI

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# focus_event_spec

Purpose and audience: ink FocusEvent contract evidence for the llm_caret UI

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/llm_caret/claude_full/ink/events/focus_event_spec.spl` |
| Updated | 2026-08-27 |
| Generator | `simple spipe-docgen` (Simple) |

Purpose and audience: ink FocusEvent contract evidence for the llm_caret UI
engineers who consume focus/blur DOM-event normalization. Covers type
normalization, related-target round-trip, bubble/cancel semantics, and
stopImmediatePropagation latching.

## Scenarios

### ink FocusEvent

#### keeps blur as blur and normalizes anything else to focus

- normalize the focus event type
   - Expected: normalizeFocusEventType("blur") equals `blur`
   - Expected: normalizeFocusEventType("focus") equals `focus`
   - Expected: normalizeFocusEventType("nonsense") equals `focus`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("normalize the focus event type")
expect(normalizeFocusEventType("blur")).to_equal("blur")
expect(normalizeFocusEventType("focus")).to_equal("focus")
expect(normalizeFocusEventType("nonsense")).to_equal("focus")
```

</details>

#### round-trips the related target

- construct a FocusEvent carrying a related target
   - Expected: e.relatedTarget equals `input-box`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("construct a FocusEvent carrying a related target")
val e = FocusEvent.new("focus", "input-box")
expect(e.relatedTarget).to_equal("input-box")
```

</details>

#### bubbles but is not cancelable

- check bubble and cancelable flags
   - Expected: e.bubbles is true
   - Expected: e.cancelable is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("check bubble and cancelable flags")
val e = FocusEvent.new("focus", "")
expect(e.bubbles).to_equal(true)
expect(e.cancelable).to_equal(false)
```

</details>

#### ignores preventDefault because the event is not cancelable

- attempt preventDefault on a non-cancelable event
   - Expected: e.defaultPrevented is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("attempt preventDefault on a non-cancelable event")
var e = FocusEvent.new("blur", "")
e.preventDefault()
expect(e.defaultPrevented).to_equal(false)
```

</details>

#### answers isFocus/isBlur consistently with the normalized type

- query isFocus and isBlur predicates
   - Expected: f.isFocus() is true
   - Expected: f.isBlur() is false
   - Expected: b.isBlur() is true
   - Expected: b.isFocus() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("query isFocus and isBlur predicates")
val f = focusEventNew("focus", "")
val b = focusEventNew("blur", "")
expect(f.isFocus()).to_equal(true)
expect(f.isBlur()).to_equal(false)
expect(b.isBlur()).to_equal(true)
expect(b.isFocus()).to_equal(false)
```

</details>

#### latches immediate-propagation stop

- stop immediate propagation and observe the latch
   - Expected: e.didStopImmediatePropagation() is false
   - Expected: e.didStopImmediatePropagation() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("stop immediate propagation and observe the latch")
var e = FocusEvent.new("focus", "")
expect(e.didStopImmediatePropagation()).to_equal(false)
e.stopImmediatePropagation()
expect(e.didStopImmediatePropagation()).to_equal(true)
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `928dbb922201b360b8293a8bb7783df885939639e4207d4035e2ad6d22aa8e89`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `928dbb922201b360b8293a8bb7783df885939639e4207d4035e2ad6d22aa8e89`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `928dbb922201b360b8293a8bb7783df885939639e4207d4035e2ad6d22aa8e89`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **91/100**; effective score: **91/100**; blockers: **0**.

SSpec documentization score: 91/100
source: test/01_unit/app/llm_caret/claude_full/ink/events/focus_event_spec.spl
mirror: doc/06_spec/01_unit/app/llm_caret/claude_full/ink/events/focus_event_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=55
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/llm_caret/claude_full/ink/events/focus_event_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/llm_caret/claude_full/ink/events/focus_event_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/llm_caret/claude_full/ink/events/focus_event_spec.spl:1:1: advice SSDOC-MNT-001 [maintainability] (-15): multiple scenarios form a flat, unfolded presentation
  why: Long flat dumps obscure the primary workflow.
  improve: Group secondary detail and keep the primary workflow visible.
test/01_unit/app/llm_caret/claude_full/ink/events/focus_event_spec.spl:19:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps blur as blur and normalizes anything else to focus' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/llm_caret/claude_full/ink/events/focus_event_spec.spl:27:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'round-trips the related target' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/llm_caret/claude_full/ink/events/focus_event_spec.spl:34:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'bubbles but is not cancelable' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
