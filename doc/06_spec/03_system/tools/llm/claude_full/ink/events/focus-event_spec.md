# Claude Full Focus Event

> Mirrors Ink focus and blur events: bubbling, non-cancelable, and carrying the

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full Focus Event

Mirrors Ink focus and blur events: bubbling, non-cancelable, and carrying the

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/ink/events/focus-event_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Mirrors Ink focus and blur events: bubbling, non-cancelable, and carrying the
related target from the previous or next focused element.

## Scenarios

### Claude full focus event

#### should preserve focus and blur event types with related target

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should preserve focus and blur event types with related target
- Create focus and blur events
   - Expected: focus.type equals `focus`
   - Expected: focus.relatedTarget equals `previous-node`
   - Expected: focus.isFocus() is true
   - Expected: focus.isBlur() is false
   - Expected: blur.type equals `blur`
   - Expected: blur.relatedTarget equals `next-node`
   - Expected: blur.isFocus() is false
   - Expected: blur.isBlur() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should preserve focus and blur event types with related target")
step("Create focus and blur events")
val focus = focusEventNew("focus", "previous-node")
val blur = focusEventNew("blur", "next-node")
expect(focus.type).to_equal("focus")
expect(focus.relatedTarget).to_equal("previous-node")
expect(focus.isFocus()).to_equal(true)
expect(focus.isBlur()).to_equal(false)
expect(blur.type).to_equal("blur")
expect(blur.relatedTarget).to_equal("next-node")
expect(blur.isFocus()).to_equal(false)
expect(blur.isBlur()).to_equal(true)
```

</details>

#### should bubble but remain non-cancelable

- should bubble but remain non-cancelable
- Create a focus event and try to prevent default
   - Expected: event.bubbles is true
   - Expected: event.cancelable is false
   - Expected: event.defaultPrevented is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should bubble but remain non-cancelable")
step("Create a focus event and try to prevent default")
val event = focusEventNew("focus", "")
expect(event.bubbles).to_equal(true)
expect(event.cancelable).to_equal(false)
event.preventDefault()
expect(event.defaultPrevented).to_equal(false)
```

</details>

#### should normalize unknown focus input and stop immediate propagation

- should normalize unknown focus input and stop immediate propagation
- Normalize a defensive event type and stop propagation
   - Expected: normalizeFocusEventType("other") equals `focus`
   - Expected: event.didStopImmediatePropagation() is false
   - Expected: event.didStopImmediatePropagation() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should normalize unknown focus input and stop immediate propagation")
step("Normalize a defensive event type and stop propagation")
expect(normalizeFocusEventType("other")).to_equal("focus")
val event = focusEventNew("other", "")
expect(event.didStopImmediatePropagation()).to_equal(false)
event.stopImmediatePropagation()
expect(event.didStopImmediatePropagation()).to_equal(true)
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `600014c1c7cf65f707b4ed5caa3d4395cebcff0ffb1e7f6e422d748c836c6b00`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `600014c1c7cf65f707b4ed5caa3d4395cebcff0ffb1e7f6e422d748c836c6b00`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `600014c1c7cf65f707b4ed5caa3d4395cebcff0ffb1e7f6e422d748c836c6b00`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/03_system/tools/llm/claude_full/ink/events/focus-event_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/ink/events/focus-event_spec.md (current)
findings: 8 blockers: 0
  narrative=100 structure=85 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/ink/events/focus-event_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/ink/events/focus-event_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/ink/events/focus-event_spec.spl:19:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should preserve focus and blur event types with related target' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/ink/events/focus-event_spec.spl:19:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should preserve focus and blur event types with related target' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/ink/events/focus-event_spec.spl:34:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should bubble but remain non-cancelable' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/ink/events/focus-event_spec.spl:34:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should bubble but remain non-cancelable' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/ink/events/focus-event_spec.spl:44:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should normalize unknown focus input and stop immediate propagation' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/ink/events/focus-event_spec.spl:44:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should normalize unknown focus input and stop immediate propagation' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
