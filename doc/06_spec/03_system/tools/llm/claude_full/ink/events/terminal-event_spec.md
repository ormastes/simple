# Claude Full Terminal Event

> Mirrors DOM-style terminal event propagation state.

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
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Mirrors DOM-style terminal event propagation state.

## Scenarios

### Claude full terminal event

#### should default to bubbling cancelable none-phase events

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should default to bubbling cancelable none-phase events
- Create a base terminal event
   - Expected: event.type equals `keydown`
   - Expected: event.bubbles is true
   - Expected: event.cancelable is true
   - Expected: event.eventPhase equals `none`
   - Expected: event.defaultPrevented is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should default to bubbling cancelable none-phase events")
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

- should honor explicit init flags
- Create a non-bubbling non-cancelable event
   - Expected: event.bubbles is false
   - Expected: event.cancelable is false
   - Expected: event.defaultPrevented is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should honor explicit init flags")
step("Create a non-bubbling non-cancelable event")
val event = terminalEventWithInit("focus", false, false)
event.preventDefault()
expect(event.bubbles).to_equal(false)
expect(event.cancelable).to_equal(false)
expect(event.defaultPrevented).to_equal(false)
```

</details>

#### should prevent defaults only when cancelable

- should prevent defaults only when cancelable
- Create a cancelable event and prevent its default
   - Expected: event.defaultPrevented is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should prevent defaults only when cancelable")
step("Create a cancelable event and prevent its default")
val event = terminalEventWithInit("input", true, true)
event.preventDefault()
expect(event.defaultPrevented).to_equal(true)
```

</details>

#### should track targets and event phases

- should track targets and event phases
- Move an event through capture and target phases
   - Expected: event.target equals `leaf`
   - Expected: event.currentTarget equals `parent`
   - Expected: event.phaseIsCapturing() is true
   - Expected: event.phaseIsAtTarget() is true
   - Expected: event.currentTarget equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should track targets and event phases")
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

- should stop propagation and immediate propagation
- Stop normal propagation
   - Expected: event.isPropagationStopped() is true
   - Expected: event.isImmediatePropagationStopped() is false
   - Expected: event.isImmediatePropagationStopped() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should stop propagation and immediate propagation")
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

- should normalize invalid phases and prepare per target
- Normalize a defensive phase input
   - Expected: normalizeEventPhase("other") equals `none`
   - Expected: event.phaseIsBubbling() is true
   - Expected: event.preparedTarget equals `child`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should normalize invalid phases and prepare per target")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `9988e4a1370c15b644ef511d012cdab0d8ffda4864a827aaa017b2749b0e38e2`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `9988e4a1370c15b644ef511d012cdab0d8ffda4864a827aaa017b2749b0e38e2`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `9988e4a1370c15b644ef511d012cdab0d8ffda4864a827aaa017b2749b0e38e2`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/03_system/tools/llm/claude_full/ink/events/terminal-event_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/ink/events/terminal-event_spec.md (current)
findings: 11 blockers: 0
  narrative=100 structure=70 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/ink/events/terminal-event_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/ink/events/terminal-event_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/ink/events/terminal-event_spec.spl:18:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should default to bubbling cancelable none-phase events' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/ink/events/terminal-event_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should default to bubbling cancelable none-phase events' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/ink/events/terminal-event_spec.spl:29:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should honor explicit init flags' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/ink/events/terminal-event_spec.spl:29:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should honor explicit init flags' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/ink/events/terminal-event_spec.spl:39:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should prevent defaults only when cancelable' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/ink/events/terminal-event_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should prevent defaults only when cancelable' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/ink/events/terminal-event_spec.spl:47:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should track targets and event phases' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/ink/events/terminal-event_spec.spl:63:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should stop propagation and immediate propagation' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/ink/events/terminal-event_spec.spl:74:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should normalize invalid phases and prepare per target' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
