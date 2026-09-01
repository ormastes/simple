# Claude Full Terminal Focus Event

> Mirrors the terminal focus/blur event emitted from DECSET 1004 focus reporting.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full Terminal Focus Event

Mirrors the terminal focus/blur event emitted from DECSET 1004 focus reporting.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/ink/events/terminal-focus-event_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Mirrors the terminal focus/blur event emitted from DECSET 1004 focus reporting.

## Scenarios

### Claude full terminal focus event

#### should preserve terminal focus and blur types

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should preserve terminal focus and blur types
- Create focus and blur events
- Check the event type helpers
   - Expected: focus.type equals `terminalfocus`
   - Expected: focus.isFocus() is true
   - Expected: focus.isBlur() is false
   - Expected: blur.type equals `terminalblur`
   - Expected: blur.isFocus() is false
   - Expected: blur.isBlur() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should preserve terminal focus and blur types")
step("Create focus and blur events")
val focus = terminalFocusEventNew("terminalfocus")
val blur = terminalFocusEventNew("terminalblur")

step("Check the event type helpers")
expect(focus.type).to_equal("terminalfocus")
expect(focus.isFocus()).to_equal(true)
expect(focus.isBlur()).to_equal(false)
expect(blur.type).to_equal("terminalblur")
expect(blur.isFocus()).to_equal(false)
expect(blur.isBlur()).to_equal(true)
```

</details>

#### should inherit immediate propagation stop behavior

- should inherit immediate propagation stop behavior
- Create a focus event and stop immediate propagation
   - Expected: event.didStopImmediatePropagation() is false
   - Expected: event.didStopImmediatePropagation() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should inherit immediate propagation stop behavior")
step("Create a focus event and stop immediate propagation")
val event = terminalFocusEventNew("terminalfocus")
expect(event.didStopImmediatePropagation()).to_equal(false)
event.stopImmediatePropagation()
expect(event.didStopImmediatePropagation()).to_equal(true)
```

</details>

#### should normalize unknown terminal focus input to focus

- should normalize unknown terminal focus input to focus
- Normalize a defensive fallback value
   - Expected: normalizeTerminalFocusEventType("other") equals `terminalfocus`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should normalize unknown terminal focus input to focus")
step("Normalize a defensive fallback value")
expect(normalizeTerminalFocusEventType("other")).to_equal("terminalfocus")
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

- Canonical SPipe generation for source `17f7e20a88149751b7f1d581543a095c68cacb893ca636352b3b5a05115de783`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `17f7e20a88149751b7f1d581543a095c68cacb893ca636352b3b5a05115de783`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `17f7e20a88149751b7f1d581543a095c68cacb893ca636352b3b5a05115de783`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/03_system/tools/llm/claude_full/ink/events/terminal-focus-event_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/ink/events/terminal-focus-event_spec.md (current)
findings: 8 blockers: 0
  narrative=100 structure=85 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/ink/events/terminal-focus-event_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/ink/events/terminal-focus-event_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/ink/events/terminal-focus-event_spec.spl:18:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should preserve terminal focus and blur types' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/ink/events/terminal-focus-event_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should preserve terminal focus and blur types' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/ink/events/terminal-focus-event_spec.spl:33:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should inherit immediate propagation stop behavior' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/ink/events/terminal-focus-event_spec.spl:33:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should inherit immediate propagation stop behavior' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/ink/events/terminal-focus-event_spec.spl:42:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should normalize unknown terminal focus input to focus' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/ink/events/terminal-focus-event_spec.spl:42:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should normalize unknown terminal focus input to focus' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
