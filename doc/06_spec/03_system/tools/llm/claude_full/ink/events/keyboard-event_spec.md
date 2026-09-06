# Claude Full Keyboard Event

> Mirrors Ink keyboard events as DOM-like keydown payloads.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full Keyboard Event

Mirrors Ink keyboard events as DOM-like keydown payloads.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/ink/events/keyboard-event_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Mirrors Ink keyboard events as DOM-like keydown payloads.

## Scenarios

### Claude full keyboard event

#### should expose keydown event defaults

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should expose keydown event defaults
- Create an event from a printable key
   - Expected: event.type equals `keydown`
   - Expected: event.bubbles is true
   - Expected: event.cancelable is true
   - Expected: event.key equals `a`
   - Expected: event.printableChar() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should expose keydown event defaults")
step("Create an event from a printable key")
val parsed = parsedKeyboardKeyNew("", "a")
val event = keyboardEventNew(parsed)
expect(event.type).to_equal("keydown")
expect(event.bubbles).to_equal(true)
expect(event.cancelable).to_equal(true)
expect(event.key).to_equal("a")
expect(event.printableChar()).to_equal(true)
```

</details>

#### should use parsed names for ctrl combinations

- should use parsed names for ctrl combinations
- Create a ctrl+c event whose sequence is a control byte
   - Expected: event.key equals `c`
   - Expected: event.ctrl is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should use parsed names for ctrl combinations")
step("Create a ctrl+c event whose sequence is a control byte")
val parsed = parsedKeyboardKeyNew("c", "\u0003")
parsed.ctrl = true
val event = keyboardEventNew(parsed)
expect(event.key).to_equal("c")
expect(event.ctrl).to_equal(true)
```

</details>

#### should use parsed names for terminal escape sequences

- should use parsed names for terminal escape sequences
- Create an arrow-key event from a terminal sequence
   - Expected: event.key equals `down`
   - Expected: event.printableChar() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should use parsed names for terminal escape sequences")
step("Create an arrow-key event from a terminal sequence")
val parsed = parsedKeyboardKeyNew("down", "\u001B[B")
val event = keyboardEventNew(parsed)
expect(event.key).to_equal("down")
expect(event.printableChar()).to_equal(false)
```

</details>

#### should propagate option as meta and preserve super and function flags

- should propagate option as meta and preserve super and function flags
- Create an event with terminal modifier flags
   - Expected: event.meta is true
   - Expected: event.superKey is true
   - Expected: event.functionKey is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should propagate option as meta and preserve super and function flags")
step("Create an event with terminal modifier flags")
val parsed = parsedKeyboardKeyNew("f1", "\u001BOP")
parsed.option = true
parsed.superKey = true
parsed.functionKey = true
val event = keyboardEventNew(parsed)
expect(event.meta).to_equal(true)
expect(event.superKey).to_equal(true)
expect(event.functionKey).to_equal(true)
```

</details>

#### should stop immediate propagation

- should stop immediate propagation
- Stop propagation on the keyboard event
   - Expected: event.didStopImmediatePropagation() is false
   - Expected: event.didStopImmediatePropagation() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should stop immediate propagation")
step("Stop propagation on the keyboard event")
val parsed = parsedKeyboardKeyNew("return", "\r")
val event = keyboardEventNew(parsed)
expect(event.didStopImmediatePropagation()).to_equal(false)
event.stopImmediatePropagation()
expect(event.didStopImmediatePropagation()).to_equal(true)
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

- Canonical SPipe generation for source `0bf3d5a5befa9cf260bfa44bb1aec65cf1c592cea6761b59f04b82ef80c8cc2f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `0bf3d5a5befa9cf260bfa44bb1aec65cf1c592cea6761b59f04b82ef80c8cc2f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `0bf3d5a5befa9cf260bfa44bb1aec65cf1c592cea6761b59f04b82ef80c8cc2f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/03_system/tools/llm/claude_full/ink/events/keyboard-event_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/ink/events/keyboard-event_spec.md (current)
findings: 10 blockers: 0
  narrative=100 structure=75 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/ink/events/keyboard-event_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/ink/events/keyboard-event_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/ink/events/keyboard-event_spec.spl:18:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should expose keydown event defaults' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/ink/events/keyboard-event_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should expose keydown event defaults' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/ink/events/keyboard-event_spec.spl:30:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should use parsed names for ctrl combinations' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/ink/events/keyboard-event_spec.spl:30:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should use parsed names for ctrl combinations' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/ink/events/keyboard-event_spec.spl:40:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should use parsed names for terminal escape sequences' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/ink/events/keyboard-event_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should use parsed names for terminal escape sequences' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/ink/events/keyboard-event_spec.spl:49:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should propagate option as meta and preserve super and function flags' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/ink/events/keyboard-event_spec.spl:62:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should stop immediate propagation' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
