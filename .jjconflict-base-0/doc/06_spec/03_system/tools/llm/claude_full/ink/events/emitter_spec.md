# Claude Full Ink EventEmitter

> Checks max-listener disabling and immediate propagation-aware emit.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full Ink EventEmitter

Checks max-listener disabling and immediate propagation-aware emit.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/ink/events/emitter_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Checks max-listener disabling and immediate propagation-aware emit.

## Scenarios

### Claude full ink EventEmitter

#### disables max listener warnings

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- disables max listener warnings
- Constructor sets max listeners to zero
   - Expected: emitter.maxListeners equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("disables max listener warnings")
step("Constructor sets max listeners to zero")
val emitter = EventEmitter.new()
expect(emitter.maxListeners).to_equal(0)
```

</details>

#### emits listeners and stops immediate propagation

- emits listeners and stops immediate propagation
- Normal emit calls listeners; stopped event breaks after first
   - Expected: emitter.emit("click", false) is true
   - Expected: emitter.calls equals `["a", "b"]`
   - Expected: stopped.emit("click", true) is true
   - Expected: stopped.calls equals `["a"]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("emits listeners and stops immediate propagation")
step("Normal emit calls listeners; stopped event breaks after first")
val emitter = EventEmitter.new()
emitter.on("a")
emitter.on("b")
expect(emitter.emit("click", false)).to_equal(true)
expect(emitter.calls).to_equal(["a", "b"])
val stopped = EventEmitter.new()
stopped.on("a")
stopped.on("b")
expect(stopped.emit("click", true)).to_equal(true)
expect(stopped.calls).to_equal(["a"])
```

</details>

#### handles error and empty listener cases

- handles error and empty listener cases
- Error delegates to node and empty emit returns false
   - Expected: empty.emit("click", false) is false
   - Expected: empty.emit("error", false) is true
   - Expected: empty.calls equals `["node:error"]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("handles error and empty listener cases")
step("Error delegates to node and empty emit returns false")
val empty = EventEmitter.new()
expect(empty.emit("click", false)).to_equal(false)
expect(empty.emit("error", false)).to_equal(true)
expect(empty.calls).to_equal(["node:error"])
```

</details>

#### exports source-backed constants

- exports source-backed constants
- Pin emitter contract
   - Expected: disablesDefaultMaxListenersWarning() is true
   - Expected: defaultMaxListeners() equals `0`
   - Expected: errorEventsDelegateToNode() is true
   - Expected: emitReturnsFalseWithoutListeners() is true
   - Expected: emitStopsOnImmediatePropagation() is true
   - Expected: eventEmitterSourceLinesModeled() equals `39`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("exports source-backed constants")
step("Pin emitter contract")
expect(disablesDefaultMaxListenersWarning()).to_equal(true)
expect(defaultMaxListeners()).to_equal(0)
expect(errorEventsDelegateToNode()).to_equal(true)
expect(emitReturnsFalseWithoutListeners()).to_equal(true)
expect(emitStopsOnImmediatePropagation()).to_equal(true)
expect(eventEmitterSourceLinesModeled()).to_equal(39)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
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

- Canonical SPipe generation for source `f3f512b13838796f018ec670c7ba6a33ecf911752ee8eeb1a0b62e716aef12e7`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f3f512b13838796f018ec670c7ba6a33ecf911752ee8eeb1a0b62e716aef12e7`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f3f512b13838796f018ec670c7ba6a33ecf911752ee8eeb1a0b62e716aef12e7`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/03_system/tools/llm/claude_full/ink/events/emitter_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/ink/events/emitter_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/ink/events/emitter_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/ink/events/emitter_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/ink/events/emitter_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/tools/llm/claude_full/ink/events/emitter_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'disables max listener warnings' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/ink/events/emitter_spec.spl:25:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'emits listeners and stops immediate propagation' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/ink/events/emitter_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'handles error and empty listener cases' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
