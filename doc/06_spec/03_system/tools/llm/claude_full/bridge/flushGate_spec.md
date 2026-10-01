# Claude Full Bridge FlushGate

> Mirrors `bridge/flushGate.ts`, the queueing state machine that prevents new

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full Bridge FlushGate

Mirrors `bridge/flushGate.ts`, the queueing state machine that prevents new

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/bridge/flushGate_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Mirrors `bridge/flushGate.ts`, the queueing state machine that prevents new
messages from interleaving with an initial history flush.

## Scenarios

### Claude full bridge FlushGate

#### should queue messages only while active and drain them on end

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should queue messages only while active and drain them on end
- Create a gate and confirm the initial inactive state
   - Expected: flushGateIsActive(gate) is false
   - Expected: flushGatePendingCount(gate) equals `0`
   - Expected: gate.enqueue("direct") is false
- Start the flush and queue messages
   - Expected: gate.isActive() is true
   - Expected: gate.enqueue("a") is true
   - Expected: gate.enqueue2("b", "c") is true
   - Expected: gate.pendingCount() equals `3`
   - Expected: gate.firstPending() equals `a`
   - Expected: gate.lastPending() equals `c`
- End the flush and drain pending messages
   - Expected: gate.isActive() is false
   - Expected: gate.pendingCount() equals `0`
   - Expected: drained.len() equals `3`
   - Expected: drained[0] equals `a`
   - Expected: drained[2] equals `c`


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should queue messages only while active and drain them on end")
step("Create a gate and confirm the initial inactive state")
val gate = flushGateNew()
expect(flushGateIsActive(gate)).to_equal(false)
expect(flushGatePendingCount(gate)).to_equal(0)
expect(gate.enqueue("direct")).to_equal(false)

step("Start the flush and queue messages")
gate.start()
expect(gate.isActive()).to_equal(true)
expect(gate.enqueue("a")).to_equal(true)
expect(gate.enqueue2("b", "c")).to_equal(true)
expect(gate.pendingCount()).to_equal(3)
expect(gate.firstPending()).to_equal("a")
expect(gate.lastPending()).to_equal("c")

step("End the flush and drain pending messages")
val drained = gate.end()
expect(gate.isActive()).to_equal(false)
expect(gate.pendingCount()).to_equal(0)
expect(drained.len()).to_equal(3)
expect(drained[0]).to_equal("a")
expect(drained[2]).to_equal("c")
```

</details>

#### should drop or preserve pending messages according to lifecycle method

- should drop or preserve pending messages according to lifecycle method
- Drop pending messages on permanent close
   - Expected: gate.enqueueMany(["x", "y"]) is true
   - Expected: gate.drop() equals `2`
   - Expected: gate.isActive() is false
   - Expected: gate.hasPending() is false
- Deactivate without clearing pending messages for transport replacement
   - Expected: gate.enqueue("replacement") is true
   - Expected: gate.isActive() is false
   - Expected: gate.pendingCount() equals `1`
   - Expected: gate.end()[0] equals `replacement`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should drop or preserve pending messages according to lifecycle method")
step("Drop pending messages on permanent close")
val gate = flushGateNew()
gate.start()
expect(gate.enqueueMany(["x", "y"])).to_equal(true)
expect(gate.drop()).to_equal(2)
expect(gate.isActive()).to_equal(false)
expect(gate.hasPending()).to_equal(false)

step("Deactivate without clearing pending messages for transport replacement")
gate.start()
expect(gate.enqueue("replacement")).to_equal(true)
gate.deactivate()
expect(gate.isActive()).to_equal(false)
expect(gate.pendingCount()).to_equal(1)
expect(gate.end()[0]).to_equal("replacement")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
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

- Canonical SPipe generation for source `51de1c18afae491a14810647b7979bc61e4a1443851558cc23aea4805e3ca423`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `51de1c18afae491a14810647b7979bc61e4a1443851558cc23aea4805e3ca423`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `51de1c18afae491a14810647b7979bc61e4a1443851558cc23aea4805e3ca423`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/03_system/tools/llm/claude_full/bridge/flushGate_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/bridge/flushGate_spec.md (current)
findings: 7 blockers: 0
  narrative=100 structure=90 oracle=70
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/bridge/flushGate_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/bridge/flushGate_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/bridge/flushGate_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 6 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/tools/llm/claude_full/bridge/flushGate_spec.spl:19:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should queue messages only while active and drain them on end' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/bridge/flushGate_spec.spl:19:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should queue messages only while active and drain them on end' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/bridge/flushGate_spec.spl:45:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should drop or preserve pending messages according to lifecycle method' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/bridge/flushGate_spec.spl:45:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should drop or preserve pending messages according to lifecycle method' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
