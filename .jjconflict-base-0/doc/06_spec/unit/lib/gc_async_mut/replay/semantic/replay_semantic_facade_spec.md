# Replay Semantic Facade Specification

> Tests covering gc_async_mut replay semantic facades.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Replay Semantic Facade Specification

## Scenarios

### gc_async_mut replay semantic facades

#### re-exports semantic event records

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- re-exports semantic event records
   - Expected: ev.kind equals `SemanticEventKind.VariableWrite.to_i32()`
   - Expected: ev.event_kind().to_i32() equals `SemanticEventKind.VariableWrite.to_i32()`
   - Expected: SEMANTIC_EVENT_SIZE equals `68`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("re-exports semantic event records")
val ev = SemanticEvent.create(SemanticEventKind.VariableWrite)

expect(ev.kind).to_equal(SemanticEventKind.VariableWrite.to_i32())
expect(ev.event_kind().to_i32()).to_equal(SemanticEventKind.VariableWrite.to_i32())
expect(SEMANTIC_EVENT_SIZE).to_equal(68)
```

</details>

#### re-exports object registry and scenario correlator

- re-exports object registry and scenario correlator
   - Expected: obj_id equals `1`
   - Expected: registry.active_count() equals `1`
   - Expected: correlator.step_count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("re-exports object registry and scenario correlator")
var registry = ObjectRegistry.create()
val obj_id = registry.register(3, 4, 5)
var correlator = ScenarioCorrelator.from_scenario("checkout")
correlator.add_step("submit order", 1, 2)

expect(obj_id).to_equal(1)
expect(registry.active_count()).to_equal(1)
expect(correlator.step_count()).to_equal(1)
expect(correlator.summary()).to_contain("checkout")
```

</details>

#### re-exports trace writer and async timeline

- re-exports trace writer and async timeline
   - Expected: writer.event_count equals `0`
   - Expected: timeline.is_complete() is true
   - Expected: timeline.duration() equals `50`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("re-exports trace writer and async timeline")
val writer = TraceWriter.create("/tmp/simple-semantic.sst", 1024)
var timeline = AsyncTaskTimeline.create(10, 20)
timeline.add_entry(1, 100, AsyncTaskState.Spawned)
timeline.add_entry(2, 150, AsyncTaskState.Completed)

expect(writer.event_count).to_equal(0)
expect(timeline.is_complete()).to_equal(true)
expect(timeline.duration()).to_equal(50)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/gc_async_mut/replay/semantic/replay_semantic_facade_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering gc_async_mut replay semantic facades.
- gc_async_mut replay semantic facades

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

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `b8ed42dab7c5dd11ba2351365c9d2d757574a7587457b57eb1b1ede8e7b1b3cb`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b8ed42dab7c5dd11ba2351365c9d2d757574a7587457b57eb1b1ede8e7b1b3cb`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b8ed42dab7c5dd11ba2351365c9d2d757574a7587457b57eb1b1ede8e7b1b3cb`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/unit/lib/gc_async_mut/replay/semantic/replay_semantic_facade_spec.spl
mirror: doc/06_spec/unit/lib/gc_async_mut/replay/semantic/replay_semantic_facade_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/gc_async_mut/replay/semantic/replay_semantic_facade_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/gc_async_mut/replay/semantic/replay_semantic_facade_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/gc_async_mut/replay/semantic/replay_semantic_facade_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 6 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/lib/gc_async_mut/replay/semantic/replay_semantic_facade_spec.spl:17:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 're-exports semantic event records' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/gc_async_mut/replay/semantic/replay_semantic_facade_spec.spl:26:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 're-exports object registry and scenario correlator' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/gc_async_mut/replay/semantic/replay_semantic_facade_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 're-exports trace writer and async timeline' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
