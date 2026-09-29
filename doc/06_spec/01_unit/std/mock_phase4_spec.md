# Mock Phase4 Specification

> Tests covering Mock Library - Phase 4 (Advanced Patterns).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 24 | 24 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Mock Phase4 Specification

## Scenarios

### Mock Library - Phase 4 (Advanced Patterns)

#### Conditional Returns

#### returns value based on argument condition

- returns value based on argument condition


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns value based on argument condition")
val cond_returns = ConditionalReturns.new()
cond_returns.add_condition(
    _1.len() > 0 and _1[0] == "user",
    "user_data"
)
cond_returns.set_default("unknown")
expect cond_returns.evaluate(["user"]) == "user_data"
expect cond_returns.evaluate(["admin"]) == "unknown"
```

</details>

#### checks multiple conditions in order

- checks multiple conditions in order


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("checks multiple conditions in order")
val cond = ConditionalReturns.new()
cond.add_condition(
    _1.len() > 0 and _1[0] == "GET",
    "retrieve"
)
cond.add_condition(
    _1.len() > 0 and _1[0] == "POST",
    "create"
)
cond.set_default("other")
expect cond.evaluate(["GET"]) == "retrieve"
expect cond.evaluate(["POST"]) == "create"
expect cond.evaluate(["DELETE"]) == "other"
```

</details>

#### returns default when no conditions match

- returns default when no conditions match


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns default when no conditions match")
val cond = ConditionalReturns.new()
cond.add_condition(
    _1.len() == 0,
    "empty"
)
cond.set_default("fallback")
expect cond.evaluate(["something"]) == "fallback"
```

</details>

#### Call Chain Tracking

#### tracks parent-child call relationships

- tracks parent-child call relationships


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("tracks parent-child call relationships")
val tracker = CallChainTracker.new()
val call1 = CallRecord(args: ["parent"], timestamp: 0, call_number: 0)
val id1 = tracker.start_chain(-1, call1)
expect id1 == 0
val call2 = CallRecord(args: ["child"], timestamp: 0, call_number: 1)
val id2 = tracker.start_chain(id1, call2)
expect id2 == 1
tracker.add_child(parent_id=id1, child_id=id2)
val all_chains = tracker.get_all_chains()
expect all_chains.len() == 2
```

</details>

#### retrieves chain by parent id

- retrieves chain by parent id


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("retrieves chain by parent id")
val tracker = CallChainTracker.new()
val call = CallRecord(args: ["test"], timestamp: 0, call_number: 0)
val id = tracker.start_chain(5, call)
expect tracker.get_chain(5).is_some()
```

</details>

#### starts multiple independent chains

- starts multiple independent chains


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("starts multiple independent chains")
val tracker = CallChainTracker.new()
val call1 = CallRecord(args: ["a"], timestamp: 0, call_number: 0)
val call2 = CallRecord(args: ["b"], timestamp: 0, call_number: 1)
val id1 = tracker.start_chain(-1, call1)
val id2 = tracker.start_chain(-1, call2)
expect id1 != id2
expect tracker.get_all_chains().len() == 2
```

</details>

#### State-Based Behavior Sequences

#### transitions through behavior states

- transitions through behavior states


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("transitions through behavior states")
val behavior = BehaviorSequence.new("init")
behavior.add_state(name="init", return_value="initializing", next_state=Some("ready"))
behavior.add_state(name="ready", return_value="operational", next_state=Some("shutdown"))
behavior.add_state(name="shutdown", return_value="stopped", next_state=nil)
expect behavior.transition() == Some("initializing")
expect behavior.current_state == "ready"
expect behavior.transition() == Some("operational")
expect behavior.current_state == "shutdown"
```

</details>

#### handles terminal states

- handles terminal states


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles terminal states")
val behavior = BehaviorSequence.new("start")
behavior.add_state(name="start", return_value="started", next_state=Some("end"))
behavior.add_state(name="end", return_value="finished", next_state=nil)
behavior.transition()
expect behavior.current_state == "end"
behavior.transition()
expect behavior.current_state == "end"
```

</details>

#### resets to initial state

- resets to initial state


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("resets to initial state")
val behavior = BehaviorSequence.new("a")
behavior.add_state(name="a", return_value="value_a", next_state=Some("b"))
behavior.add_state(name="b", return_value="value_b", next_state=nil)
behavior.transition()
expect behavior.current_state == "b"
behavior.reset_to("a")
expect behavior.current_state == "a"
```

</details>

#### manages complex state machines

- manages complex state machines


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("manages complex state machines")
val behavior = BehaviorSequence.new("idle")
behavior.add_state(name="idle", return_value="waiting", next_state=Some("running"))
behavior.add_state(name="running", return_value="executing", next_state=Some("paused"))
behavior.add_state(name="paused", return_value="suspended", next_state=Some("running"))
expect behavior.transition() == Some("waiting")
expect behavior.transition() == Some("executing")
expect behavior.transition() == Some("suspended")
```

</details>

#### Mock Snapshots

#### captures mock state at a point in time

- captures mock state at a point in time


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("captures mock state at a point in time")
val mockfn = MockFunction.new("service")
mockfn.record_call(["arg1"])
mockfn.record_call(["arg2"])
val snapshot = MockSnapshot.from_mock(mockfn)
expect snapshot.call_count == 2
expect snapshot.last_args[0] == "arg2"
```

</details>

#### tracks expectation satisfaction in snapshot

- tracks expectation satisfaction in snapshot


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("tracks expectation satisfaction in snapshot")
val mockfn = MockFunction.new("verified")
mockfn.expect_call(1)
mockfn.record_call([])
val snapshot = MockSnapshot.from_mock(mockfn)
expect snapshot.expectations_met == true
```

</details>

#### shows when expectations are not met

- shows when expectations are not met


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("shows when expectations are not met")
val mockfn = MockFunction.new("unverified")
mockfn.expect_call(2)
mockfn.record_call([])
val snapshot = MockSnapshot.from_mock(mockfn)
expect snapshot.expectations_met == false
```

</details>

#### generates snapshot summary

- generates snapshot summary


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("generates snapshot summary")
val mockfn = MockFunction.new("test")
mockfn.record_call([])
val snapshot = MockSnapshot.from_mock(mockfn)
val summary = snapshot.summary()
expect summary.contains("1")
expect summary.contains("Snapshot")
```

</details>

#### Mock Composition

#### groups multiple mocks

- groups multiple mocks


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("groups multiple mocks")
val composition = MockComposition.new()
val m1 = MockFunction.new("fn1")
val m2 = MockFunction.new("fn2")
composition.add_mock(m1)
composition.add_mock(m2)
expect composition.mocks.len() == 2
```

</details>

#### verifies all mocks in composition

- verifies all mocks in composition


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("verifies all mocks in composition")
val composition = MockComposition.new()
val m1 = MockFunction.new("fn1")
val m2 = MockFunction.new("fn2")
m1.expect_call(1)
m2.expect_call(1)
m1.record_call([])
m2.record_call([])
composition.add_mock(m1)
composition.add_mock(m2)
expect composition.verify_all() == true
```

</details>

#### fails verification if any mock fails

- fails verification if any mock fails


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fails verification if any mock fails")
val composition = MockComposition.new()
val m1 = MockFunction.new("fn1")
val m2 = MockFunction.new("fn2")
m1.expect_call(1)
m2.expect_call(2)
m1.record_call([])
m2.record_call([])
composition.add_mock(m1)
composition.add_mock(m2)
expect composition.verify_all() == false
```

</details>

#### counts total calls across all mocks

- counts total calls across all mocks


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("counts total calls across all mocks")
val composition = MockComposition.new()
val m1 = MockFunction.new("fn1")
val m2 = MockFunction.new("fn2")
m1.record_call([])
m1.record_call([])
m2.record_call([])
composition.add_mock(m1)
composition.add_mock(m2)
expect composition.get_total_calls() == 3
```

</details>

#### resets all mocks in composition

- resets all mocks in composition


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("resets all mocks in composition")
val composition = MockComposition.new()
val m1 = MockFunction.new("fn1")
val m2 = MockFunction.new("fn2")
m1.record_call([])
m2.record_call([])
composition.add_mock(m1)
composition.add_mock(m2)
expect composition.get_total_calls() == 2
composition.reset_all()
expect composition.get_total_calls() == 0
```

</details>

#### generates composition summary

- generates composition summary


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("generates composition summary")
val composition = MockComposition.new()
val m1 = MockFunction.new("api")
val m2 = MockFunction.new("db")
m1.record_call(["GET"])
m2.record_call(["SELECT"])
composition.add_mock(m1)
composition.add_mock(m2)
val summary = composition.summary()
expect summary.contains("2")
expect summary.contains("mocks")
expect summary.contains("2")
```

</details>

#### Complex Phase 4 Scenarios

#### combines conditional returns with snapshots

- combines conditional returns with snapshots


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("combines conditional returns with snapshots")
val cond = ConditionalReturns.new()
cond.add_condition(
    _1.len() > 0 and _1[0] == "cache",
    "cached_value"
)
cond.set_default("fresh_value")
expect cond.evaluate(["cache"]) == "cached_value"
expect cond.evaluate(["fetch"]) == "fresh_value"
```

</details>

#### uses state machine with mock composition

- uses state machine with mock composition


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("uses state machine with mock composition")
val composition = MockComposition.new()
val behavior = BehaviorSequence.new("init")
behavior.add_state(name="init", return_value="starting", next_state=Some("running"))
behavior.add_state(name="running", return_value="operational", next_state=nil)
val m1 = MockFunction.new("startup")
val m2 = MockFunction.new("service")
composition.add_mock(m1)
composition.add_mock(m2)
m1.record_call([])
m2.record_call([])
expect composition.get_total_calls() == 2
expect behavior.transition() == Some("starting")
```

</details>

#### chains calls and tracks with snapshots

- chains calls and tracks with snapshots


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("chains calls and tracks with snapshots")
val tracker = CallChainTracker.new()
val mockfn = MockFunction.new("main")
val call1 = CallRecord(args: ["init"], timestamp: 0, call_number: 0)
val call2 = CallRecord(args: ["process"], timestamp: 0, call_number: 1)
val id1 = tracker.start_chain(-1, call1)
val id2 = tracker.start_chain(id1, call2)
tracker.add_child(parent_id=id1, child_id=id2)
mockfn.record_call(["init"])
mockfn.record_call(["process"])
val snapshot = MockSnapshot.from_mock(mockfn)
expect snapshot.call_count == 2
```

</details>

#### manages complex multi-mock workflow

- manages complex multi-mock workflow


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("manages complex multi-mock workflow")
val api_mock = MockFunction.new("api")
val db_mock = MockFunction.new("db")
val cache_mock = MockFunction.new("cache")
val composition = MockComposition.new()
composition.add_mock(api_mock)
composition.add_mock(db_mock)
composition.add_mock(cache_mock)
api_mock.record_call(["GET", "/users"])
db_mock.record_call(["SELECT", "users"])
cache_mock.record_call(["get", "users"])
expect composition.get_total_calls() == 3
val summary = composition.summary()
expect summary.contains("3")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/std/mock_phase4_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Mock Library - Phase 4 (Advanced Patterns).
- Mock Library - Phase 4 (Advanced Patterns)

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 24 |
| Active scenarios | 24 |
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

- Canonical SPipe generation for source `387c65f8e5f10d8d7f185b1793af77009676a39c2049baf446f290133483c420`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `387c65f8e5f10d8d7f185b1793af77009676a39c2049baf446f290133483c420`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `387c65f8e5f10d8d7f185b1793af77009676a39c2049baf446f290133483c420`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/std/mock_phase4_spec.spl
mirror: doc/06_spec/01_unit/std/mock_phase4_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/std/mock_phase4_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/std/mock_phase4_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/std/mock_phase4_spec.spl:347:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns value based on argument condition' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/std/mock_phase4_spec.spl:359:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'checks multiple conditions in order' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/std/mock_phase4_spec.spl:376:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns default when no conditions match' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
