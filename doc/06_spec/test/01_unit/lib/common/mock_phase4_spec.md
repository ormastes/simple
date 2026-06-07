# Mock Phase4 Specification

> 1.  1 len

<!-- sdn-diagram:id=mock_phase4_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=mock_phase4_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

mock_phase4_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=mock_phase4_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

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

1.  1 len
2. cond returns set default
3. expect cond returns evaluate
4. expect cond returns evaluate


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1.  1 len
2.  1 len
3. cond set default
4. expect cond evaluate
5. expect cond evaluate
6. expect cond evaluate


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1.  1 len
2. cond set default
3. expect cond evaluate


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. tracker add child
2. expect all chains len


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. expect tracker get chain


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tracker = CallChainTracker.new()
val call = CallRecord(args: ["test"], timestamp: 0, call_number: 0)
val id = tracker.start_chain(5, call)
expect tracker.get_chain(5).is_some()
```

</details>

#### starts multiple independent chains

1. expect tracker get all chains


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. behavior add state
2. behavior add state
3. behavior add state
4. expect behavior transition
5. expect behavior transition


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. behavior add state
2. behavior add state
3. behavior transition
4. behavior transition


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. behavior add state
2. behavior add state
3. behavior transition
4. behavior reset to


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. behavior add state
2. behavior add state
3. behavior add state
4. expect behavior transition
5. expect behavior transition
6. expect behavior transition


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. mockfn record call
2. mockfn record call


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mockfn = MockFunction.new("service")
mockfn.record_call(["arg1"])
mockfn.record_call(["arg2"])
val snapshot = MockSnapshot.from_mock(mockfn)
expect snapshot.call_count == 2
expect snapshot.last_args[0] == "arg2"
```

</details>

#### tracks expectation satisfaction in snapshot

1. mockfn expect call
2. mockfn record call


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mockfn = MockFunction.new("verified")
mockfn.expect_call(1)
mockfn.record_call([])
val snapshot = MockSnapshot.from_mock(mockfn)
expect snapshot.expectations_met == true
```

</details>

#### shows when expectations are not met

1. mockfn expect call
2. mockfn record call


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mockfn = MockFunction.new("unverified")
mockfn.expect_call(2)
mockfn.record_call([])
val snapshot = MockSnapshot.from_mock(mockfn)
expect snapshot.expectations_met == false
```

</details>

#### generates snapshot summary

1. mockfn record call
2. expect summary contains
3. expect summary contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. composition add mock
2. composition add mock
3. expect composition mocks len


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val composition = MockComposition.new()
val m1 = MockFunction.new("fn1")
val m2 = MockFunction.new("fn2")
composition.add_mock(m1)
composition.add_mock(m2)
expect composition.mocks.len() == 2
```

</details>

#### verifies all mocks in composition

1. m1 expect call
2. m2 expect call
3. m1 record call
4. m2 record call
5. composition add mock
6. composition add mock
7. expect composition verify all


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. m1 expect call
2. m2 expect call
3. m1 record call
4. m2 record call
5. composition add mock
6. composition add mock
7. expect composition verify all


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. m1 record call
2. m1 record call
3. m2 record call
4. composition add mock
5. composition add mock
6. expect composition get total calls


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. m1 record call
2. m2 record call
3. composition add mock
4. composition add mock
5. expect composition get total calls
6. composition reset all
7. expect composition get total calls


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. composition add mock
2. composition add mock
3. m1 record call
4. m2 record call
5. expect summary contains
6. expect summary contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val composition = MockComposition.new()
val m1 = MockFunction.new("api")
val m2 = MockFunction.new("db")
composition.add_mock(m1)
composition.add_mock(m2)
m1.record_call(["GET"])
m2.record_call(["SELECT"])
val summary = composition.summary()
expect summary.contains("2")
expect summary.contains("mocks")
```

</details>

#### Complex Phase 4 Scenarios

#### combines conditional returns with snapshots

1.  1 len
2. cond set default
3. expect cond evaluate
4. expect cond evaluate


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. behavior add state
2. behavior add state
3. composition add mock
4. composition add mock
5. m1 record call
6. m2 record call
7. expect composition get total calls
8. expect behavior transition


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. tracker add child
2. mockfn record call
3. mockfn record call


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. composition add mock
2. composition add mock
3. composition add mock
4. api mock record call
5. db mock record call
6. cache mock record call
7. expect composition get total calls
8. expect summary contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
| Source | `test/01_unit/lib/common/mock_phase4_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
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
