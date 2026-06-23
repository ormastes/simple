# Replay Scenario Specification

> <details>

<!-- sdn-diagram:id=replay_scenario_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=replay_scenario_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

replay_scenario_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=replay_scenario_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Replay Scenario Specification

## Scenarios

### ScenarioCorrelator creation

#### from_scenario sets scenario_name

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sc = ScenarioCorrelator.from_scenario("user logs in")
expect(sc.scenario_name).to_equal("user logs in")
```

</details>

#### from_scenario starts with zero steps

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sc = ScenarioCorrelator.from_scenario("checkout flow")
expect(sc.step_count()).to_equal(0)
```

</details>

### ScenarioCorrelator add_step

#### add_step increases step_count

1. var sc = ScenarioCorrelator from scenario
2. sc add step
   - Expected: sc.step_count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sc = ScenarioCorrelator.from_scenario("login")
sc.add_step("open login page", 0, 100)
expect(sc.step_count()).to_equal(1)
```

</details>

#### add_step stores step name and event range

1. var sc = ScenarioCorrelator from scenario
2. sc add step
   - Expected: st.name equals `submit credentials`
   - Expected: st.start_event_id equals `100`
   - Expected: st.end_event_id equals `250`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sc = ScenarioCorrelator.from_scenario("login")
sc.add_step("submit credentials", 100, 250)
val st = sc.get_step(0)
expect(st.name).to_equal("submit credentials")
expect(st.start_event_id).to_equal(100)
expect(st.end_event_id).to_equal(250)
```

</details>

#### multiple add_step calls maintain order

1. var sc = ScenarioCorrelator from scenario
2. sc add step
3. sc add step
4. sc add step
   - Expected: sc.step_count() equals `3`
   - Expected: first.name equals `add to cart`
   - Expected: last.name equals `confirm`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sc = ScenarioCorrelator.from_scenario("purchase")
sc.add_step("add to cart", 0, 50)
sc.add_step("checkout", 51, 200)
sc.add_step("confirm", 201, 300)
expect(sc.step_count()).to_equal(3)
val first = sc.get_step(0)
expect(first.name).to_equal("add to cart")
val last = sc.get_step(2)
expect(last.name).to_equal("confirm")
```

</details>

### ScenarioCorrelator match_functions

#### match_functions attaches patterns to a step

1. var sc = ScenarioCorrelator from scenario
2. sc add step
3. sc match functions
   - Expected: st.matched_functions.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sc = ScenarioCorrelator.from_scenario("login")
sc.add_step("authenticate", 0, 100)
sc.match_functions(0, ["auth.login", "auth.verify_password"])
val st = sc.get_step(0)
expect(st.matched_functions.len()).to_equal(2)
```

</details>

#### match_functions does not affect other steps

1. var sc = ScenarioCorrelator from scenario
2. sc add step
3. sc add step
4. sc match functions
   - Expected: sb.matched_functions.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sc = ScenarioCorrelator.from_scenario("multi")
sc.add_step("step-a", 0, 10)
sc.add_step("step-b", 11, 20)
sc.match_functions(0, ["fn_a"])
val sb = sc.get_step(1)
expect(sb.matched_functions.len()).to_equal(0)
```

</details>

### ScenarioCorrelator match_objects

#### match_objects attaches object ids to a step

1. var sc = ScenarioCorrelator from scenario
2. sc add step
3. sc match objects
   - Expected: st.matched_objects.len() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sc = ScenarioCorrelator.from_scenario("alloc test")
sc.add_step("allocate user", 0, 50)
sc.match_objects(0, [101, 102, 103])
val st = sc.get_step(0)
expect(st.matched_objects.len()).to_equal(3)
```

</details>

### ScenarioCorrelator summary

#### summary contains scenario name

1. var sc = ScenarioCorrelator from scenario


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sc = ScenarioCorrelator.from_scenario("dashboard load")
val out = sc.summary()
expect(out).to_contain("dashboard load")
```

</details>

#### summary contains step count

1. var sc = ScenarioCorrelator from scenario
2. sc add step
3. sc add step


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sc = ScenarioCorrelator.from_scenario("flow")
sc.add_step("step one", 0, 10)
sc.add_step("step two", 11, 20)
val out = sc.summary()
expect(out).to_contain("2")
```

</details>

### ScenarioStep to_text

#### to_text contains step name

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val st = ScenarioStep(
    name: "render page",
    start_event_id: 10,
    end_event_id: 99,
    matched_functions: [],
    matched_objects: []
)
val s = st.to_text()
expect(s).to_contain("render page")
```

</details>

#### to_text contains event range

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val st = ScenarioStep(
    name: "submit",
    start_event_id: 5,
    end_event_id: 42,
    matched_functions: [],
    matched_objects: []
)
val s = st.to_text()
expect(s).to_contain("5")
expect(s).to_contain("42")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/replay_scenario_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- ScenarioCorrelator creation
- ScenarioCorrelator add_step
- ScenarioCorrelator match_functions
- ScenarioCorrelator match_objects
- ScenarioCorrelator summary
- ScenarioStep to_text

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
