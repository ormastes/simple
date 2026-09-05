# what_if_spec

> Office sheets What-If Analysis spec.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# what_if_spec

Office sheets What-If Analysis spec.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/office/sheets/what_if_spec.spl` |
| Updated | 2026-08-18 |
| Generator | `simple spipe-docgen` (Simple) |

Office sheets What-If Analysis spec.

Hand-computed tests for What-If Analysis over a simple linear model
f(x) = slope*x + intercept: one-variable data tables, Goal Seek,
Scenario Manager, and two-variable data tables.

## Scenarios

### model_eval: linear model evaluation
_f(x) = 2x + 3._

#### evaluates f(5) = 2*5+3 = 13

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val model = model_new(2, 3)
expect(model_eval(model, 5)).to_equal(13)
```

</details>

### data_table_1d: one-variable data table
_Evaluate f(x) = 2x+3 across a list of inputs._

#### produces one line per input in order

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val model = model_new(2, 3)
val rows = data_table_1d(model, [0, 1, 2])
expect(rows.len()).to_equal(3)
expect(rows[0]).to_equal("0 -> 3")
expect(rows[1]).to_equal("1 -> 5")
expect(rows[2]).to_equal("2 -> 7")
```

</details>

### goal_seek: algebraic solve for x
_x = (target_y - intercept) / slope for f(x) = 2x+3._

#### solves target 13 -> x=5

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val model = model_new(2, 3)
expect(goal_seek(model, 13)).to_equal(5)
```

</details>

#### solves target 3 -> x=0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val model = model_new(2, 3)
expect(goal_seek(model, 3)).to_equal(0)
```

</details>

#### returns 0 for a degenerate zero-slope model

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val model = model_new(0, 3)
expect(goal_seek(model, 3)).to_equal(0)
```

</details>

### scenario_results and scenario_best: Scenario Manager
_Scenarios Low(x=1) and High(x=10) over f(x) = 2x+3._

#### summarizes each scenario as name: x=<x> -> <f(x)>

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val model = model_new(2, 3)
val low = scenario_new("Low", 1)
val high = scenario_new("High", 10)
val rows = scenario_results(model, [low, high])
expect(rows.len()).to_equal(2)
expect(rows[0]).to_equal("Low: x=1 -> 5")
expect(rows[1]).to_equal("High: x=10 -> 23")
```

</details>

#### picks the scenario with the highest f(x)

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val model = model_new(2, 3)
val low = scenario_new("Low", 1)
val high = scenario_new("High", 10)
val best = scenario_best(model, [low, high])
expect(best).to_equal("High")
```

</details>

#### breaks ties by keeping the first scenario

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val model = model_new(2, 3)
val first_tie = scenario_new("First", 5)
val second_tie = scenario_new("Second", 5)
val best = scenario_best(model, [first_tie, second_tie])
expect(best).to_equal("First")
```

</details>

### data_table_2d: two-variable data table

#### evaluates slope*x+intercept for every (slope, intercept) pair in row-major order

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rows = data_table_2d(99, 99, [1, 2], [0, 10], 5)
expect(rows.len()).to_equal(4)
expect(rows[0]).to_equal("s=1 b=0 -> 5")
expect(rows[1]).to_equal("s=1 b=10 -> 15")
expect(rows[2]).to_equal("s=2 b=0 -> 10")
expect(rows[3]).to_equal("s=2 b=10 -> 20")
```

</details>

### deliberate-fail probe (fixed to green below)

#### sanity: row count matches slopes.len() * intercepts.len()

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rows = data_table_2d(0, 0, [1, 2], [0, 10], 5)
expect(rows.len()).to_equal(4)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
