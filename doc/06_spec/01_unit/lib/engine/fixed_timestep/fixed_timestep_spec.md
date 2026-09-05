# fixed_timestep_spec

> FixedTimestep — Unit Tests

<!-- sdn-diagram:id=fixed_timestep_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=fixed_timestep_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

fixed_timestep_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=fixed_timestep_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# fixed_timestep_spec

FixedTimestep — Unit Tests

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/engine/fixed_timestep/fixed_timestep_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

FixedTimestep — Unit Tests

Tests the shared fixed-timestep accumulator used by game_loop.spl and
game_loop3d.spl.  Covers creation, single-step advance, fractional advance,
alpha interpolation, and the spiral-of-death cap.

## Scenarios

### FixedTimestep

#### create sets fields correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ts = FixedTimestep.create(1.0 / 60.0, 5)
expect(ts.fixed_dt).to_be_greater_than(0.016)
expect(ts.fixed_dt).to_be_less_than(0.017)
expect(ts.max_substeps).to_equal(5)
expect(ts.accumulator).to_equal(0.0)
```

</details>

#### advance by exactly one fixed_dt returns 1 step

- var ts = FixedTimestep create
   - Expected: steps equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ts = FixedTimestep.create(1.0 / 60.0, 5)
val dt = 1.0 / 60.0
val steps = ts.advance(dt)
expect(steps).to_equal(1)
```

</details>

#### alpha is near zero after exactly one fixed_dt advance

- var ts = FixedTimestep create
- ts advance


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ts = FixedTimestep.create(1.0 / 60.0, 5)
val dt = 1.0 / 60.0
ts.advance(dt)
val alpha = ts.interpolation_alpha()
expect(alpha).to_be_greater_than(-0.001)
expect(alpha).to_be_less_than(0.001)
```

</details>

#### advance(0.025) with fixed_dt=0.01 returns 2 steps

- var ts = FixedTimestep create
   - Expected: steps equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ts = FixedTimestep.create(0.01, 5)
val steps = ts.advance(0.025)
expect(steps).to_equal(2)
```

</details>

#### advance(0.025) with fixed_dt=0.01 leaves alpha near 0.5

- var ts = FixedTimestep create
- ts advance


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ts = FixedTimestep.create(0.01, 5)
ts.advance(0.025)
val alpha = ts.interpolation_alpha()
# accumulator = 0.025 - 2*0.01 = 0.005; alpha = 0.005/0.01 = 0.5
expect(alpha).to_be_greater_than(0.49)
expect(alpha).to_be_less_than(0.51)
```

</details>

#### large frame_dt is capped at max_substeps

- var ts = FixedTimestep create
   - Expected: steps equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ts = FixedTimestep.create(1.0 / 60.0, 5)
val steps = ts.advance(10.0)
expect(steps).to_equal(5)
```

</details>

#### accumulator is drained to zero after cap

- var ts = FixedTimestep create
- ts advance
   - Expected: alpha equals `0.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ts = FixedTimestep.create(1.0 / 60.0, 5)
ts.advance(10.0)
# cap drains accumulator to 0.0
val alpha = ts.interpolation_alpha()
expect(alpha).to_equal(0.0)
```

</details>

#### accumulator stays below fixed_dt without cap

- var ts = FixedTimestep create
- ts advance


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ts = FixedTimestep.create(0.01, 5)
ts.advance(0.025)
# accumulator = 0.005, which is < 0.01
expect(ts.accumulator).to_be_less_than(0.01)
expect(ts.accumulator).to_be_greater_than(0.0)
```

</details>

#### alpha is zero when fixed_dt is zero

- var ts = FixedTimestep create
   - Expected: alpha equals `0.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ts = FixedTimestep.create(0.0, 5)
val alpha = ts.interpolation_alpha()
expect(alpha).to_equal(0.0)
```

</details>

#### zero frame_dt returns zero steps

- var ts = FixedTimestep create
   - Expected: steps equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ts = FixedTimestep.create(1.0 / 60.0, 5)
val steps = ts.advance(0.0)
expect(steps).to_equal(0)
```

</details>

#### accumulates across multiple frames

- var ts = FixedTimestep create
- ts advance
- ts advance
   - Expected: steps equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ts = FixedTimestep.create(0.1, 10)
# three frames of 0.04 s = 0.12 s total => 1 step, 0.02 s left
ts.advance(0.04)
ts.advance(0.04)
val steps = ts.advance(0.04)
expect(steps).to_equal(1)
expect(ts.accumulator).to_be_greater_than(0.019)
expect(ts.accumulator).to_be_less_than(0.021)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
