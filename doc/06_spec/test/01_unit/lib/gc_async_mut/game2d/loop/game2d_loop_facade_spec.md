# Game2d Loop Facade Specification

> <details>

<!-- sdn-diagram:id=game2d_loop_facade_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=game2d_loop_facade_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

game2d_loop_facade_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=game2d_loop_facade_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Game2d Loop Facade Specification

## Scenarios

### gc_async_mut game2d loop facade

<details>
<summary>Advanced: re-exports fixed-step loop driver accumulator helpers</summary>

#### re-exports fixed-step loop driver accumulator helpers

1. var driver = LoopDriver new
   - Expected: driver.fixed_step_ns equals `16666666`
   - Expected: driver.running is true
   - Expected: driver.consume_fixed_steps(10000000) equals `0`
   - Expected: driver.consume_fixed_steps(10000000) equals `1`
   - Expected: driver.accumulator_ns equals `3333334`
2. var fallback = LoopDriver new
   - Expected: fallback.fixed_step_ns equals `16666667`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var driver = LoopDriver.new(60)
expect(driver.fixed_step_ns).to_equal(16666666)
expect(driver.running).to_equal(true)
expect(driver.consume_fixed_steps(10000000)).to_equal(0)
expect(driver.consume_fixed_steps(10000000)).to_equal(1)
expect(driver.accumulator_ns).to_equal(3333334)

var fallback = LoopDriver.new(0)
expect(fallback.fixed_step_ns).to_equal(16666667)
```

</details>


</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/game2d/loop/game2d_loop_facade_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- gc_async_mut game2d loop facade

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
