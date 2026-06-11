# Game2d Time Facade Specification

> 1. set deterministic mode

<!-- sdn-diagram:id=game2d_time_facade_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=game2d_time_facade_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

game2d_time_facade_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=game2d_time_facade_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Game2d Time Facade Specification

## Scenarios

### gc_async_mut game2d time facade

#### re-exports deterministic callback time guard and seeded random

1. set deterministic mode
2. enter callback
   - Expected: now() equals `16666667`
3. seed random
4. seed random
   - Expected: random_u64() equals `first`
5. leave callback
6. set deterministic mode


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val state = TimeState.create()
expect(state.deterministic).to_equal(false)

set_deterministic_mode(true)
enter_callback(16666667)
expect(now()).to_equal(16666667)
seed_random(123)
val first = random_u64()
seed_random(123)
expect(random_u64()).to_equal(first)
expect(random_f64()).to_be_less_than(1.0)
expect(rand()).to_be_less_than(1.0)
leave_callback()
set_deterministic_mode(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/game2d/time/game2d_time_facade_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- gc_async_mut game2d time facade

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
