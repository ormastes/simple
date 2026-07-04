# Physics Sleeping Specification

> <details>

<!-- sdn-diagram:id=physics_sleeping_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=physics_sleeping_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

physics_sleeping_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=physics_sleeping_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Physics Sleeping Specification

## Scenarios

### Physics2 IslandManager sleeping

#### bodies start awake

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = make_manager()
expect(m.is_island_sleeping(0)).to_equal(false)
```

</details>

#### low KE puts island to sleep

1. var m = make manager
2. m update sleep
   - Expected: m.is_island_sleeping(0) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var m = make_manager()
m.update_sleep(0, 0.001, 0.6)
expect(m.is_island_sleeping(0)).to_equal(true)
```

</details>

#### high KE wakes island

1. var m = make manager
2. m update sleep
3. m update sleep
   - Expected: m.is_island_sleeping(0) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var m = make_manager()
m.update_sleep(0, 0.001, 0.6)
m.update_sleep(0, 1.0, 0.1)
expect(m.is_island_sleeping(0)).to_equal(false)
```

</details>

#### union merges islands

1. var m = make manager
2. m union
   - Expected: r0 equals `r1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var m = make_manager()
m.union(0, 1)
val r0 = m.find(0)
val r1 = m.find(1)
expect(r0).to_equal(r1)
```

</details>

#### wake propagates to merged island

1. var m = make manager
2. m union
3. m update sleep
4. m update sleep
5. m wake island
   - Expected: m.is_island_sleeping(0) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var m = make_manager()
m.union(0, 1)
m.update_sleep(0, 0.001, 0.6)
m.update_sleep(1, 0.001, 0.6)
m.wake_island(1)
expect(m.is_island_sleeping(0)).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/engine/physics_sleeping_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Physics2 IslandManager sleeping

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
