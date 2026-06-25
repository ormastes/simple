# RTOS PRNG Specification

> Verifies the RTOS PRNG API contract. Uses a simplified LCG inline since

<!-- sdn-diagram:id=random_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=random_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

random_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=random_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# RTOS PRNG Specification

Verifies the RTOS PRNG API contract. Uses a simplified LCG inline since

## At a Glance

| Field | Value |
|-------|-------|
| Category | Infrastructure  **Difficulty:** 2/5  **Status:** Implemented |
| Status | Active |
| Source | `test/01_unit/os/realtime/random_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Verifies the RTOS PRNG API contract. Uses a simplified LCG inline since
xoshiro256** bit-shift ops are too complex for interpreter i64 mode.

## Scenarios

### PRNG Seeding

#### rng_seed sets the state

1. rng seed
   - Expected: rng_get_state() equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
rng_seed(42)
expect(rng_get_state()).to_equal(42)
```

</details>

#### rng_seed with zero sets state to zero

1. rng seed
   - Expected: rng_get_state() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
rng_seed(0)
expect(rng_get_state()).to_equal(0)
```

</details>

### PRNG Determinism

#### same seed produces same first value

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = value_from_seed(42)
val b = value_from_seed(42)
expect(a).to_equal(b)
```

</details>

#### same seed produces same second value

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = second_value_from_seed(42)
val b = second_value_from_seed(42)
expect(a).to_equal(b)
```

</details>

#### different seeds produce different values

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = value_from_seed(1)
val b = value_from_seed(2)
expect(a == b).to_equal(false)
```

</details>

#### rng_next produces non-zero from non-zero seed

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = value_from_seed(123)
expect(v).to_be_greater_than(0)
```

</details>

### PRNG Bounded

#### rng_next_bounded with max=1 returns 0

1. rng seed
   - Expected: v equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
rng_seed(999)
val v = rng_next_bounded(1)
expect(v).to_equal(0)
```

</details>

#### rng_next_bounded with max=0 returns 0

1. rng seed
   - Expected: v equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
rng_seed(999)
val v = rng_next_bounded(0)
expect(v).to_equal(0)
```

</details>

#### rng_next_bounded stays below max

1. rng seed


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
rng_seed(42)
val v = rng_next_bounded(100)
expect(v).to_be_less_than(100)
expect(v).to_be_greater_than(-1)
```

</details>

### PRNG State Roundtrip

#### get_state returns current state

1. rng seed
2. rng next
3. rng set state
   - Expected: replayed equals `after_save`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
rng_seed(77)
rng_next()
val saved = rng_get_state()
val after_save = rng_next()
rng_set_state(saved)
val replayed = rng_next()
expect(replayed).to_equal(after_save)
```

</details>

#### set_state restores exact position

1. rng seed
2. rng next
3. rng next
4. rng set state
5. rng set state
   - Expected: v1 equals `v2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
rng_seed(55)
val saved = rng_get_state()
rng_next()
rng_next()
rng_set_state(saved)
val v1 = value_from_seed(55)
rng_set_state(saved)
val v2 = rng_next()
expect(v1).to_equal(v2)
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
