# random_pure_spec

> Advance both module LCG and inline reference LCG n steps from seed=123

<!-- sdn-diagram:id=random_pure_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=random_pure_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

random_pure_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=random_pure_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 21 | 21 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# random_pure_spec

Advance both module LCG and inline reference LCG n steps from seed=123

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/random_pure_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Advance both module LCG and inline reference LCG n steps from seed=123
    and check they produce identical outputs.

## Scenarios

### random_pure — seeding and determinism

#### seed then lcg_next matches known LCG output (seed=42 step 1)

1. seed
   - Expected: v equals `1083814273`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
seed(42)
val v = lcg_next()
expect(v).to_equal(1083814273)
```

</details>

#### second lcg_next after seed=42 matches known output

1. seed
2. lcg next
   - Expected: v2 equals `378494188`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
seed(42)
lcg_next()
val v2 = lcg_next()
expect(v2).to_equal(378494188)
```

</details>

#### same seed produces same first value

1. seed
2. seed
   - Expected: a1 equals `b1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
seed(42)
val a1 = lcg_next()
seed(42)
val b1 = lcg_next()
expect(a1).to_equal(b1)
```

</details>

#### same seed produces same second value

1. seed
2. lcg next
3. seed
4. lcg next
   - Expected: a2 equals `b2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
seed(42)
lcg_next()
val a2 = lcg_next()
seed(42)
lcg_next()
val b2 = lcg_next()
expect(a2).to_equal(b2)
```

</details>

#### different seeds produce different first values

1. seed
2. seed
   - Expected: differ is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
seed(42)
val a = lcg_next()
seed(99)
val b = lcg_next()
val differ = a != b
expect(differ).to_equal(true)
```

</details>

### random_pure — getstate / setstate

#### getstate returns seed value before any advance

1. seed
   - Expected: s equals `7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
seed(7)
val s = getstate()
expect(s).to_equal(7)
```

</details>

#### setstate restores state for exact replay

1. seed
2. lcg next
3. setstate
   - Expected: v1 equals `v2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
seed(42)
lcg_next()
val saved = getstate()
val v1 = lcg_next()
setstate(saved)
val v2 = lcg_next()
expect(v1).to_equal(v2)
```

</details>

#### setstate(42) produces same first output as seed(42)

1. seed
2. setstate
   - Expected: direct equals `via_set`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
seed(42)
val direct = lcg_next()
setstate(42)
val via_set = lcg_next()
expect(direct).to_equal(via_set)
```

</details>

### random_pure — randint range

#### randint(0,0) returns 0

1. seed
   - Expected: v equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
seed(42)
val v = randint(0, 0)
expect(v).to_equal(0)
```

</details>

#### randint when min > max returns min

1. seed
   - Expected: v equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
seed(42)
val v = randint(10, 5)
expect(v).to_equal(10)
```

</details>

#### randint(1,10) first call is in range

1. seed
   - Expected: ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
seed(42)
val v = randint(1, 10)
val ok = v >= 1 and v <= 10
expect(ok).to_equal(true)
```

</details>

#### randint(1,10) stays in range for 50 calls

1. seed
   - Expected: ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
seed(42)
val ok = check_randint_in_range(1, 10, 50)
expect(ok).to_equal(true)
```

</details>

#### randint covers low half of range in 100 calls

1. seed


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
seed(42)
val low = count_low_half(100)
expect(low).to_be_greater_than(10)
```

</details>

#### randint covers high half of range in 100 calls

1. seed


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
seed(42)
val low = count_low_half(100)
val high = 100 - low
expect(high).to_be_greater_than(10)
```

</details>

### random_pure — random float

#### random() first call is in [0.0, 1.0)

1. seed
   - Expected: ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
seed(42)
val v = random()
val ok = v >= 0.0 and v < 1.0
expect(ok).to_equal(true)
```

</details>

#### random() is non-constant across two calls

1. seed
   - Expected: differ is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
seed(42)
val v1 = random()
val v2 = random()
val differ = v1 != v2
expect(differ).to_equal(true)
```

</details>

#### random() stays in [0.0, 1.0) for 50 calls

1. seed
   - Expected: ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
seed(42)
val ok = check_random_in_unit(50)
expect(ok).to_equal(true)
```

</details>

### random_pure — LcgRng struct API

#### lcg_rng seed=42 first advance matches known output

1. var rng = lcg rng
2. rng = lcg advance
   - Expected: v equals `1083814273`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var rng = lcg_rng(42)
rng = lcg_advance(rng)
val v = lcg_value(rng)
expect(v).to_equal(1083814273)
```

</details>

#### lcg_rng seed=42 second advance matches known output

1. var rng = lcg rng
2. rng = lcg advance
3. rng = lcg advance
   - Expected: v equals `378494188`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var rng = lcg_rng(42)
rng = lcg_advance(rng)
rng = lcg_advance(rng)
val v = lcg_value(rng)
expect(v).to_equal(378494188)
```

</details>

#### lcg_rng struct value is independent of module-level seed

1. seed
2. var rng = lcg rng
3. rng = lcg advance
   - Expected: struct_val equals `1083814273`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
seed(99)
var rng = lcg_rng(42)
rng = lcg_advance(rng)
val struct_val = lcg_value(rng)
expect(struct_val).to_equal(1083814273)
```

</details>

### random_pure — matches inline reference LCG

#### lcg_next matches inline reference for 5 steps from seed=123

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ok = check_lcg_matches_ref(5)
expect(ok).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 21 |
| Active scenarios | 21 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
