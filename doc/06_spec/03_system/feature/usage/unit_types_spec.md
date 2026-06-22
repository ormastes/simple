# Unit Types Specification

> Tests for semantic unit types that add compile-time dimensional safety to numeric values.

<!-- sdn-diagram:id=unit_types_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=unit_types_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

unit_types_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=unit_types_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 21 | 21 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Unit Types Specification

Tests for semantic unit types that add compile-time dimensional safety to numeric values.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #UNIT-001 |
| Category | Language \| Types |
| Status | Implemented |
| Source | `test/03_system/feature/usage/unit_types_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests for semantic unit types that add compile-time dimensional safety
to numeric values.

## Scenarios

### Standalone Units

#### defines standalone unit type

1. expect user id value


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
unit UserId: i64 as uid
val user_id = 42_uid
expect user_id.value() == 42
```

</details>

#### performs arithmetic with units

1. expect


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
unit Score: i64 as pts
val a = 100_pts
val b = 50_pts
expect (a + b).value() == 150
```

</details>

#### gets value from unit

1. expect d value


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val d = 42_km
expect d.value() == 42
```

</details>

#### gets suffix from unit

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val d = 100_bytes
val s = d.suffix()
expect s == "bytes"
```

</details>

#### converts unit to string

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val d = 5_km
val s = d.to_string()
expect s == "5_km"
```

</details>

### Unit Families

#### defines unit family

1. unit length
2. expect d value


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
unit length(base: f64): m = 1.0, km = 1000.0
val d = 5000.0_m
expect d.value() == 5000.0
```

</details>

### Unit Arithmetic

#### allows same-family addition

1. unit length
2. allow add
3. allow sub
4. expect


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
unit length(base: f64): m = 1.0, km = 1000.0:
    allow add(length) -> length
    allow sub(length) -> length
val a = 100_m
val b = 50_m
expect (a + b).value() == 150
```

</details>

#### allows same-family subtraction

1. unit length
2. allow sub
3. expect


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
unit length(base: f64): m = 1.0, km = 1000.0:
    allow sub(length) -> length
val a = 100_m
val b = 30_m
expect (a - b).value() == 70
```

</details>

#### allows scaling by scalar

1. unit length
2. expect scaled value


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
unit length(base: f64): m = 1.0
val d = 10_m
val scaled = d * 3
expect scaled.value() == 30
```

</details>

#### allows comparison always

1. unit length


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
unit length(base: f64): m = 1.0
val a = 100_m
val b = 50_m
expect a > b
```

</details>

### Compound Units

#### defines compound unit

1. unit length
2. unit time


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
unit length(base: f64): m = 1.0
unit time(base: f64): s = 1.0
unit velocity = length / time
expect 1 == 1
```

</details>

#### computes velocity from division

1. unit length
2. unit time
3. expect speed value


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
unit length(base: f64): m = 1.0
unit time(base: f64): s = 1.0
unit velocity = length / time
val dist = 100_m
val dur = 10_s
val speed = dist / dur
expect speed.value() == 10
```

</details>

#### cancels same units in division

1. unit length
2. expect ratio value


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
unit length(base: f64): m = 1.0
val dist1 = 100_m
val dist2 = 20_m
val ratio = dist1 / dist2
expect ratio.value() == 5
```

</details>

#### defines area from multiplication

1. unit length
2. expect a value


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
unit length(base: f64): m = 1.0
unit area = length * length
val width = 10_m
val height = 5_m
val a = width * height
expect a.value() == 50
```

</details>

### SI Prefixes

#### uses kilo prefix

1. unit length
2. expect dist value


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
unit length(base: f64): m = 1.0
val dist = 5_km
expect dist.value() == 5000
```

</details>

#### uses mega prefix

1. unit length
2. expect dist value


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
unit length(base: f64): m = 1.0
val dist = 2_Mm
expect dist.value() == 2000000.0
```

</details>

#### uses milli prefix

1. unit time
2. expect dur value


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
unit time(base: f64): s = 1.0
val dur = 500_ms
expect dur.value() < 1.0
```

</details>

### Unit Type Inference

#### accepts correct unit parameter

1. unit length
2. fn double distance
3. expect double distance


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
unit length(base: f64): m = 1.0, km = 1000.0
fn double_distance(d: length) -> length:
    return d + d
val dist = 5_km
expect double_distance(dist).value() == 10
```

</details>

#### returns correct unit type

1. unit length
2. fn get distance
3. expect get distance


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
unit length(base: f64): m = 1.0, km = 1000.0
fn get_distance() -> length:
    return 10_m
expect get_distance().value() == 10
```

</details>

### Semantic Wrapper APIs

#### uses unit wrappers in public function signatures

1. pub fn current user
2. pub fn same user
   - Expected: user_id.value() equals `42`
   - Expected: same_user(user_id).value() equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
unit UserId: i64 as uid

pub fn current_user() -> UserId:
    return 42_uid

pub fn same_user(user_id: UserId) -> UserId:
    return user_id

val user_id = current_user()
expect(user_id.value()).to_equal(42)
expect(same_user(user_id).value()).to_equal(42)
```

</details>

#### supports helper functions around semantic wrapper units

1. fn plus two
   - Expected: total.value() equals `44`
   - Expected: total.suffix() equals `ms`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
unit Milliseconds: u64 as ms

fn plus_two(value: Milliseconds) -> Milliseconds:
    return value + 2_ms

val base = 42_ms
val total = plus_two(base)

expect(total.value()).to_equal(44)
expect(total.suffix()).to_equal("ms")
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
