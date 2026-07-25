# curry_partial_spec

> Curry and Partial Application

<!-- sdn-diagram:id=curry_partial_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=curry_partial_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

curry_partial_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=curry_partial_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# curry_partial_spec

Curry and Partial Application

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #FUNC-010 |
| Category | Functional Programming |
| Status | Active |
| Source | `test/03_system/feature/usage/curry_partial_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Curry and Partial Application

Standard library functions for currying and partial application.
`curry2(f)` converts a 2-arg function into nested single-arg lambdas.
`partial1(f, a)` fixes the first argument of a 2-arg function.

## Scenarios

### Curry and Partial Application

#### curry2

#### curries a two-argument function

1. expect add5


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val curried = curry2(add)
val add5 = curried(5)
expect add5(3) == 8
```

</details>

#### curries multiply

1. expect double


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val curried = curry2(mul)
val double = curried(2)
expect double(7) == 14
```

</details>

#### applies both arguments

1. expect curried


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val curried = curry2(add)
expect curried(10)(20) == 30
```

</details>

#### curry3

#### curries a three-argument function

1. expect curried


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val curried = curry3(triple_add)
expect curried(1)(2)(3) == 6
```

</details>

#### partial application of curry3

1. expect add1 2


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val curried = curry3(triple_add)
val add1 = curried(1)
val add1_2 = add1(2)
expect add1_2(10) == 13
```

</details>

#### partial1

#### fixes first argument

1. expect add10


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val add10 = partial1(add, 10)
expect add10(5) == 15
```

</details>

#### creates increment function

1. expect inc


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val inc = partial1(add, 1)
expect inc(99) == 100
```

</details>

#### works with map

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val add100 = partial1(add, 100)
val data = [1, 2, 3]
val result = data.map(add100)
expect result == [101, 102, 103]
```

</details>

#### partial2

#### fixes first two arguments

1. expect add1 2


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val add1_2 = partial2(triple_add, 1, 2)
expect add1_2(3) == 6
```

</details>

#### fixes different values

1. expect add10 20


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val add10_20 = partial2(triple_add, 10, 20)
expect add10_20(30) == 60
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
