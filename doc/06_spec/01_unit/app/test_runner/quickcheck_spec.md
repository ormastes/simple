# Quickcheck Specification

> <details>

<!-- sdn-diagram:id=quickcheck_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=quickcheck_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

quickcheck_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=quickcheck_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 61 | 61 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Quickcheck Specification

## Scenarios

### Rng

#### creates with seed

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Rng.create(12345)
pass
```

</details>

#### generates different values

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# rng.next() != rng.next() (usually)
pass
```

</details>

#### generates values in range

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# rng.next_in_range(0, 10) in [0, 10)
pass
```

</details>

#### generates booleans

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# rng.next_bool() is true or false
pass
```

</details>

#### generates floats in [0, 1)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# rng.next_f64() >= 0.0 and < 1.0
pass
```

</details>

#### is reproducible with same seed

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Same seed produces same sequence
pass
```

</details>

### IntGen

#### creates full range generator

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# IntGen.full_range()
pass
```

</details>

#### creates positive generator

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# IntGen.positive() generates >= 0
pass
```

</details>

#### creates small range generator

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# IntGen.small() generates in [-100, 100]
pass
```

</details>

#### creates custom range generator

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# IntGen.in_range(10, 20)
pass
```

</details>

#### generates values in range

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# All generated values satisfy constraints
pass
```

</details>

#### shrinks towards zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# IntGen.shrink(10) contains 0
pass
```

</details>

#### shrinks negative towards zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# IntGen.shrink(-10) contains 0
pass
```

</details>

#### shrinks zero to empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# IntGen.shrink(0) == []
pass
```

</details>

### BoolGen

#### generates booleans

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# gen.generate(rng) is bool
pass
```

</details>

#### shrinks true to false

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# BoolGen.shrink(true) == [false]
pass
```

</details>

#### shrinks false to empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# BoolGen.shrink(false) == []
pass
```

</details>

### FloatGen

#### creates unit generator

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# FloatGen.unit() generates in [0.0, 1.0]
pass
```

</details>

#### creates standard generator

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# FloatGen.standard() generates in [-1000, 1000]
pass
```

</details>

#### generates values in range

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# All values satisfy constraints
pass
```

</details>

#### shrinks towards zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# FloatGen.shrink(5.0) contains 0.0
pass
```

</details>

### StringGen

#### creates ASCII generator

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# StringGen.ascii()
pass
```

</details>

#### creates alpha generator

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# StringGen.alpha() generates only letters
pass
```

</details>

#### creates digit generator

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# StringGen.digits() generates only digits
pass
```

</details>

#### generates strings within length range

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# len(string) in [min_length, max_length]
pass
```

</details>

#### shrinks to shorter strings

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# StringGen.shrink("hello") contains ""
pass
```

</details>

#### shrinks empty to empty list

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# StringGen.shrink("") == []
pass
```

</details>

### ListGen

#### creates list of int generator

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# ListGen.of_ints(IntGen.small())
pass
```

</details>

#### generates lists within length range

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# len(list) in [min_length, max_length]
pass
```

</details>

#### shrinks by removing elements

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# ListGen.shrink([1,2,3]) contains [1,2], [1,3], [2,3]
pass
```

</details>

#### shrinks empty to empty list

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# ListGen.shrink([]) == []
pass
```

</details>

### Property

#### creates property with name and generator

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Property.create("test", gen, pred)
pass
```

</details>

#### adds shrinker

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# prop.with_shrinker(shrink)
pass
```

</details>

### PropertyResult

#### identifies passed result

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# PropertyResult.Passed(100).is_passed() == true
pass
```

</details>

#### identifies failed result

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# PropertyResult.Failed(...).is_failed() == true
pass
```

</details>

### PropertyConfig

#### creates default config

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# PropertyConfig.default_config()
# config.iterations == 100
pass
```

</details>

#### creates quick config

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# PropertyConfig.quick()
# config.iterations == 20
pass
```

</details>

#### creates thorough config

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# PropertyConfig.thorough()
# config.iterations == 1000
pass
```

</details>

### PropertyChecker

#### creates with config

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# PropertyChecker.create(config)
pass
```

</details>

#### creates default checker

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# PropertyChecker.default_checker()
pass
```

</details>

#### checks passing property

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Property that always returns true passes
pass
```

</details>

#### checks failing property

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Property that returns false fails
pass
```

</details>

#### shrinks failing input

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Counterexample is minimized
pass
```

</details>

#### returns counterexample on failure

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Failed result contains the input that failed
pass
```

</details>

### forall_int

#### creates integer property generator

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# forall_int(\x: x == x)
pass
```

</details>

### forall_bool

#### creates boolean property generator

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# forall_bool(\b: b or not b)
pass
```

</details>

### forall_string

#### creates string property generator

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# forall_string(\s: s.len() >= 0)
pass
```

</details>

### PropertyTest

#### formats passing result

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# test.format_result() contains "passed"
pass
```

</details>

#### formats failing result with counterexample

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# test.format_result() contains counterexample
pass
```

</details>

#### indicates shrinking

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# test.shrunk shows if counterexample was shrunk
pass
```

</details>

### check_property

#### checks integer property

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# check_property("test", gen, pred)
pass
```

</details>

#### returns PropertyTest result

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Result has name, passed, iterations, etc.
pass
```

</details>

### Example Properties

#### verifies addition is commutative

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# addition_commutative().passed == true
pass
```

</details>

#### verifies multiplication by zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# multiplication_by_zero().passed == true
pass
```

</details>

#### verifies double negation

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# double_negation().passed == true
pass
```

</details>

### Property Testing Integration

#### handles failing properties

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Property that sometimes fails is caught
pass
```

</details>

#### shrinks to minimal counterexample

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Large failing input shrinks to small one
pass
```

</details>

#### supports custom generators

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# User-defined generators work
pass
```

</details>

#### supports custom shrinkers

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# User-defined shrinkers work
pass
```

</details>

#### respects iteration count

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Runs specified number of iterations
pass
```

</details>

#### respects seed for reproducibility

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Same seed gives same results
pass
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/test_runner/quickcheck_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Rng
- IntGen
- BoolGen
- FloatGen
- StringGen
- ListGen
- Property
- PropertyResult
- PropertyConfig
- PropertyChecker
- forall_int
- forall_bool
- forall_string
- PropertyTest
- check_property
- Example Properties
- Property Testing Integration

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 61 |
| Active scenarios | 61 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
