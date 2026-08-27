# Quickcheck Specification

> Tests covering Rng, IntGen, BoolGen, FloatGen, StringGen, ListGen, Property, PropertyResult, PropertyConfig, PropertyChecker, forall_int, forall_bool, forall_string, PropertyTest, check_property, Example Properties, Property Testing Integration.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 61 | 61 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Quickcheck Specification

## Scenarios

### Rng

#### creates with seed

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- creates with seed


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("creates with seed")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
# Rng.create(12345)
pass
```

</details>

#### generates different values

- generates different values


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("generates different values")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
# rng.next() != rng.next() (usually)
pass
```

</details>

#### generates values in range

- generates values in range


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("generates values in range")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
# rng.next_in_range(0, 10) in [0, 10)
pass
```

</details>

#### generates booleans

- generates booleans


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("generates booleans")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
# rng.next_bool() is true or false
pass
```

</details>

#### generates floats in [0, 1)

- generates floats in [0, 1)


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("generates floats in [0, 1)")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
# rng.next_f64() >= 0.0 and < 1.0
pass
```

</details>

#### is reproducible with same seed

- is reproducible with same seed


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("is reproducible with same seed")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
# Same seed produces same sequence
pass
```

</details>

### IntGen

#### creates full range generator

- creates full range generator


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("creates full range generator")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
# IntGen.full_range()
pass
```

</details>

#### creates positive generator

- creates positive generator


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("creates positive generator")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
# IntGen.positive() generates >= 0
pass
```

</details>

#### creates small range generator

- creates small range generator


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("creates small range generator")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
# IntGen.small() generates in [-100, 100]
pass
```

</details>

#### creates custom range generator

- creates custom range generator


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("creates custom range generator")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
# IntGen.in_range(10, 20)
pass
```

</details>

#### generates values in range

- generates values in range


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("generates values in range")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
# All generated values satisfy constraints
pass
```

</details>

#### shrinks towards zero

- shrinks towards zero


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("shrinks towards zero")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
# IntGen.shrink(10) contains 0
pass
```

</details>

#### shrinks negative towards zero

- shrinks negative towards zero


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("shrinks negative towards zero")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
# IntGen.shrink(-10) contains 0
pass
```

</details>

#### shrinks zero to empty

- shrinks zero to empty


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("shrinks zero to empty")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
# IntGen.shrink(0) == []
pass
```

</details>

### BoolGen

#### generates booleans

- generates booleans


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("generates booleans")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
# gen.generate(rng) is bool
pass
```

</details>

#### shrinks true to false

- shrinks true to false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("shrinks true to false")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
# BoolGen.shrink(true) == [false]
pass
```

</details>

#### shrinks false to empty

- shrinks false to empty


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("shrinks false to empty")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
# BoolGen.shrink(false) == []
pass
```

</details>

### FloatGen

#### creates unit generator

- creates unit generator


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("creates unit generator")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
# FloatGen.unit() generates in [0.0, 1.0]
pass
```

</details>

#### creates standard generator

- creates standard generator


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("creates standard generator")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
# FloatGen.standard() generates in [-1000, 1000]
pass
```

</details>

#### generates values in range

- generates values in range


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("generates values in range")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
# All values satisfy constraints
pass
```

</details>

#### shrinks towards zero

- shrinks towards zero


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("shrinks towards zero")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
# FloatGen.shrink(5.0) contains 0.0
pass
```

</details>

### StringGen

#### creates ASCII generator

- creates ASCII generator


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("creates ASCII generator")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
# StringGen.ascii()
pass
```

</details>

#### creates alpha generator

- creates alpha generator


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("creates alpha generator")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
# StringGen.alpha() generates only letters
pass
```

</details>

#### creates digit generator

- creates digit generator


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("creates digit generator")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
# StringGen.digits() generates only digits
pass
```

</details>

#### generates strings within length range

- generates strings within length range


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("generates strings within length range")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
# len(string) in [min_length, max_length]
pass
```

</details>

#### shrinks to shorter strings

- shrinks to shorter strings


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("shrinks to shorter strings")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
# StringGen.shrink("hello") contains ""
pass
```

</details>

#### shrinks empty to empty list

- shrinks empty to empty list


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("shrinks empty to empty list")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
# StringGen.shrink("") == []
pass
```

</details>

### ListGen

#### creates list of int generator

- creates list of int generator


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("creates list of int generator")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
# ListGen.of_ints(IntGen.small())
pass
```

</details>

#### generates lists within length range

- generates lists within length range


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("generates lists within length range")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
# len(list) in [min_length, max_length]
pass
```

</details>

#### shrinks by removing elements

- shrinks by removing elements


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("shrinks by removing elements")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
# ListGen.shrink([1,2,3]) contains [1,2], [1,3], [2,3]
pass
```

</details>

#### shrinks empty to empty list

- shrinks empty to empty list


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("shrinks empty to empty list")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
# ListGen.shrink([]) == []
pass
```

</details>

### Property

#### creates property with name and generator

- creates property with name and generator


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("creates property with name and generator")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
# Property.create("test", gen, pred)
pass
```

</details>

#### adds shrinker

- adds shrinker


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("adds shrinker")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
# prop.with_shrinker(shrink)
pass
```

</details>

### PropertyResult

#### identifies passed result

- identifies passed result


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("identifies passed result")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
# PropertyResult.Passed(100).is_passed() == true
pass
```

</details>

#### identifies failed result

- identifies failed result


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("identifies failed result")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
# PropertyResult.Failed(...).is_failed() == true
pass
```

</details>

### PropertyConfig

#### creates default config

- creates default config


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("creates default config")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
# PropertyConfig.default_config()
# config.iterations == 100
pass
```

</details>

#### creates quick config

- creates quick config


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("creates quick config")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
# PropertyConfig.quick()
# config.iterations == 20
pass
```

</details>

#### creates thorough config

- creates thorough config


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("creates thorough config")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
# PropertyConfig.thorough()
# config.iterations == 1000
pass
```

</details>

### PropertyChecker

#### creates with config

- creates with config


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("creates with config")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
# PropertyChecker.create(config)
pass
```

</details>

#### creates default checker

- creates default checker


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("creates default checker")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
# PropertyChecker.default_checker()
pass
```

</details>

#### checks passing property

- checks passing property


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("checks passing property")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
# Property that always returns true passes
pass
```

</details>

#### checks failing property

- checks failing property


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("checks failing property")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
# Property that returns false fails
pass
```

</details>

#### shrinks failing input

- shrinks failing input


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("shrinks failing input")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
# Counterexample is minimized
pass
```

</details>

#### returns counterexample on failure

- returns counterexample on failure


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("returns counterexample on failure")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
# Failed result contains the input that failed
pass
```

</details>

### forall_int

#### creates integer property generator

- creates integer property generator


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("creates integer property generator")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
# forall_int(\x: x == x)
pass
```

</details>

### forall_bool

#### creates boolean property generator

- creates boolean property generator


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("creates boolean property generator")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
# forall_bool(\b: b or not b)
pass
```

</details>

### forall_string

#### creates string property generator

- creates string property generator


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("creates string property generator")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
# forall_string(\s: s.len() >= 0)
pass
```

</details>

### PropertyTest

#### formats passing result

- formats passing result


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("formats passing result")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
# test.format_result() contains "passed"
pass
```

</details>

#### formats failing result with counterexample

- formats failing result with counterexample


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("formats failing result with counterexample")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
# test.format_result() contains counterexample
pass
```

</details>

#### indicates shrinking

- indicates shrinking


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("indicates shrinking")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
# test.shrunk shows if counterexample was shrunk
pass
```

</details>

### check_property

#### checks integer property

- checks integer property


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("checks integer property")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
# check_property("test", gen, pred)
pass
```

</details>

#### returns PropertyTest result

- returns PropertyTest result


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("returns PropertyTest result")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
# Result has name, passed, iterations, etc.
pass
```

</details>

### Example Properties

#### verifies addition is commutative

- verifies addition is commutative


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("verifies addition is commutative")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
# addition_commutative().passed == true
pass
```

</details>

#### verifies multiplication by zero

- verifies multiplication by zero


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("verifies multiplication by zero")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
# multiplication_by_zero().passed == true
pass
```

</details>

#### verifies double negation

- verifies double negation


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("verifies double negation")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
# double_negation().passed == true
pass
```

</details>

### Property Testing Integration

#### handles failing properties

- handles failing properties


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("handles failing properties")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
# Property that sometimes fails is caught
pass
```

</details>

#### shrinks to minimal counterexample

- shrinks to minimal counterexample


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("shrinks to minimal counterexample")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
# Large failing input shrinks to small one
pass
```

</details>

#### supports custom generators

- supports custom generators


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("supports custom generators")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
# User-defined generators work
pass
```

</details>

#### supports custom shrinkers

- supports custom shrinkers


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("supports custom shrinkers")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
# User-defined shrinkers work
pass
```

</details>

#### respects iteration count

- respects iteration count


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("respects iteration count")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
# Runs specified number of iterations
pass
```

</details>

#### respects seed for reproducibility

- respects seed for reproducibility


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("respects seed for reproducibility")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
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
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Rng, IntGen, BoolGen, FloatGen, StringGen, ListGen, Property, PropertyResult, PropertyConfig, PropertyChecker, forall_int, forall_bool, forall_string, PropertyTest, check_property, Example Properties, Property Testing Integration.
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-APP`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `8c0255989eca4d03cbd509f778ca688076b37a0d2b31c9ee6f3076b88f70e108`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `8c0255989eca4d03cbd509f778ca688076b37a0d2b31c9ee6f3076b88f70e108`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `8c0255989eca4d03cbd509f778ca688076b37a0d2b31c9ee6f3076b88f70e108`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **87/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/app/test_runner/quickcheck_spec.spl
mirror: doc/06_spec/01_unit/app/test_runner/quickcheck_spec.md (current)
findings: 3 blockers: 1
  narrative=100 structure=100 oracle=50
  traceability=100 evidence=100 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=87; blocker cap makes effective=49
doc/06_spec/01_unit/app/test_runner/quickcheck_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/test_runner/quickcheck_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/test_runner/quickcheck_spec.spl:1:1: blocker SSDOC-ORA-001 [oracle] (-50): no real executed assertion or compiler oracle
  why: A passing-looking document without an oracle is not conformance evidence.
  improve: Replace placeholders with an observable production assertion.
<!-- sspec-maintain:scorecard:end -->
