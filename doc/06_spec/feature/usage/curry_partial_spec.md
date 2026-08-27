# curry_partial_spec

> Curry and Partial Application

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
| Source | `test/feature/usage/curry_partial_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Curry and Partial Application

Standard library functions for currying and partial application.
`curry2(f)` converts a 2-arg function into nested single-arg lambdas.
`partial1(f, a)` fixes the first argument of a 2-arg function.

## Scenarios

### Curry and Partial Application

#### curry2

#### curries a two-argument function

- curries a two-argument function


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("curries a two-argument function")
val curried = curry2(add)
val add5 = curried(5)
expect add5(3) == 8
```

</details>

#### curries multiply

- curries multiply


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("curries multiply")
val curried = curry2(mul)
val double = curried(2)
expect double(7) == 14
```

</details>

#### applies both arguments

- applies both arguments


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("applies both arguments")
val curried = curry2(add)
expect curried(10)(20) == 30
```

</details>

#### curry3

#### curries a three-argument function

- curries a three-argument function


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("curries a three-argument function")
val curried = curry3(triple_add)
expect curried(1)(2)(3) == 6
```

</details>

#### partial application of curry3

- partial application of curry3


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("partial application of curry3")
val curried = curry3(triple_add)
val add1 = curried(1)
val add1_2 = add1(2)
expect add1_2(10) == 13
```

</details>

#### partial1

#### fixes first argument

- fixes first argument


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("fixes first argument")
val add10 = partial1(add, 10)
expect add10(5) == 15
```

</details>

#### creates increment function

- creates increment function


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("creates increment function")
val inc = partial1(add, 1)
expect inc(99) == 100
```

</details>

#### works with map

- works with map


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("works with map")
val add100 = partial1(add, 100)
val data = [1, 2, 3]
val result = data.map(add100)
expect result == [101, 102, 103]
```

</details>

#### partial2

#### fixes first two arguments

- fixes first two arguments


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("fixes first two arguments")
val add1_2 = partial2(triple_add, 1, 2)
expect add1_2(3) == 6
```

</details>

#### fixes different values

- fixes different values


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("fixes different values")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-FEATURE`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `1dc71236f9114533c7fefcdbb3e6f3408761f0178bbdf94d7dfc7d99df23f3b2`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `1dc71236f9114533c7fefcdbb3e6f3408761f0178bbdf94d7dfc7d99df23f3b2`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `1dc71236f9114533c7fefcdbb3e6f3408761f0178bbdf94d7dfc7d99df23f3b2`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/feature/usage/curry_partial_spec.spl
mirror: doc/06_spec/feature/usage/curry_partial_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/feature/usage/curry_partial_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/feature/usage/curry_partial_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/feature/usage/curry_partial_spec.spl:34:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'curries a two-argument function' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/usage/curry_partial_spec.spl:41:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'curries multiply' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/usage/curry_partial_spec.spl:48:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'applies both arguments' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
