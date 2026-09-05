# Ndarray Dtype Variant Equality Specification

> Tests covering DType variant equality (name-collision reproducer).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Ndarray Dtype Variant Equality Specification

## Scenarios

### DType variant equality (name-collision reproducer)

#### the Bool variant -- the filed failing case -- compares equal

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- the Bool variant -- the filed failing case -- compares equal
   - Expected: arr.dtype == DType.Bool is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("the Bool variant -- the filed failing case -- compares equal")
val arr = array_bool([Bool.new(true)])
expect(arr.dtype == DType.Bool).to_equal(true)
```

</details>

#### the three variants that always worked still work

- the three variants that always worked still work
   - Expected: array_f32([Float32.new(1.0)]).dtype == DType.F32 is true
   - Expected: array([Float64.new(1.0)]).dtype == DType.F64 is true
   - Expected: array_i64([Int64.new(1)]).dtype == DType.I64 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("the three variants that always worked still work")
expect(array_f32([Float32.new(1.0)]).dtype == DType.F32).to_equal(true)
expect(array([Float64.new(1.0)]).dtype == DType.F64).to_equal(true)
expect(array_i64([Int64.new(1)]).dtype == DType.I64).to_equal(true)
```

</details>

#### the colliding variant literal is an ENUM VALUE, not a constructor

- the colliding variant literal is an ENUM VALUE, not a constructor
   - Expected: DType.Bool == arr.dtype is true
   - Expected: DType.Bool == DType.F32 is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("the colliding variant literal is an ENUM VALUE, not a constructor")
# This is the assertion that names the true root cause. Before the fix
# `DType.Bool` was the std `Bool` struct's constructor, so it compared
# equal to nothing that came out of a field.
val arr = array_bool([Bool.new(true)])
expect(DType.Bool == arr.dtype).to_equal(true)
expect(DType.Bool == DType.F32).to_equal(false)
```

</details>

#### equality agrees with pattern matching for the colliding variant

- equality agrees with pattern matching for the colliding variant
   - Expected: matched is true
   - Expected: arr.dtype == DType.Bool equals `matched`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("equality agrees with pattern matching for the colliding variant")
# Patterns were correct throughout, so a disagreement between these two
# is the signature of this defect.
val arr = array_bool([Bool.new(true)])
var matched = false
match arr.dtype:
    case DType.Bool:
        matched = true
    case _:
        matched = false
expect(matched).to_equal(true)
expect(arr.dtype == DType.Bool).to_equal(matched)
```

</details>

#### inequality against a non-matching variant is still correct

- inequality against a non-matching variant is still correct
   - Expected: arr.dtype != DType.F32 is true
   - Expected: arr.dtype != DType.Bool is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("inequality against a non-matching variant is still correct")
val arr = array_bool([Bool.new(true)])
expect(arr.dtype != DType.F32).to_equal(true)
expect(arr.dtype != DType.Bool).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut/ndarray_dtype_variant_equality_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering DType variant equality (name-collision reproducer).
- DType variant equality (name-collision reproducer)

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `7578f7975178e4860be348758b6db51696be776752725b8aceadc70ff7f7a9c8`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `7578f7975178e4860be348758b6db51696be776752725b8aceadc70ff7f7a9c8`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `7578f7975178e4860be348758b6db51696be776752725b8aceadc70ff7f7a9c8`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/nogc_async_mut/ndarray_dtype_variant_equality_spec.spl
mirror: doc/06_spec/01_unit/lib/nogc_async_mut/ndarray_dtype_variant_equality_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/nogc_async_mut/ndarray_dtype_variant_equality_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/nogc_async_mut/ndarray_dtype_variant_equality_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/nogc_async_mut/ndarray_dtype_variant_equality_spec.spl:43:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'the Bool variant -- the filed failing case -- compares equal' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_async_mut/ndarray_dtype_variant_equality_spec.spl:49:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'the three variants that always worked still work' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_async_mut/ndarray_dtype_variant_equality_spec.spl:56:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'the colliding variant literal is an ENUM VALUE, not a constructor' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
