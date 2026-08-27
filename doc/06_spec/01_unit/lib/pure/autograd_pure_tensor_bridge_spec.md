# Autograd Pure Tensor Bridge Specification

> Tests covering std.pure f64 tensor representations stay convertible and accessor-compatible, accessor parity (invariant 1), a declared crossing exists in both directions (invariant 2), the crossing is lossless at every rank tested (invariant 3).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 13 | 13 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Autograd Pure Tensor Bridge Specification

## Scenarios

### std.pure f64 tensor representations stay convertible and accessor-compatible

### accessor parity (invariant 1)

#### PureTensor answers its dimensions through a method

- PureTensor answers its dimensions through a method


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("PureTensor answers its dimensions through a method")
assert_equal(tensor_from_data([1.0, 2.0, 3.0, 4.0], [2, 2]).dims(), [2, 2])
```

</details>

#### autograd Tensor answers its dimensions through a method

- autograd Tensor answers its dimensions through a method


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("autograd Tensor answers its dimensions through a method")
assert_equal(Tensor.from_data([1.0, 2.0, 3.0, 4.0], [2, 2], requires_grad: false).shape(), [2, 2])
```

</details>

#### the method agrees with the underlying field on PureTensor

- the method agrees with the underlying field on PureTensor


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("the method agrees with the underlying field on PureTensor")
val p = tensor_zeros([3, 4])
assert_equal(p.dims(), p.shape)
```

</details>

#### both representations agree on element count for the same shape

- both representations agree on element count for the same shape


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("both representations agree on element count for the same shape")
val p = tensor_ones([2, 3, 4])
val t = Tensor.ones([2, 3, 4], requires_grad: false)
assert_equal(p.numel(), t.numel())
```

</details>

### a declared crossing exists in both directions (invariant 2)

#### converts autograd Tensor -> PureTensor

- converts autograd Tensor -> PureTensor


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts autograd Tensor -> PureTensor")
val t = Tensor.from_data([5.0, 6.0], [2], requires_grad: false)
assert_equal(to_pure(t).dims(), [2])
```

</details>

#### converts PureTensor -> autograd Tensor

- converts PureTensor -> autograd Tensor


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts PureTensor -> autograd Tensor")
val p = tensor_from_data([5.0, 6.0], [2])
assert_equal(to_autograd(p, requires_grad: false).shape(), [2])
```

</details>

#### converts TensorF64 -> PureTensor without reaching into fields

- converts TensorF64 -> PureTensor without reaching into fields


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts TensorF64 -> PureTensor without reaching into fields")
val t = Tensor.from_data([7.0, 8.0, 9.0], [3], requires_grad: false)
assert_equal(pure_from_f64(t.value).dims(), [3])
```

</details>

#### converts PureTensor -> TensorF64 without reaching into fields

- converts PureTensor -> TensorF64 without reaching into fields


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts PureTensor -> TensorF64 without reaching into fields")
val p = tensor_from_data([7.0, 8.0, 9.0], [3])
assert_equal(f64_from_pure(p).numel(), 3)
```

</details>

### the crossing is lossless at every rank tested (invariant 3)

#### round-trips a rank-1 tensor's shape and values

- round-trips a rank-1 tensor's shape and values


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("round-trips a rank-1 tensor's shape and values")
val p = tensor_from_data([1.5, 2.5, 3.5], [3])
val r = to_pure(to_autograd(p, requires_grad: false))
assert_equal(r.dims(), [3])
assert_equal(r.data, [1.5, 2.5, 3.5])
```

</details>

#### round-trips a rank-2 tensor

- round-trips a rank-2 tensor


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("round-trips a rank-2 tensor")
val p = tensor_from_data([1.0, 2.0, 3.0, 4.0, 5.0, 6.0], [2, 3])
val r = to_pure(to_autograd(p, requires_grad: false))
assert_equal(r.dims(), [2, 3])
assert_equal(r.data, [1.0, 2.0, 3.0, 4.0, 5.0, 6.0])
```

</details>

#### round-trips a rank-3 tensor

- round-trips a rank-3 tensor


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("round-trips a rank-3 tensor")
val p = tensor_from_data([1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0], [2, 2, 2])
val r = to_pure(to_autograd(p, requires_grad: false))
assert_equal(r.dims(), [2, 2, 2])
assert_equal(r.numel(), 8)
```

</details>

#### preserves strides across the crossing

- preserves strides across the crossing


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("preserves strides across the crossing")
val p = tensor_from_data([1.0, 2.0, 3.0, 4.0, 5.0, 6.0], [2, 3])
assert_equal(to_pure(to_autograd(p, requires_grad: false)).strides, p.strides)
```

</details>

#### round-trips starting from the autograd side

- round-trips starting from the autograd side


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("round-trips starting from the autograd side")
val t = Tensor.from_data([9.0, 8.0, 7.0, 6.0], [2, 2], requires_grad: false)
val r = to_autograd(to_pure(t), requires_grad: false)
assert_equal(r.shape(), [2, 2])
assert_equal(r.value.data, [9.0, 8.0, 7.0, 6.0])
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/pure/autograd_pure_tensor_bridge_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering std.pure f64 tensor representations stay convertible and accessor-compatible, accessor parity (invariant 1), a declared crossing exists in both directions (invariant 2), the crossing is lossless at every rank tested (invariant 3).
- std.pure f64 tensor representations stay convertible and accessor-compatible
- accessor parity (invariant 1)
- a declared crossing exists in both directions (invariant 2)
- the crossing is lossless at every rank tested (invariant 3)

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 13 |
| Active scenarios | 13 |
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

- Canonical SPipe generation for source `93080b5aba690a60372fd7540611870dfa4b3e54b53eedf971e608917f999d05`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `93080b5aba690a60372fd7540611870dfa4b3e54b53eedf971e608917f999d05`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `93080b5aba690a60372fd7540611870dfa4b3e54b53eedf971e608917f999d05`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/pure/autograd_pure_tensor_bridge_spec.spl
mirror: doc/06_spec/01_unit/lib/pure/autograd_pure_tensor_bridge_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/pure/autograd_pure_tensor_bridge_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/pure/autograd_pure_tensor_bridge_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/pure/autograd_pure_tensor_bridge_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'PureTensor answers its dimensions through a method' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/pure/autograd_pure_tensor_bridge_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'autograd Tensor answers its dimensions through a method' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/pure/autograd_pure_tensor_bridge_spec.spl:42:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'the method agrees with the underlying field on PureTensor' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
