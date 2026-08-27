# Tensor Bridge Batch Conversion

> Tests batch conversion between math vector types (Vec3, Vec3d) and flat tensor arrays. Validates flattening Vec3 lists to float arrays, unflattening arrays back to Vec3 lists, round-trip consistency, and equivalent operations for double-precision Vec3d types.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Tensor Bridge Batch Conversion

Tests batch conversion between math vector types (Vec3, Vec3d) and flat tensor arrays. Validates flattening Vec3 lists to float arrays, unflattening arrays back to Vec3 lists, round-trip consistency, and equivalent operations for double-precision Vec3d types.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #ML-001 |
| Category | Runtime |
| Status | Active |
| Source | `test/03_system/feature/usage/tensor_bridge_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests batch conversion between math vector types (Vec3, Vec3d) and flat tensor
arrays. Validates flattening Vec3 lists to float arrays, unflattening arrays
back to Vec3 lists, round-trip consistency, and equivalent operations for
double-precision Vec3d types.

## Syntax

```simple
use std.spec.step

val vecs = [math.Vec3(1.0, 2.0, 3.0), math.Vec3(4.0, 5.0, 6.0)]
val arr = math.vecs_to_tensor(vecs)
val restored = math.tensor_to_vecs(arr)
```

## Scenarios

### Tensor Bridge Batch Conversion

#### arrtens Vec3 list to array

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- arrtens Vec3 list to array


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("arrtens Vec3 list to array")
val vecs = [
    math.Vec3(1.0, 2.0, 3.0),
    math.Vec3(4.0, 5.0, 6.0)
]
val arr = math.vecs_to_tensor(vecs)
expect arr.len() == 6
expect arr[0] == 1.0
expect arr[1] == 2.0
expect arr[2] == 3.0
expect arr[3] == 4.0
expect arr[4] == 5.0
expect arr[5] == 6.0
```

</details>

#### unarrtens array to Vec3 list

- unarrtens array to Vec3 list


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("unarrtens array to Vec3 list")
val arr = [1.0, 2.0, 3.0, 4.0, 5.0, 6.0]
val vecs = math.tensor_to_vecs(arr)
expect vecs.len() == 2
expect vecs[0].x == 1.0
expect vecs[0].y == 2.0
expect vecs[0].z == 3.0
expect vecs[1].x == 4.0
```

</details>

#### round-trips Vec3 list

- round-trips Vec3 list


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("round-trips Vec3 list")
val original = [
    math.Vec3(10.0, 20.0, 30.0),
    math.Vec3(40.0, 50.0, 60.0)
]
val arr = math.vecs_to_tensor(original)
val restored = math.tensor_to_vecs(arr)
expect restored.len() == 2
expect restored[0].x == 10.0
expect restored[1].z == 60.0
```

</details>

### Tensor Bridge Vec3d Batch Conversion

#### arrtens Vec3d list to f64 array

- arrtens Vec3d list to f64 array


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("arrtens Vec3d list to f64 array")
val vecs = [
    math.Vec3d(1.0, 2.0, 3.0),
    math.Vec3d(4.0, 5.0, 6.0)
]
val arr = math.vecs3d_to_tensor(vecs)
expect arr.len() == 6
expect arr[0] == 1.0
```

</details>

#### unarrtens f64 array to Vec3d list

- unarrtens f64 array to Vec3d list


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("unarrtens f64 array to Vec3d list")
val arr = [1.0, 2.0, 3.0, 4.0, 5.0, 6.0]
val vecs = math.tensor_to_vecs3d(arr)
expect vecs.len() == 2
expect vecs[0].x == 1.0
```

</details>

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

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `7956137efc9e8a660413fb890bfc443e550a0018374ea1e4d25b439a62a9457b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `7956137efc9e8a660413fb890bfc443e550a0018374ea1e4d25b439a62a9457b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `7956137efc9e8a660413fb890bfc443e550a0018374ea1e4d25b439a62a9457b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/feature/usage/tensor_bridge_spec.spl
mirror: doc/06_spec/03_system/feature/usage/tensor_bridge_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/usage/tensor_bridge_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/usage/tensor_bridge_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/usage/tensor_bridge_spec.spl:38:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'arrtens Vec3 list to array' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/usage/tensor_bridge_spec.spl:54:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'unarrtens array to Vec3 list' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/usage/tensor_bridge_spec.spl:65:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'round-trips Vec3 list' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
