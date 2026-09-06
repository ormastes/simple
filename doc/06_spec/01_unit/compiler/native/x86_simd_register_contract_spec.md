# X86 Simd Register Contract Specification

> Tests covering x86 SIMD machine register contract.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# X86 Simd Register Contract Specification

## Scenarios

### x86 SIMD machine register contract

#### normalizes canonical physical XMM and YMM ranges

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- normalizes canonical physical XMM and YMM ranges


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("normalizes canonical physical XMM and YMM ranges")
assert_equal(xmm_to_index(X86_XMM0), 0)
assert_equal(xmm_to_index(X86_XMM15), 15)
assert_equal(ymm_to_index(X86_YMM0), 0)
assert_equal(ymm_to_index(X86_YMM15), 15)
assert_equal(xmm_to_index(X86_YMM0), -1)
assert_equal(ymm_to_index(X86_XMM0), -1)
```

</details>

#### keeps vector machine opcodes distinct from scalar and each other

- keeps vector machine opcodes distinct from scalar and each other


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps vector machine opcodes distinct from scalar and each other")
assert_true(X86_OP_VMOVAPS_LOAD_YMM > 80)
assert_false(X86_OP_VMOVAPS_LOAD_YMM == X86_OP_VMOVAPS_STORE_YMM)
assert_false(X86_OP_VMOVAPS_STORE_YMM == X86_OP_VADDPS_YMM)
```

</details>

#### assigns overlapping 128-bit intervals only to XMM registers

- assigns overlapping 128-bit intervals only to XMM registers


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("assigns overlapping 128-bit intervals only to XMM registers")
val result = linear_scan_x86_64_simd([
    overlapping_interval(1), overlapping_interval(2),
    overlapping_interval(3)
], 128)
assert_true(result.ok)
assert_true(result.assignments[1] >= X86_XMM0)
assert_true(result.assignments[1] <= X86_XMM7)
assert_false(result.assignments[1] == result.assignments[2])
```

</details>

#### assigns overlapping 256-bit intervals only to YMM registers

- assigns overlapping 256-bit intervals only to YMM registers


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("assigns overlapping 256-bit intervals only to YMM registers")
val result = linear_scan_x86_64_simd([
    overlapping_interval(1), overlapping_interval(2),
    overlapping_interval(3)
], 256)
assert_true(result.ok)
assert_true(result.assignments[1] >= X86_YMM0)
assert_true(result.assignments[1] <= X86_YMM7)
assert_false(result.assignments[1] == result.assignments[2])
```

</details>

#### fails closed when vector pressure would require a spill

- fails closed when vector pressure would require a spill


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fails closed when vector pressure would require a spill")
var intervals: [LiveInterval] = []
var id = 0
while id < 9:
    intervals.push(overlapping_interval(id))
    id = id + 1
val result = linear_scan_x86_64_simd(intervals, 256)
assert_false(result.ok)
assert_equal(result.assignments.len(), 0)
assert_equal(result.reason, "simd-spill-lowering-unavailable")
```

</details>

#### rejects non-YMM operands instead of encoding register zero

- rejects non-YMM operands instead of encoding register zero


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects non-YMM operands instead of encoding register zero")
assert_equal(encode_vaddps_ymm(X86_XMM0, X86_YMM0, X86_YMM0).len(), 0)
assert_equal(encode_vmovaps_load_ymm(X86_XMM0, 0, 0).len(), 0)
```

</details>

#### rejects an unsupported vector register width

- rejects an unsupported vector register width


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects an unsupported vector register width")
val result = linear_scan_x86_64_simd([overlapping_interval(1)], 512)
assert_false(result.ok)
assert_equal(result.reason, "unsupported-vector-register-width")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/native/x86_simd_register_contract_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering x86 SIMD machine register contract.
- x86 SIMD machine register contract

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
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

- Canonical SPipe generation for source `6dccfc48332b5a9ef8bd377e6787f7ccbc266285e439f92dea532a9cb645e799`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `6dccfc48332b5a9ef8bd377e6787f7ccbc266285e439f92dea532a9cb645e799`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `6dccfc48332b5a9ef8bd377e6787f7ccbc266285e439f92dea532a9cb645e799`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/native/x86_simd_register_contract_spec.spl
mirror: doc/06_spec/01_unit/compiler/native/x86_simd_register_contract_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/native/x86_simd_register_contract_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/native/x86_simd_register_contract_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/native/x86_simd_register_contract_spec.spl:30:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'normalizes canonical physical XMM and YMM ranges' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/native/x86_simd_register_contract_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps vector machine opcodes distinct from scalar and each other' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/native/x86_simd_register_contract_spec.spl:47:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'assigns overlapping 128-bit intervals only to XMM registers' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
