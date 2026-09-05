# Weight Utils Specification

> Tests covering dtype_element_size, tensor_byte_len.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Weight Utils Specification

## Scenarios

### dtype_element_size

#### F32 is 4 bytes

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- F32 is 4 bytes
   - Expected: dtype_element_size(Dtype.F32) equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("F32 is 4 bytes")
expect(dtype_element_size(Dtype.F32)).to_equal(4)
```

</details>

#### F16 and Bf16 are 2 bytes

- F16 and Bf16 are 2 bytes
   - Expected: dtype_element_size(Dtype.F16) equals `2`
   - Expected: dtype_element_size(Dtype.Bf16) equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("F16 and Bf16 are 2 bytes")
expect(dtype_element_size(Dtype.F16)).to_equal(2)
expect(dtype_element_size(Dtype.Bf16)).to_equal(2)
```

</details>

#### F64 and I64 are 8 bytes

- F64 and I64 are 8 bytes
   - Expected: dtype_element_size(Dtype.F64) equals `8`
   - Expected: dtype_element_size(Dtype.I64) equals `8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("F64 and I64 are 8 bytes")
expect(dtype_element_size(Dtype.F64)).to_equal(8)
expect(dtype_element_size(Dtype.I64)).to_equal(8)
```

</details>

#### U8 and Bool are 1 byte

- U8 and Bool are 1 byte
   - Expected: dtype_element_size(Dtype.U8) equals `1`
   - Expected: dtype_element_size(Dtype.Bool) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("U8 and Bool are 1 byte")
expect(dtype_element_size(Dtype.U8)).to_equal(1)
expect(dtype_element_size(Dtype.Bool)).to_equal(1)
```

</details>

### tensor_byte_len

#### scalar is one element

- scalar is one element
   - Expected: tensor_byte_len(shape, Dtype.F32) equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("scalar is one element")
val shape: [i64] = []
expect(tensor_byte_len(shape, Dtype.F32)).to_equal(4)
```

</details>

#### vector of 8 f32 is 32 bytes

- vector of 8 f32 is 32 bytes
   - Expected: tensor_byte_len(shape, Dtype.F32) equals `32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("vector of 8 f32 is 32 bytes")
val shape: [i64] = [8]
expect(tensor_byte_len(shape, Dtype.F32)).to_equal(32)
```

</details>

<details>
<summary>Advanced: matrix 4x8 bf16 is 64 bytes</summary>

#### matrix 4x8 bf16 is 64 bytes

- matrix 4x8 bf16 is 64 bytes
   - Expected: tensor_byte_len(shape, Dtype.Bf16) equals `64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("matrix 4x8 bf16 is 64 bytes")
val shape: [i64] = [4, 8]
expect(tensor_byte_len(shape, Dtype.Bf16)).to_equal(64)
```

</details>


</details>

#### returns 0 on negative dim

- returns 0 on negative dim
   - Expected: tensor_byte_len(shape, Dtype.F32) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 0 on negative dim")
val shape: [i64] = [-1, 8]
expect(tensor_byte_len(shape, Dtype.F32)).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/slang/model_executor/model_loader/weight_utils_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering dtype_element_size, tensor_byte_len.
- dtype_element_size
- tensor_byte_len

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `1789b56f70dfda466e39bbe90ced3dcd77ccb58f1ebb2387f24d8d1ab8b29eaa`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `1789b56f70dfda466e39bbe90ced3dcd77ccb58f1ebb2387f24d8d1ab8b29eaa`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `1789b56f70dfda466e39bbe90ced3dcd77ccb58f1ebb2387f24d8d1ab8b29eaa`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/lib/gc_async_mut/slang/model_executor/model_loader/weight_utils_spec.spl
mirror: doc/06_spec/01_unit/lib/gc_async_mut/slang/model_executor/model_loader/weight_utils_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/gc_async_mut/slang/model_executor/model_loader/weight_utils_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/gc_async_mut/slang/model_executor/model_loader/weight_utils_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/gc_async_mut/slang/model_executor/model_loader/weight_utils_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 11 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/gc_async_mut/slang/model_executor/model_loader/weight_utils_spec.spl:17:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'F32 is 4 bytes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/slang/model_executor/model_loader/weight_utils_spec.spl:22:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'F16 and Bf16 are 2 bytes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/slang/model_executor/model_loader/weight_utils_spec.spl:28:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'F64 and I64 are 8 bytes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
