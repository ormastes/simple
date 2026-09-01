# Simd Check Specification

> Tests covering SimdElementType, SimdVectorType, SimdOperation, SimdCheckError, SimdTypeChecker, VectorizationStatus, LoopInfo, AutoVectorizer, SimdInstructionInfo, SimdCapability, check_simd_binary, can_vectorize_loop, get_vector_type_for_scalar.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 61 | 61 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simd Check Specification

## Scenarios

### SimdElementType

#### converts to text

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- converts to text


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("converts to text")
# SimdElementType.I32.to_text() == "i32"
pass
```

</details>

#### returns correct bit width

- returns correct bit width


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("returns correct bit width")
# SimdElementType.I8.bit_width() == 8
# SimdElementType.I64.bit_width() == 64
pass
```

</details>

#### identifies integer types

- identifies integer types


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("identifies integer types")
# SimdElementType.I32.is_integer() == true
# SimdElementType.F32.is_integer() == false
pass
```

</details>

#### identifies float types

- identifies float types


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("identifies float types")
# SimdElementType.F32.is_float() == true
# SimdElementType.I32.is_float() == false
pass
```

</details>

### SimdVectorType

#### creates vector type

- creates vector type


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("creates vector type")
# SimdVectorType.create(I32, 4)
# ty.lane_count == 4
pass
```

</details>

#### creates standard types

- creates standard types


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("creates standard types")
# SimdVectorType.i32x4()
# SimdVectorType.f64x2()
pass
```

</details>

#### formats as string

- formats as string


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("formats as string")
# SimdVectorType.i32x4().to_text() == "i32x4"
pass
```

</details>

#### calculates total bits

- calculates total bits


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("calculates total bits")
# SimdVectorType.i32x4().total_bits() == 128
pass
```

</details>

#### validates vector width

- validates vector width


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("validates vector width")
# 128-bit vector is valid
# 96-bit vector is invalid
pass
```

</details>

#### checks type compatibility

- checks type compatibility


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("checks type compatibility")
# i32x4 compatible with i32x4
# i32x4 not compatible with i64x2
pass
```

</details>

### SimdOperation

#### converts to text

- converts to text


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("converts to text")
# SimdOperation.Add.to_text() == "add"
pass
```

</details>

#### identifies binary operations

- identifies binary operations


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("identifies binary operations")
# SimdOperation.Add.is_binary() == true
pass
```

</details>

#### identifies unary operations

- identifies unary operations


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("identifies unary operations")
# SimdOperation.Not.is_unary() == true
pass
```

</details>

#### checks float support

- checks float support


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("checks float support")
# SimdOperation.Add.supports_float() == true
# SimdOperation.And.supports_float() == false
pass
```

</details>

#### checks integer support

- checks integer support


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("checks integer support")
# SimdOperation.And.supports_integer() == true
pass
```

</details>

### SimdCheckError

#### formats invalid lane count error

- formats invalid lane count error


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("formats invalid lane count error")
# SimdCheckError.InvalidLaneCount(4, 8).to_text()
pass
```

</details>

#### formats incompatible types error

- formats incompatible types error


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("formats incompatible types error")
# SimdCheckError.IncompatibleTypes(i32x4, i64x2).to_text()
pass
```

</details>

#### formats invalid width error

- formats invalid width error


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("formats invalid width error")
# SimdCheckError.InvalidVectorWidth(96).to_text()
pass
```

</details>

#### formats unsupported operation error

- formats unsupported operation error


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("formats unsupported operation error")
# SimdCheckError.UnsupportedOperation(And, F32).to_text()
pass
```

</details>

#### formats lane index out of bounds error

- formats lane index out of bounds error


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("formats lane index out of bounds error")
# SimdCheckError.LaneIndexOutOfBounds(5, 4).to_text()
pass
```

</details>

### SimdTypeChecker

#### creates checker with max width

- creates checker with max width


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("creates checker with max width")
# SimdTypeChecker.create(128)
pass
```

</details>

#### creates SSE checker

- creates SSE checker


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("creates SSE checker")
# SimdTypeChecker.for_sse() has 128-bit max
pass
```

</details>

#### creates AVX checker

- creates AVX checker


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("creates AVX checker")
# SimdTypeChecker.for_avx() has 256-bit max
pass
```

</details>

#### creates AVX-512 checker

- creates AVX-512 checker


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("creates AVX-512 checker")
# SimdTypeChecker.for_avx512() has 512-bit max
pass
```

</details>

#### validates vector types

- validates vector types


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("validates vector types")
# checker.check_vector_type(i32x4) == true
pass
```

</details>

#### rejects invalid vector width

- rejects invalid vector width


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("rejects invalid vector width")
# checker.check_vector_type with 96-bit vector fails
pass
```

</details>

#### rejects vectors too wide for target

- rejects vectors too wide for target


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("rejects vectors too wide for target")
# SSE checker rejects 256-bit vectors
pass
```

</details>

#### validates binary operations

- validates binary operations


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("validates binary operations")
# checker.check_binary_op(Add, i32x4, i32x4) == true
pass
```

</details>

#### rejects incompatible operand types

- rejects incompatible operand types


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("rejects incompatible operand types")
# checker.check_binary_op(Add, i32x4, i64x2) == false
pass
```

</details>

#### rejects unsupported operations for type

- rejects unsupported operations for type


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("rejects unsupported operations for type")
# checker.check_binary_op(And, f32x4, f32x4) == false
pass
```

</details>

#### validates lane access

- validates lane access


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("validates lane access")
# checker.check_lane_access(i32x4, 2) == true
# checker.check_lane_access(i32x4, 5) == false
pass
```

</details>

#### validates shuffle masks

- validates shuffle masks


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("validates shuffle masks")
# checker.check_shuffle(i32x4, [0, 1, 2, 3]) == true
pass
```

</details>

#### rejects invalid shuffle mask length

- rejects invalid shuffle mask length


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("rejects invalid shuffle mask length")
# checker.check_shuffle(i32x4, [0, 1]) == false
pass
```

</details>

### VectorizationStatus

#### identifies vectorizable status

- identifies vectorizable status


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("identifies vectorizable status")
# VectorizationStatus.Vectorizable(4).can_vectorize() == true
pass
```

</details>

#### identifies non-vectorizable status

- identifies non-vectorizable status


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("identifies non-vectorizable status")
# VectorizationStatus.NotVectorizable("reason").can_vectorize() == false
pass
```

</details>

#### identifies partially vectorizable

- identifies partially vectorizable


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("identifies partially vectorizable")
# VectorizationStatus.PartiallyVectorizable(4, 2).can_vectorize() == true
pass
```

</details>

#### formats status as text

- formats status as text


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("formats status as text")
# status.to_text() describes the status
pass
```

</details>

### LoopInfo

<details>
<summary>Advanced: creates simple loop info</summary>

#### creates simple loop info

- creates simple loop info


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("creates simple loop info")
# LoopInfo.simple_loop(100)
# info.iteration_count == Some(100)
pass
```

</details>


</details>

#### identifies vectorization candidates

- identifies vectorization candidates


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("identifies vectorization candidates")
# Simple loop is candidate
pass
```

</details>

<details>
<summary>Advanced: rejects loops with dependencies</summary>

#### rejects loops with dependencies

- rejects loops with dependencies


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("rejects loops with dependencies")
# has_dependencies = true not a candidate
pass
```

</details>


</details>

<details>
<summary>Advanced: rejects loops with function calls</summary>

#### rejects loops with function calls

- rejects loops with function calls


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("rejects loops with function calls")
# has_function_calls = true not a candidate
pass
```

</details>


</details>

### AutoVectorizer

#### creates with target vector width

- creates with target vector width


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("creates with target vector width")
# AutoVectorizer.create(128)
pass
```

</details>

<details>
<summary>Advanced: analyzes simple loop as vectorizable</summary>

#### analyzes simple loop as vectorizable

- analyzes simple loop as vectorizable


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("analyzes simple loop as vectorizable")
# Simple loop with 100 iterations is vectorizable
pass
```

</details>


</details>

#### calculates vectorization factor

- calculates vectorization factor


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("calculates vectorization factor")
# For 128-bit and i32: factor = 4
pass
```

</details>

#### detects partial vectorization

- detects partial vectorization


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("detects partial vectorization")
# Loop with 6 iterations and factor 4 has remainder 2
pass
```

</details>

<details>
<summary>Advanced: rejects loops with low trip count</summary>

#### rejects loops with low trip count

- rejects loops with low trip count


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("rejects loops with low trip count")
# Loop with 2 iterations not worth vectorizing
pass
```

</details>


</details>

<details>
<summary>Advanced: rejects loops with dependencies</summary>

#### rejects loops with dependencies

- rejects loops with dependencies


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("rejects loops with dependencies")
# Returns NotVectorizable with reason
pass
```

</details>


</details>

#### suggests vector type for element type

- suggests vector type for element type


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("suggests vector type for element type")
# For i32 with 128-bit target: i32x4
pass
```

</details>

### SimdInstructionInfo

#### creates binary instruction info

- creates binary instruction info


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("creates binary instruction info")
# SimdInstructionInfo.binary(Add, i32x4)
pass
```

</details>

#### creates unary instruction info

- creates unary instruction info


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("creates unary instruction info")
# SimdInstructionInfo.unary(Not, i32x4)
pass
```

</details>

### SimdCapability

#### creates SSE2 capability

- creates SSE2 capability


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("creates SSE2 capability")
# SimdCapability.sse2()
# capability.max_vector_width == 128
pass
```

</details>

#### creates AVX2 capability

- creates AVX2 capability


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("creates AVX2 capability")
# SimdCapability.avx2()
# capability.has_fma == true
pass
```

</details>

#### checks type support

- checks type support


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("checks type support")
# capability.supports_type(i32x4) == true
pass
```

</details>

#### checks operation support

- checks operation support


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("checks operation support")
# capability.supports_operation(Add) == true
pass
```

</details>

### check_simd_binary

#### validates compatible operation

- validates compatible operation


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("validates compatible operation")
# check_simd_binary(Add, i32x4, i32x4) == Ok(())
pass
```

</details>

#### rejects incompatible types

- rejects incompatible types


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("rejects incompatible types")
# check_simd_binary(Add, i32x4, i64x2) is Err
pass
```

</details>

### can_vectorize_loop

<details>
<summary>Advanced: returns true for vectorizable loop</summary>

#### returns true for vectorizable loop

- returns true for vectorizable loop


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("returns true for vectorizable loop")
# can_vectorize_loop(100, 32) == true
pass
```

</details>


</details>

#### returns false for low iteration count

- returns false for low iteration count


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("returns false for low iteration count")
# can_vectorize_loop(2, 32) == false
pass
```

</details>

### get_vector_type_for_scalar

#### returns i32x4 for i32

- returns i32x4 for i32


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("returns i32x4 for i32")
# get_vector_type_for_scalar("i32") == Some(i32x4)
pass
```

</details>

#### returns f64x2 for f64

- returns f64x2 for f64


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("returns f64x2 for f64")
# get_vector_type_for_scalar("f64") == Some(f64x2)
pass
```

</details>

#### returns None for unknown scalar

- returns None for unknown scalar


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("returns None for unknown scalar")
# get_vector_type_for_scalar("unknown") == None
pass
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/native/simd_check_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering SimdElementType, SimdVectorType, SimdOperation, SimdCheckError, SimdTypeChecker, VectorizationStatus, LoopInfo, AutoVectorizer, SimdInstructionInfo, SimdCapability, check_simd_binary, can_vectorize_loop, get_vector_type_for_scalar.
- SimdElementType
- SimdVectorType
- SimdOperation
- SimdCheckError
- SimdTypeChecker
- VectorizationStatus
- LoopInfo
- AutoVectorizer
- SimdInstructionInfo
- SimdCapability
- check_simd_binary
- can_vectorize_loop
- get_vector_type_for_scalar

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

- `REQ-SSPEC-UNIT`
- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `2def7f9ad3b4573d0e0d915cbdceab200a16dbbfb0c6cb634d2b5e1d7d1d6184`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `2def7f9ad3b4573d0e0d915cbdceab200a16dbbfb0c6cb634d2b5e1d7d1d6184`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `2def7f9ad3b4573d0e0d915cbdceab200a16dbbfb0c6cb634d2b5e1d7d1d6184`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **76/100**; effective score: **49/100**; blockers: **2**.

SSpec documentization score: 49/100
source: test/01_unit/compiler/native/simd_check_spec.spl
mirror: doc/06_spec/01_unit/compiler/native/simd_check_spec.md (current)
findings: 7 blockers: 2
  narrative=100 structure=100 oracle=50
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=76; blocker cap makes effective=49
doc/06_spec/01_unit/compiler/native/simd_check_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/native/simd_check_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/native/simd_check_spec.spl:1:1: blocker SSDOC-ORA-001 [oracle] (-50): no real executed assertion or compiler oracle
  why: A passing-looking document without an oracle is not conformance evidence.
  improve: Replace placeholders with an observable production assertion.
test/01_unit/compiler/native/simd_check_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/compiler/native/simd_check_spec.spl:21:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'converts to text' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/native/simd_check_spec.spl:27:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns correct bit width' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/native/simd_check_spec.spl:34:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'identifies integer types' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
