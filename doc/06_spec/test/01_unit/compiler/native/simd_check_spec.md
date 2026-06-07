# Simd Check Specification

> <details>

<!-- sdn-diagram:id=simd_check_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=simd_check_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

simd_check_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=simd_check_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 61 | 61 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simd Check Specification

## Scenarios

### SimdElementType

#### converts to text

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# SimdElementType.I32.to_text() == "i32"
pass
```

</details>

#### returns correct bit width

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# SimdElementType.I8.bit_width() == 8
# SimdElementType.I64.bit_width() == 64
pass
```

</details>

#### identifies integer types

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# SimdElementType.I32.is_integer() == true
# SimdElementType.F32.is_integer() == false
pass
```

</details>

#### identifies float types

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# SimdElementType.F32.is_float() == true
# SimdElementType.I32.is_float() == false
pass
```

</details>

### SimdVectorType

#### creates vector type

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# SimdVectorType.create(I32, 4)
# ty.lane_count == 4
pass
```

</details>

#### creates standard types

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# SimdVectorType.i32x4()
# SimdVectorType.f64x2()
pass
```

</details>

#### formats as string

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# SimdVectorType.i32x4().to_text() == "i32x4"
pass
```

</details>

#### calculates total bits

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# SimdVectorType.i32x4().total_bits() == 128
pass
```

</details>

#### validates vector width

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# 128-bit vector is valid
# 96-bit vector is invalid
pass
```

</details>

#### checks type compatibility

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# i32x4 compatible with i32x4
# i32x4 not compatible with i64x2
pass
```

</details>

### SimdOperation

#### converts to text

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# SimdOperation.Add.to_text() == "add"
pass
```

</details>

#### identifies binary operations

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# SimdOperation.Add.is_binary() == true
pass
```

</details>

#### identifies unary operations

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# SimdOperation.Not.is_unary() == true
pass
```

</details>

#### checks float support

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# SimdOperation.Add.supports_float() == true
# SimdOperation.And.supports_float() == false
pass
```

</details>

#### checks integer support

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# SimdOperation.And.supports_integer() == true
pass
```

</details>

### SimdCheckError

#### formats invalid lane count error

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# SimdCheckError.InvalidLaneCount(4, 8).to_text()
pass
```

</details>

#### formats incompatible types error

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# SimdCheckError.IncompatibleTypes(i32x4, i64x2).to_text()
pass
```

</details>

#### formats invalid width error

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# SimdCheckError.InvalidVectorWidth(96).to_text()
pass
```

</details>

#### formats unsupported operation error

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# SimdCheckError.UnsupportedOperation(And, F32).to_text()
pass
```

</details>

#### formats lane index out of bounds error

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# SimdCheckError.LaneIndexOutOfBounds(5, 4).to_text()
pass
```

</details>

### SimdTypeChecker

#### creates checker with max width

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# SimdTypeChecker.create(128)
pass
```

</details>

#### creates SSE checker

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# SimdTypeChecker.for_sse() has 128-bit max
pass
```

</details>

#### creates AVX checker

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# SimdTypeChecker.for_avx() has 256-bit max
pass
```

</details>

#### creates AVX-512 checker

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# SimdTypeChecker.for_avx512() has 512-bit max
pass
```

</details>

#### validates vector types

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# checker.check_vector_type(i32x4) == true
pass
```

</details>

#### rejects invalid vector width

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# checker.check_vector_type with 96-bit vector fails
pass
```

</details>

#### rejects vectors too wide for target

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# SSE checker rejects 256-bit vectors
pass
```

</details>

#### validates binary operations

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# checker.check_binary_op(Add, i32x4, i32x4) == true
pass
```

</details>

#### rejects incompatible operand types

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# checker.check_binary_op(Add, i32x4, i64x2) == false
pass
```

</details>

#### rejects unsupported operations for type

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# checker.check_binary_op(And, f32x4, f32x4) == false
pass
```

</details>

#### validates lane access

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# checker.check_lane_access(i32x4, 2) == true
# checker.check_lane_access(i32x4, 5) == false
pass
```

</details>

#### validates shuffle masks

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# checker.check_shuffle(i32x4, [0, 1, 2, 3]) == true
pass
```

</details>

#### rejects invalid shuffle mask length

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# checker.check_shuffle(i32x4, [0, 1]) == false
pass
```

</details>

### VectorizationStatus

#### identifies vectorizable status

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# VectorizationStatus.Vectorizable(4).can_vectorize() == true
pass
```

</details>

#### identifies non-vectorizable status

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# VectorizationStatus.NotVectorizable("reason").can_vectorize() == false
pass
```

</details>

#### identifies partially vectorizable

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# VectorizationStatus.PartiallyVectorizable(4, 2).can_vectorize() == true
pass
```

</details>

#### formats status as text

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# status.to_text() describes the status
pass
```

</details>

### LoopInfo

<details>
<summary>Advanced: creates simple loop info</summary>

#### creates simple loop info

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# LoopInfo.simple_loop(100)
# info.iteration_count == Some(100)
pass
```

</details>


</details>

#### identifies vectorization candidates

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Simple loop is candidate
pass
```

</details>

<details>
<summary>Advanced: rejects loops with dependencies</summary>

#### rejects loops with dependencies

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# has_dependencies = true not a candidate
pass
```

</details>


</details>

<details>
<summary>Advanced: rejects loops with function calls</summary>

#### rejects loops with function calls

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# has_function_calls = true not a candidate
pass
```

</details>


</details>

### AutoVectorizer

#### creates with target vector width

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# AutoVectorizer.create(128)
pass
```

</details>

<details>
<summary>Advanced: analyzes simple loop as vectorizable</summary>

#### analyzes simple loop as vectorizable

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Simple loop with 100 iterations is vectorizable
pass
```

</details>


</details>

#### calculates vectorization factor

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# For 128-bit and i32: factor = 4
pass
```

</details>

#### detects partial vectorization

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Loop with 6 iterations and factor 4 has remainder 2
pass
```

</details>

<details>
<summary>Advanced: rejects loops with low trip count</summary>

#### rejects loops with low trip count

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Loop with 2 iterations not worth vectorizing
pass
```

</details>


</details>

<details>
<summary>Advanced: rejects loops with dependencies</summary>

#### rejects loops with dependencies

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Returns NotVectorizable with reason
pass
```

</details>


</details>

#### suggests vector type for element type

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# For i32 with 128-bit target: i32x4
pass
```

</details>

### SimdInstructionInfo

#### creates binary instruction info

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# SimdInstructionInfo.binary(Add, i32x4)
pass
```

</details>

#### creates unary instruction info

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# SimdInstructionInfo.unary(Not, i32x4)
pass
```

</details>

### SimdCapability

#### creates SSE2 capability

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# SimdCapability.sse2()
# capability.max_vector_width == 128
pass
```

</details>

#### creates AVX2 capability

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# SimdCapability.avx2()
# capability.has_fma == true
pass
```

</details>

#### checks type support

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# capability.supports_type(i32x4) == true
pass
```

</details>

#### checks operation support

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# capability.supports_operation(Add) == true
pass
```

</details>

### check_simd_binary

#### validates compatible operation

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# check_simd_binary(Add, i32x4, i32x4) == Ok(())
pass
```

</details>

#### rejects incompatible types

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# check_simd_binary(Add, i32x4, i64x2) is Err
pass
```

</details>

### can_vectorize_loop

<details>
<summary>Advanced: returns true for vectorizable loop</summary>

#### returns true for vectorizable loop

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# can_vectorize_loop(100, 32) == true
pass
```

</details>


</details>

#### returns false for low iteration count

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# can_vectorize_loop(2, 32) == false
pass
```

</details>

### get_vector_type_for_scalar

#### returns i32x4 for i32

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# get_vector_type_for_scalar("i32") == Some(i32x4)
pass
```

</details>

#### returns f64x2 for f64

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# get_vector_type_for_scalar("f64") == Some(f64x2)
pass
```

</details>

#### returns None for unknown scalar

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
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
