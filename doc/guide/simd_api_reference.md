# SIMD API Reference

**Status:** ⚠️ API DESIGN ONLY - No code generation implemented

**Location:** `src/std/simd.spl` (390 lines)

**Implemented:** API surface, platform detection stubs
**Not Implemented:** AVX2 codegen, NEON codegen, auto-vectorization, actual intrinsics

---

## Overview

The Simple SIMD API provides platform-independent vector operations that compile to:
- **x86_64:** AVX2 (256-bit) or SSE (128-bit) instructions
- **ARM:** NEON (128-bit) instructions

**Current Status:** API designed but backend code generation NOT implemented. Functions are declared but do not produce working code.

---

## Platform Detection

### `has_sse() -> bool`

Check if SSE (Streaming SIMD Extensions) is available on x86_64.

**Returns:** `true` if SSE supported, `false` otherwise

**Status:** ⚠️ Stub - Always returns `false` currently

**Example:**
```simple
use std.simd.{has_sse}

if has_sse():
    print "SSE available - can use 128-bit vectors"
else:
    print "No SSE - falling back to scalar"
```

---

### `has_avx() -> bool`

Check if AVX (Advanced Vector Extensions) is available on x86_64.

**Returns:** `true` if AVX supported, `false` otherwise

**Status:** ⚠️ Stub - Always returns `false` currently

---

### `has_avx2() -> bool`

Check if AVX2 (Advanced Vector Extensions 2) is available on x86_64.

**Returns:** `true` if AVX2 supported, `false` otherwise

**Status:** ⚠️ Stub - Always returns `false` currently

**Note:** AVX2 adds integer operations to AVX's floating-point operations.

---

### `has_neon() -> bool`

Check if ARM NEON is available (128-bit SIMD for ARM processors).

**Returns:** `true` if NEON supported, `false` otherwise

**Status:** ⚠️ Stub - Always returns `false` currently

---

## Vector Types (Planned)

These types are **not yet implemented** but are part of the API design:

### Floating-Point Vectors

```simple
# 32-bit floats (single precision)
Vec4f   # 4x f32 (128-bit) - SSE, NEON
Vec8f   # 8x f32 (256-bit) - AVX/AVX2

# 64-bit floats (double precision)
Vec2d   # 2x f64 (128-bit) - SSE2
Vec4d   # 4x f64 (256-bit) - AVX
```

### Integer Vectors

```simple
# 32-bit integers
Vec4i   # 4x i32 (128-bit)
Vec8i   # 8x i32 (256-bit)

# 64-bit integers
Vec2l   # 2x i64 (128-bit)
Vec4l   # 4x i64 (256-bit)
```

**Status:** ⚠️ Type definitions not implemented

---

## Arithmetic Operations (Planned)

### Addition

```simple
# 32-bit float addition (4-wide)
fn simd_add_f32x4(a: Vec4f, b: Vec4f) -> Vec4f

# 32-bit float addition (8-wide)
fn simd_add_f32x8(a: Vec8f, b: Vec8f) -> Vec8f

# 32-bit integer addition (4-wide)
fn simd_add_i32x4(a: Vec4i, b: Vec4i) -> Vec4i

# 32-bit integer addition (8-wide)
fn simd_add_i32x8(a: Vec8i, b: Vec8i) -> Vec8i
```

**Status:** ⚠️ Declared but not implemented
**Backend:** Would compile to `vaddps` (AVX) or `vadd.f32` (NEON)

---

### Subtraction

```simple
fn simd_sub_f32x4(a: Vec4f, b: Vec4f) -> Vec4f
fn simd_sub_f32x8(a: Vec8f, b: Vec8f) -> Vec8f
fn simd_sub_i32x4(a: Vec4i, b: Vec4i) -> Vec4i
fn simd_sub_i32x8(a: Vec8i, b: Vec8i) -> Vec8i
```

**Status:** ⚠️ Declared but not implemented

---

### Multiplication

```simple
fn simd_mul_f32x4(a: Vec4f, b: Vec4f) -> Vec4f
fn simd_mul_f32x8(a: Vec8f, b: Vec8f) -> Vec8f
fn simd_mul_i32x4(a: Vec4i, b: Vec4i) -> Vec4i
fn simd_mul_i32x8(a: Vec8i, b: Vec8i) -> Vec8i
```

**Status:** ⚠️ Declared but not implemented

---

### Division

```simple
fn simd_div_f32x4(a: Vec4f, b: Vec4f) -> Vec4f
fn simd_div_f32x8(a: Vec8f, b: Vec8f) -> Vec8f
# Note: Integer division not provided (no direct SIMD instruction)
```

**Status:** ⚠️ Declared but not implemented

---

### Fused Multiply-Add (FMA)

```simple
# a * b + c (single instruction, higher precision)
fn simd_fma_f32x4(a: Vec4f, b: Vec4f, c: Vec4f) -> Vec4f
fn simd_fma_f32x8(a: Vec8f, b: Vec8f, c: Vec8f) -> Vec8f
```

**Status:** ⚠️ Declared but not implemented
**Requires:** FMA3 instruction set on x86_64

---

## Comparison Operations (Planned)

```simple
# Equal
fn simd_eq_f32x4(a: Vec4f, b: Vec4f) -> Vec4i  # Returns mask
fn simd_eq_f32x8(a: Vec8f, b: Vec8f) -> Vec8i

# Less than
fn simd_lt_f32x4(a: Vec4f, b: Vec4f) -> Vec4i
fn simd_lt_f32x8(a: Vec8f, b: Vec8f) -> Vec8i

# Less than or equal
fn simd_le_f32x4(a: Vec4f, b: Vec4f) -> Vec4i
fn simd_le_f32x8(a: Vec8f, b: Vec8f) -> Vec8i

# Greater than
fn simd_gt_f32x4(a: Vec4f, b: Vec4f) -> Vec4i
fn simd_gt_f32x8(a: Vec8f, b: Vec8f) -> Vec8i

# Greater than or equal
fn simd_ge_f32x4(a: Vec4f, b: Vec4f) -> Vec4i
fn simd_ge_f32x8(a: Vec8f, b: Vec8f) -> Vec8i
```

**Status:** ⚠️ Declared but not implemented
**Returns:** Integer vector with lanes set to all 1s (true) or all 0s (false)

---

## Load/Store Operations (Planned)

### Load from Array

```simple
# Load 4 floats from array at index
fn simd_load_f32x4(array: [f32], index: i64) -> Vec4f

# Load 8 floats from array at index
fn simd_load_f32x8(array: [f32], index: i64) -> Vec8f

# Aligned load (faster, requires 16/32-byte alignment)
fn simd_load_aligned_f32x4(array: [f32], index: i64) -> Vec4f
fn simd_load_aligned_f32x8(array: [f32], index: i64) -> Vec8f
```

**Status:** ⚠️ Declared but not implemented
**Note:** Unaligned loads are slower but safer

---

### Store to Array

```simple
# Store 4 floats to array at index
fn simd_store_f32x4(array: [f32], index: i64, vec: Vec4f)

# Store 8 floats to array at index
fn simd_store_f32x8(array: [f32], index: i64, vec: Vec8f)

# Aligned store (faster, requires 16/32-byte alignment)
fn simd_store_aligned_f32x4(array: [f32], index: i64, vec: Vec4f)
fn simd_store_aligned_f32x8(array: [f32], index: i64, vec: Vec8f)
```

**Status:** ⚠️ Declared but not implemented

---

### Splat (Broadcast)

```simple
# Create vector with all lanes set to same value
fn simd_splat_f32x4(value: f32) -> Vec4f
fn simd_splat_f32x8(value: f32) -> Vec8f
fn simd_splat_i32x4(value: i32) -> Vec4i
fn simd_splat_i32x8(value: i32) -> Vec8i
```

**Status:** ⚠️ Declared but not implemented
**Example:** `simd_splat_f32x4(3.14)` → `[3.14, 3.14, 3.14, 3.14]`

---

## Reduction Operations (Planned)

### Horizontal Add

Sum all lanes of a vector into a scalar.

```simple
fn simd_hadd_f32x4(vec: Vec4f) -> f32  # Sum 4 lanes
fn simd_hadd_f32x8(vec: Vec8f) -> f32  # Sum 8 lanes
fn simd_hadd_i32x4(vec: Vec4i) -> i32
fn simd_hadd_i32x8(vec: Vec8i) -> i32
```

**Status:** ⚠️ Declared but not implemented

---

### Horizontal Max/Min

```simple
fn simd_hmax_f32x4(vec: Vec4f) -> f32
fn simd_hmax_f32x8(vec: Vec8f) -> f32
fn simd_hmin_f32x4(vec: Vec4f) -> f32
fn simd_hmin_f32x8(vec: Vec8f) -> f32
```

**Status:** ⚠️ Declared but not implemented

---

## Auto-Vectorization (Planned)

The compiler should automatically vectorize simple loops:

```simple
# Scalar code (written by user)
fn array_add(a: [f32], b: [f32], c: [f32], n: i64):
    for i in 0..n:
        c[i] = a[i] + b[i]

# Compiler should transform to (conceptually):
fn array_add_vectorized(a: [f32], b: [f32], c: [f32], n: i64):
    var i = 0
    # Vector loop (process 8 elements at a time)
    while i + 8 <= n:
        val va = simd_load_f32x8(a, i)
        val vb = simd_load_f32x8(b, i)
        val vc = simd_add_f32x8(va, vb)
        simd_store_f32x8(c, i, vc)
        i = i + 8
    # Scalar remainder loop
    while i < n:
        c[i] = a[i] + b[i]
        i = i + 1
```

**Status:** ⚠️ Auto-vectorization pass exists but is a stub with `pass_do_nothing` placeholders

**Location:** `src/compiler/mir_opt/auto_vectorize.spl`

**Planned Features:**
- Loop dependency analysis
- Vectorizability validation
- Cost model estimation
- Vector prologue/body/epilogue generation

---

## Example Usage (When Implemented)

### Explicit SIMD (Future)

```simple
use std.simd.{Vec4f, simd_add_f32x4, simd_mul_f32x4, simd_splat_f32x4}

fn dot_product_simd(a: [f32], b: [f32], n: i64) -> f32:
    var sum = simd_splat_f32x4(0.0)
    var i = 0

    # Process 4 elements at a time
    while i + 4 <= n:
        val va = simd_load_f32x4(a, i)
        val vb = simd_load_f32x4(b, i)
        val prod = simd_mul_f32x4(va, vb)
        sum = simd_add_f32x4(sum, prod)
        i = i + 4

    # Horizontal sum
    var result = simd_hadd_f32x4(sum)

    # Handle remainder
    while i < n:
        result = result + (a[i] * b[i])
        i = i + 1

    result
```

**Note:** This example will NOT work until backend code generation is implemented.

---

## Limitations (Current Implementation)

⚠️ **These components are NOT implemented:**

1. **Vector types** - Vec4f, Vec8f, Vec4i, etc. don't exist
2. **Intrinsic functions** - All simd_* functions are stubs
3. **x86_64 AVX2 codegen** - No instruction encoding (`src/compiler/backend/native/x86_64_simd.spl` missing, 800 lines planned)
4. **ARM NEON codegen** - No instruction encoding (`src/compiler/backend/native/arm_neon.spl` missing, 700 lines planned)
5. **Auto-vectorization** - Stub only, no actual loop transformation (`src/compiler/mir_opt/auto_vectorize.spl` is 80 lines of stubs)
6. **Platform detection** - Stubs always return `false`

**Current Status:**
- ✅ API design complete
- ✅ Function signatures documented
- ❌ Backend code generation NOT implemented
- ❌ No working SIMD code
- ❌ Auto-vectorization NOT implemented

---

## Future Implementation

See `COMPREHENSIVE_IMPLEMENTATION_PLAN_2026-02-14.md` Section 2 for complete plan:

**Planned Components:**
1. x86_64 AVX2 codegen (~800 lines, 80 tests) - VEX encoding, YMM registers
2. ARM NEON codegen (~700 lines, 60 tests) - NEON encoding, Q registers
3. Auto-vectorization pass (~1200 lines, 100 tests) - Loop analysis, cost model
4. Integration and benchmarks (20 benchmarks)

**Estimated Effort:** 14 days of development

**Expected Performance:** 7x speedup for vectorizable loops (based on typical SIMD gains)

---

## See Also

- `src/std/simd.spl` - API surface definition
- `src/compiler/mir_opt/auto_vectorize.spl` - Auto-vectorization stub
- `src/compiler/mir_opt/simd_lowering.spl` - SIMD lowering pass
- `COMPREHENSIVE_IMPLEMENTATION_PLAN_2026-02-14.md` - Implementation plan
- `DOCUMENTATION_REALITY_CHECK_2026-02-14.md` - Current status

---

**Last Updated:** 2026-02-14
**Implementation Status:** API design only (10% complete)
**Production Ready:** ❌ No - No code generation implemented
