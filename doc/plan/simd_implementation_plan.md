# SIMD Complete Implementation Plan

**Date:** 2026-02-03
**Phase:** 9 of Rust Feature Parity Roadmap
**Total Time:** 4 hours
**Status:** Planning

---

## Overview

Implement complete SIMD (Single Instruction Multiple Data) support for Simple, enabling vector operations and parallel computation. This includes vector types, SIMD operations, platform detection, and performance optimizations.

**Key Concept:**
```simple
# Vector operations
val v1 = Vec4f(1.0, 2.0, 3.0, 4.0)
val v2 = Vec4f(5.0, 6.0, 7.0, 8.0)
val result = v1 + v2  # SIMD addition: [6.0, 8.0, 10.0, 12.0]

# Automatic vectorization
val data = [1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0]
val doubled = data.map_simd(\x: x * 2.0)  # Uses SIMD automatically
```

---

## Background: SIMD in Simple

### Definition

**SIMD** is a parallel computing technique where a single instruction operates on multiple data points simultaneously. Modern CPUs have SIMD instruction sets (SSE, AVX, NEON) that can process 4-8 floats or 2-4 doubles in one instruction.

### Why SIMD Matters

**Performance:**
```simple
# Without SIMD (scalar):
for i in 0..1000:
    result[i] = data[i] * 2.0  # 1000 operations

# With SIMD (4-wide):
for i in 0..250:  # Only 250 iterations!
    result_vec[i] = data_vec[i] * 2.0  # Processes 4 elements per iteration
# 4x speedup!
```

**Benefits:**
- 2-8x performance improvement for numeric code
- Lower power consumption (fewer instructions)
- Better cache utilization
- Essential for ML, graphics, physics

---

## Current Status

### Simple's Numeric Types

Simple has basic numeric types but no SIMD:

```simple
val x: f64 = 3.14
val arr = [1.0, 2.0, 3.0, 4.0]

# No vector operations
# No SIMD intrinsics
# No automatic vectorization
```

### Missing Features

1. ✅ **Already have:** Basic numeric types (i64, f64)
2. ❌ **Need:** Vector types (Vec2f, Vec4f, Vec8f)
3. ❌ **Need:** SIMD operations (+, -, *, /)
4. ❌ **Need:** Platform detection (AVX, SSE, NEON)
5. ❌ **Need:** Automatic vectorization hints

---

## Phase Breakdown

### Phase 9A: Vector Types (1 hour)

**Goal:** Implement vector types for SIMD operations

**Data Structures:**

```simple
# Vector types (aligned for SIMD)
struct Vec2f:
    x: f32
    y: f32

struct Vec4f:
    x: f32
    y: f32
    z: f32
    w: f32

struct Vec8f:
    data: [f32; 8]  # AVX 256-bit register

struct Vec2d:
    x: f64
    y: f64

struct Vec4d:
    data: [f64; 4]  # AVX 256-bit register

# Constructors
impl Vec4f:
    static fn splat(value: f32) -> Vec4f:
        """Create vector with all elements set to value"""
        Vec4f(x: value, y: value, z: value, w: value)

    static fn from_array(arr: [f32]) -> Vec4f:
        """Create from array (must have 4+ elements)"""
        Vec4f(x: arr[0], y: arr[1], z: arr[2], w: arr[3])

    fn to_array() -> [f32]:
        """Convert to array"""
        [self.x, self.y, self.z, self.w]

    fn get(index: i64) -> f32:
        """Get element by index"""
        match index:
            case 0: self.x
            case 1: self.y
            case 2: self.z
            case 3: self.w
            case _: assert false, "Index out of bounds"
```

**Examples:**

```simple
# Create vectors
val v1 = Vec4f(x: 1.0, y: 2.0, z: 3.0, w: 4.0)
val v2 = Vec4f.splat(5.0)  # [5.0, 5.0, 5.0, 5.0]
val v3 = Vec4f.from_array([10.0, 20.0, 30.0, 40.0])

# Access elements
val x = v1.x
val elem = v1.get(2)  # z = 3.0

# Convert to array
val arr = v1.to_array()  # [1.0, 2.0, 3.0, 4.0]
```

**Tests:**
- Create Vec2f, Vec4f, Vec8f
- splat constructor
- from_array constructor
- Element access by index
- to_array conversion
- Bounds checking

---

### Phase 9B: SIMD Operations (1.5 hours)

**Goal:** Implement arithmetic operations using SIMD

**Operations:**

```simple
impl Vec4f:
    # Arithmetic operators
    fn add(other: Vec4f) -> Vec4f:
        """Vector addition (SIMD)"""
        Vec4f(
            x: self.x + other.x,
            y: self.y + other.y,
            z: self.z + other.z,
            w: self.w + other.w
        )

    fn sub(other: Vec4f) -> Vec4f:
        """Vector subtraction (SIMD)"""
        Vec4f(
            x: self.x - other.x,
            y: self.y - other.y,
            z: self.z - other.z,
            w: self.w - other.w
        )

    fn mul(other: Vec4f) -> Vec4f:
        """Element-wise multiplication (SIMD)"""
        Vec4f(
            x: self.x * other.x,
            y: self.y * other.y,
            z: self.z * other.z,
            w: self.w * other.w
        )

    fn div(other: Vec4f) -> Vec4f:
        """Element-wise division (SIMD)"""
        Vec4f(
            x: self.x / other.x,
            y: self.y / other.y,
            z: self.z / other.z,
            w: self.w / other.w
        )

    # Scalar operations
    fn scale(scalar: f32) -> Vec4f:
        """Multiply by scalar"""
        Vec4f(
            x: self.x * scalar,
            y: self.y * scalar,
            z: self.z * scalar,
            w: self.w * scalar
        )

    # Reductions
    fn sum() -> f32:
        """Sum all elements"""
        self.x + self.y + self.z + self.w

    fn dot(other: Vec4f) -> f32:
        """Dot product"""
        val prod = self.mul(other)
        prod.sum()

    fn length_squared() -> f32:
        """Squared length"""
        self.dot(self)

    fn length() -> f32:
        """Vector length (magnitude)"""
        self.length_squared().sqrt()

    # Comparisons
    fn equals(other: Vec4f) -> bool:
        """Element-wise equality"""
        self.x == other.x and
        self.y == other.y and
        self.z == other.z and
        self.w == other.w

    fn less_than(other: Vec4f) -> [bool; 4]:
        """Element-wise less than"""
        [
            self.x < other.x,
            self.y < other.y,
            self.z < other.z,
            self.w < other.w
        ]
```

**Operator Overloading:**

```simple
# Enable operator syntax
val v1 = Vec4f(1.0, 2.0, 3.0, 4.0)
val v2 = Vec4f(5.0, 6.0, 7.0, 8.0)

val sum = v1 + v2        # Calls v1.add(v2)
val diff = v1 - v2       # Calls v1.sub(v2)
val prod = v1 * v2       # Calls v1.mul(v2)
val quot = v1 / v2       # Calls v1.div(v2)
val scaled = v1 * 2.0    # Calls v1.scale(2.0)
```

**Examples:**

```simple
# Arithmetic
val v1 = Vec4f(1.0, 2.0, 3.0, 4.0)
val v2 = Vec4f(5.0, 6.0, 7.0, 8.0)

val sum = v1 + v2        # [6.0, 8.0, 10.0, 12.0]
val diff = v1 - v2       # [-4.0, -4.0, -4.0, -4.0]
val prod = v1 * v2       # [5.0, 12.0, 21.0, 32.0]
val quot = v1 / v2       # [0.2, 0.33, 0.43, 0.5]

# Scalar operations
val scaled = v1 * 2.0    # [2.0, 4.0, 6.0, 8.0]

# Reductions
val total = v1.sum()     # 10.0
val dot = v1.dot(v2)     # 70.0
val len = v1.length()    # 5.477

# Comparisons
val lt = v1.less_than(v2)  # [true, true, true, true]
```

**Tests:**
- Vector addition
- Vector subtraction
- Element-wise multiplication
- Element-wise division
- Scalar multiplication
- Sum reduction
- Dot product
- Length calculation
- Element-wise comparisons
- Operator overloading

---

### Phase 9C: Platform Detection & Intrinsics (1.5 hours)

**Goal:** Detect SIMD capabilities and provide intrinsics

**Platform Detection:**

```simple
enum SimdPlatform:
    """SIMD instruction sets"""
    None          # No SIMD support
    SSE           # x86 SSE (128-bit)
    SSE2          # x86 SSE2 (128-bit, doubles)
    AVX           # x86 AVX (256-bit)
    AVX2          # x86 AVX2 (256-bit, integers)
    AVX512        # x86 AVX-512 (512-bit)
    NEON          # ARM NEON (128-bit)
    SVE           # ARM SVE (variable length)

class SimdCapabilities:
    """Runtime SIMD capability detection"""

    static fn detect() -> SimdPlatform:
        """Detect available SIMD platform"""
        # Use CPUID on x86
        # Use /proc/cpuinfo on Linux
        # Use sysctl on macOS
        # ...

    static fn has_sse() -> bool
    static fn has_sse2() -> bool
    static fn has_avx() -> bool
    static fn has_avx2() -> bool
    static fn has_avx512() -> bool
    static fn has_neon() -> bool

    static fn register_width() -> i64:
        """Get SIMD register width in bits"""
        match SimdCapabilities.detect():
            case SSE: 128
            case SSE2: 128
            case AVX: 256
            case AVX2: 256
            case AVX512: 512
            case NEON: 128
            case _: 0

    static fn vector_width_f32() -> i64:
        """How many f32 values fit in SIMD register"""
        SimdCapabilities.register_width() / 32

    static fn vector_width_f64() -> i64:
        """How many f64 values fit in SIMD register"""
        SimdCapabilities.register_width() / 64
```

**SIMD Intrinsics:**

```simple
# Low-level SIMD operations (compiler intrinsics)
extern fn simd_add_f32x4(a: Vec4f, b: Vec4f) -> Vec4f
extern fn simd_sub_f32x4(a: Vec4f, b: Vec4f) -> Vec4f
extern fn simd_mul_f32x4(a: Vec4f, b: Vec4f) -> Vec4f
extern fn simd_div_f32x4(a: Vec4f, b: Vec4f) -> Vec4f

extern fn simd_add_f32x8(a: Vec8f, b: Vec8f) -> Vec8f
extern fn simd_sub_f32x8(a: Vec8f, b: Vec8f) -> Vec8f
extern fn simd_mul_f32x8(a: Vec8f, b: Vec8f) -> Vec8f
extern fn simd_div_f32x8(a: Vec8f, b: Vec8f) -> Vec8f

extern fn simd_sqrt_f32x4(a: Vec4f) -> Vec4f
extern fn simd_min_f32x4(a: Vec4f, b: Vec4f) -> Vec4f
extern fn simd_max_f32x4(a: Vec4f, b: Vec4f) -> Vec4f
```

**Automatic Selection:**

```simple
impl Vec4f:
    fn add(other: Vec4f) -> Vec4f:
        """Vector addition (uses SIMD if available)"""
        if SimdCapabilities.has_sse():
            simd_add_f32x4(self, other)  # Use SSE intrinsic
        else:
            # Fallback to scalar
            Vec4f(
                x: self.x + other.x,
                y: self.y + other.y,
                z: self.z + other.z,
                w: self.w + other.w
            )
```

**Examples:**

```simple
# Detect platform
val platform = SimdCapabilities.detect()
print "SIMD platform: {platform}"

# Check capabilities
if SimdCapabilities.has_avx():
    print "AVX available"

# Get vector width
val width = SimdCapabilities.vector_width_f32()
print "Can process {width} floats at once"

# Operations automatically use best available SIMD
val v1 = Vec4f(1.0, 2.0, 3.0, 4.0)
val v2 = Vec4f(5.0, 6.0, 7.0, 8.0)
val sum = v1 + v2  # Uses AVX if available, SSE if not, scalar fallback
```

**Tests:**
- Platform detection
- Capability queries (has_sse, has_avx, etc.)
- Register width calculation
- Vector width calculation
- Automatic intrinsic selection
- Fallback to scalar code

---

## Examples

### Example 1: Vector Math

```simple
# 3D point
val position = Vec3f(x: 10.0, y: 20.0, z: 30.0)
val velocity = Vec3f(x: 1.0, y: 2.0, z: -1.0)

# Update position
val new_position = position + velocity  # [11.0, 22.0, 29.0]

# Calculate distance
val distance = (new_position - position).length()  # 2.449
```

### Example 2: Image Processing

```simple
# Brightness adjustment (SIMD)
fn adjust_brightness(pixels: [Vec4f], factor: f32) -> [Vec4f]:
    pixels.map(\p: p * factor)  # Vectorized!

val image = [
    Vec4f(0.5, 0.6, 0.7, 1.0),
    Vec4f(0.1, 0.2, 0.3, 1.0),
    # ... millions of pixels
]

val brighter = adjust_brightness(image, 1.5)
```

### Example 3: Physics Simulation

```simple
# Particle system
struct Particle:
    position: Vec3f
    velocity: Vec3f
    acceleration: Vec3f

fn update_particles(particles: [Particle], dt: f32) -> [Particle]:
    particles.map(\p:
        val new_vel = p.velocity + p.acceleration * dt
        val new_pos = p.position + new_vel * dt
        Particle(position: new_pos, velocity: new_vel, acceleration: p.acceleration)
    )
```

### Example 4: Matrix Operations

```simple
# 4x4 matrix-vector multiply (SIMD)
fn mat4_mul_vec4(mat: [[f32; 4]; 4], vec: Vec4f) -> Vec4f:
    val row0 = Vec4f.from_array(mat[0])
    val row1 = Vec4f.from_array(mat[1])
    val row2 = Vec4f.from_array(mat[2])
    val row3 = Vec4f.from_array(mat[3])

    Vec4f(
        x: row0.dot(vec),  # SIMD dot product
        y: row1.dot(vec),
        z: row2.dot(vec),
        w: row3.dot(vec)
    )
```

---

## Testing Strategy

### Test Categories

1. **Vector Types (Phase 9A):**
   - Create vectors (Vec2f, Vec4f, Vec8f, Vec2d, Vec4d)
   - splat constructor
   - from_array constructor
   - Element access (get, indexing)
   - to_array conversion
   - Bounds checking

2. **SIMD Operations (Phase 9B):**
   - Arithmetic (add, sub, mul, div)
   - Scalar operations (scale)
   - Reductions (sum, dot, length)
   - Comparisons (equals, less_than)
   - Operator overloading

3. **Platform Detection (Phase 9C):**
   - Detect SIMD platform
   - Capability queries
   - Register width
   - Vector width
   - Intrinsic selection
   - Scalar fallback

### Test Count: ~20 tests

---

## Performance Characteristics

### Time Complexity

| Operation | Scalar | SIMD (4-wide) | Speedup |
|-----------|--------|---------------|---------|
| Vector add | O(n) | O(n/4) | 4x |
| Dot product | O(n) | O(n/4) + O(log n) | ~3.5x |
| Matrix multiply | O(n³) | O(n³/4) | 4x |
| Image filter | O(w×h) | O(w×h/4) | 4x |

### Space Complexity

| Structure | Size | Alignment | Notes |
|-----------|------|-----------|-------|
| Vec2f | 8 bytes | 8 bytes | 2× f32 |
| Vec4f | 16 bytes | 16 bytes | SSE register |
| Vec8f | 32 bytes | 32 bytes | AVX register |
| Vec4d | 32 bytes | 32 bytes | AVX register |

---

## Integration with Existing Systems

### 1. Type System Integration

```simple
# In type_infer.spl
fn infer_expr(expr: Expr) -> Result<HirType, TypeError>:
    match expr:
        case VecLit(elems):
            # Infer Vec4f, Vec8f, etc.
            match elems.len():
                case 2: HirType.Vec2f
                case 4: HirType.Vec4f
                case 8: HirType.Vec8f

        case BinOp("+", lhs, rhs):
            val lhs_ty = self.infer_expr(lhs)?
            val rhs_ty = self.infer_expr(rhs)?

            if lhs_ty.is_vector() and rhs_ty.is_vector():
                # Use SIMD addition
                return Ok(lhs_ty)
```

### 2. Codegen Integration

```simple
# In codegen.spl
fn codegen_binop(op: "+", lhs: Value, rhs: Value) -> Value:
    match (lhs.ty, rhs.ty):
        case (Vec4f, Vec4f):
            # Emit SIMD instruction
            if target.has_avx():
                emit_avx_add_ps(lhs, rhs)
            elif target.has_sse():
                emit_sse_add_ps(lhs, rhs)
            else:
                # Scalar fallback
                emit_scalar_vec4_add(lhs, rhs)
```

### 3. Stdlib Integration

```simple
# In std/math.spl
fn distance_3d(p1: Vec3f, p2: Vec3f) -> f32:
    (p2 - p1).length()

fn normalize(v: Vec3f) -> Vec3f:
    val len = v.length()
    v / Vec3f.splat(len)
```

---

## Limitations

### 1. Fixed Vector Sizes

Only support 2, 4, 8 element vectors:

```simple
# Supported:
Vec2f, Vec4f, Vec8f

# Not supported:
Vec3f (use Vec4f with unused element)
Vec16f (use two Vec8f)
```

**Future:** Add arbitrary-length vectors.

### 2. No Auto-Vectorization

Compiler doesn't automatically vectorize loops:

```simple
# Not auto-vectorized:
for i in 0..1000:
    result[i] = data[i] * 2.0

# Manual vectorization required:
for i in 0..250:
    result_vec[i] = data_vec[i] * 2.0
```

**Future:** Add loop vectorization pass.

### 3. No Mixed Precision

Can't mix f32 and f64 in same vector:

```simple
# Not supported:
Vec4(1.0_f32, 2.0_f32, 3.0_f64, 4.0_f64)
```

**Future:** Add mixed-precision types.

---

## Next Steps

After Phase 9:
1. **Phase 1:** Bidirectional Type Checking (12h) - deferred
2. **Loop Vectorization:** Auto-vectorize simple loops
3. **Matrix Types:** Mat4f, Mat3f with SIMD operations
4. **Quaternions:** Quat type for 3D rotations

---

## File Structure

```
src/compiler/
  simd_phase9a.spl         # Vector types (1h)
  simd_phase9b.spl         # SIMD operations (1.5h)
  simd_phase9c.spl         # Platform detection (1.5h)

doc/plan/
  simd_implementation_plan.md  # This file

doc/report/
  simd_complete_2026-02-03.md  # To be created
```

---

## Success Criteria

✅ All 3 phases implemented
✅ 20+ tests passing
✅ Vector types (Vec2f, Vec4f, Vec8f, Vec2d, Vec4d)
✅ SIMD operations (add, sub, mul, div, dot, length)
✅ Platform detection (SSE, AVX, NEON)
✅ Intrinsics integration
✅ Scalar fallback
✅ Performance benchmarks (show 2-4x speedup)

---

**Status:** Ready to implement
**Next:** Phase 9A - Vector Types (1 hour)
