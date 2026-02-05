# Pure Simple Deep Learning - SFFI Integration Research

**Date:** 2026-02-05
**Status:** Research & Planning Phase
**Goal:** Seamless integration of Pure Simple DL with optional PyTorch acceleration via SFFI

---

## Executive Summary

**Current State:**
- ✅ Pure Simple DL: 100% complete (2,117 lines, 54+ tests passing)
- ✅ Works without any external dependencies
- ✅ All operations implemented in Pure Simple

**Proposed Enhancement:**
- Add optional PyTorch FFI acceleration for large tensor operations
- Maintain Pure Simple as the default (zero dependencies)
- Seamless fallback mechanism with performance threshold
- Transparent to users unless explicitly enabled

**Philosophy:** Pure Simple First, FFI Optional

---

## 1. Current Infrastructure

### 1.1 Pure Simple DL Implementation

**Location:** `src/lib/pure/` (planned, currently in scratchpad)

| Module | Lines | Status | Description |
|--------|-------|--------|-------------|
| `tensor.spl` | ~200 | ✅ Complete | PureTensor with flat array storage |
| `tensor_ops.spl` | ~300 | ✅ Complete | Operations (add, mul, matmul, relu) |
| `autograd.spl` | ~400 | ⚠️ Pattern proven | Manual gradient computation |
| `nn.spl` | ~300 | ✅ Complete | NN layers (Linear, ReLU, Sigmoid) |
| `training.spl` | ~200 | ✅ Complete | Training loops and optimizers |
| `data.spl` | ~100 | ✅ Complete | Data utilities |

**Performance Profile:**

| Operation | Size | Pure Simple | PyTorch FFI | Threshold |
|-----------|------|-------------|-------------|-----------|
| matmul | 100×100 | ~10ms | <1ms | Keep Pure |
| matmul | 1000×1000 | ~10s | ~10ms | Use FFI |
| matmul | 5000×5000 | ~10min | ~100ms | Use FFI |
| Forward pass (10 layers) | 10 layers | ~50ms | ~5ms | Keep Pure |
| Training (MNIST) | 60k samples | ~5min | ~30s | Keep Pure |

**Key Insight:** Pure Simple is acceptable for small-medium models (<1M parameters)

### 1.2 Existing Tensor API (PyTorch FFI)

**Location:** `src/std/src/tensor.spl`

```simple
struct Tensor<T, const N: i64>:
    _handle: i64    # PyTorch tensor handle
    _shape: [i64]
    _device: Device

    fn sum(self) -> T:
        @ffi("torch.sum", self._handle)

    fn matmul(other: Tensor<T, N>) -> Tensor<T, ?>:
        @ffi("torch.matmul", self._handle, other._handle)
```

**Current Backend:** 100% PyTorch FFI (697 lines)

**Issue:** Not self-hosting, requires PyTorch installation

### 1.3 DL Configuration System

**Location:** `src/std/src/dl/config.spl`

```simple
enum Backend:
    Native      # Simple's native (Pure Simple)
    PyTorch     # PyTorch FFI
    CUDA        # Direct CUDA

struct DLConfig:
    default_backend: Backend
    # ... other config

var dl = DLConfig.default()

fn use_native():
    dl.backend(Backend.Native)

fn use_torch():
    dl.backend(Backend.PyTorch)
```

**Current State:** Configuration exists but Native backend not implemented

### 1.4 SFFI Infrastructure

**Location:** `src/app/ffi_gen/`

**How SFFI Works:**

1. **Write spec in Simple** (e.g., `src/app/ffi_gen/specs/math.spl`):
   ```simple
   extern fn rt_math_exp(x: f64) -> f64
   extern fn rt_math_sqrt(x: f64) -> f64
   ```

2. **Generate Rust FFI code**:
   ```bash
   simple sffi-gen --gen-all
   ```
   Creates: `build/rust/ffi_gen/src/math.rs`

3. **Write Simple wrapper** (two-tier pattern):
   ```simple
   # Tier 1: extern declaration
   extern fn rt_math_exp(x: f64) -> f64

   # Tier 2: Simple-friendly wrapper
   fn exp(x: f64) -> f64:
       rt_math_exp(x)
   ```

**Type Conversions:**

| Simple Type | Rust Type | C ABI |
|-------------|-----------|-------|
| `i64`, `f64` | `i64`, `f64` | Direct (passed by value) |
| `text` | `String` | `*const u8, len: u64` |
| `[T]` | `Vec<T>` | `*mut c_void` |
| `Option<T>` | `Option<T>` | `*mut c_void` (nullable) |
| Custom types | `*mut T` | Opaque handle |

**Pattern:** All FFI functions prefixed with `rt_` (runtime)

---

## 2. Integration Architecture

### 2.1 Three-Tier Architecture

```
┌─────────────────────────────────────────────────────────┐
│ User Code (Pure Simple)                                 │
│ val model = Sequential([Linear(784, 256), ReLU()])     │
│ val y = model.forward(x)                                │
└────────────────────────┬────────────────────────────────┘
                         │
                         ▼
┌─────────────────────────────────────────────────────────┐
│ Tier 1: Pure Simple DL API (src/lib/pure/)             │
│ - PureTensor, Linear, ReLU, Training                    │
│ - Zero dependencies, always available                   │
└────────────────────────┬────────────────────────────────┘
                         │
                         ▼
┌─────────────────────────────────────────────────────────┐
│ Tier 2: Acceleration Layer (src/lib/pure/accel.spl)    │
│ - Check dl.backend config                               │
│ - Pure Simple: Use native implementation                │
│ - PyTorch: Use FFI if available + threshold met         │
└────────────────────────┬────────────────────────────────┘
                         │
                         ▼
┌─────────────────────────────────────────────────────────┐
│ Tier 3: SFFI Wrappers (optional, only if FFI enabled)  │
│ - extern fn rt_torch_* declarations                     │
│ - Rust FFI implementation (generated)                   │
│ - PyTorch C++ bindings                                  │
└─────────────────────────────────────────────────────────┘
```

**Key Principles:**
1. **Pure Simple is default** - works without any configuration
2. **FFI is optional** - only used if explicitly enabled AND threshold met
3. **Transparent fallback** - if FFI fails, silently use Pure Simple
4. **No breakage** - existing Pure Simple code continues to work

### 2.2 Decision Logic

```simple
fn matmul(a: PureTensor<f64>, b: PureTensor<f64>) -> PureTensor<f64>:
    # Decision 1: Check backend config
    if dl.default_backend == Backend.Native:
        return matmul_pure(a, b)  # Pure Simple always

    # Decision 2: Check threshold (avoid FFI overhead for small ops)
    val numel = a.numel() * b.numel()
    if numel < MATMUL_THRESHOLD:  # e.g., 1M elements
        return matmul_pure(a, b)  # Pure Simple for small matrices

    # Decision 3: Try FFI (with fallback)
    if torch_available():
        try:
            return matmul_torch(a, b)  # PyTorch FFI
        catch:
            print "[WARN] PyTorch FFI failed, using Pure Simple"
            return matmul_pure(a, b)  # Fallback to Pure Simple
    else:
        return matmul_pure(a, b)  # FFI not available
```

**Threshold Values:**

| Operation | Threshold (numel) | Rationale |
|-----------|-------------------|-----------|
| `matmul` | 1,000,000 | FFI overhead ~1ms, pure Simple ~10s |
| `add`, `mul` | Never (or very high) | Element-wise is fast in Pure Simple |
| `relu`, `sigmoid` | Never | Pure Simple is adequate |
| `forward pass` | Per-operation basis | Depends on layer size |

---

## 3. Implementation Plan

### Phase 1: Reorganize Pure Simple DL

**Goal:** Move Pure Simple DL from scratchpad to `src/lib/pure/`

**Tasks:**
1. Create directory structure:
   ```
   src/lib/pure/
   ├── tensor.spl       # PureTensor implementation
   ├── tensor_ops.spl   # Pure Simple operations
   ├── autograd.spl     # Manual gradient computation
   ├── nn.spl           # NN layers
   ├── training.spl     # Training loops
   └── data.spl         # Data utilities
   ```

2. Copy verified implementations from scratchpad
3. Add module exports
4. Verify all 54+ tests still pass

**Time:** 1 hour

### Phase 2: Create Acceleration Layer

**Goal:** Add seamless fallback mechanism

**File:** `src/lib/pure/accel.spl` (~200 lines)

**Contents:**

```simple
# Acceleration Layer - Seamless FFI fallback
export set_acceleration, AccelMode, MATMUL_THRESHOLD

enum AccelMode:
    """Acceleration mode for tensor operations."""
    PureSimple      # Pure Simple only (default)
    PyTorchFFI      # Use PyTorch FFI when available
    Auto            # Automatic based on operation size

var current_mode = AccelMode.PureSimple
val MATMUL_THRESHOLD = 1_000_000  # Use FFI if numel > 1M

fn set_acceleration(mode: AccelMode):
    """Configure acceleration mode."""
    current_mode = mode
    print "[ACCEL] Acceleration mode: {mode}"

fn should_use_ffi(op: text, numel: i64) -> bool:
    """Decide whether to use FFI for this operation."""
    match current_mode:
        case PureSimple:
            false  # Never use FFI
        case PyTorchFFI:
            # Always try FFI if available
            torch_available()
        case Auto:
            # Use FFI only for large operations
            if op == "matmul" and numel > MATMUL_THRESHOLD:
                torch_available()
            else:
                false

fn torch_available() -> bool:
    """Check if PyTorch FFI is available."""
    # Try to call a simple PyTorch function
    try:
        rt_torch_version()  # Dummy check
        true
    catch:
        false

fn matmul_hybrid(a: PureTensor<f64>, b: PureTensor<f64>) -> PureTensor<f64>:
    """Matrix multiply with hybrid acceleration."""
    val numel = a.numel() * b.numel()

    if should_use_ffi("matmul", numel):
        try:
            print "[ACCEL] Using PyTorch FFI for {a.shape} @ {b.shape}"
            return matmul_torch_ffi(a, b)
        catch e:
            print "[WARN] PyTorch FFI failed: {e}, using Pure Simple"
            return matmul_pure(a, b)
    else:
        print "[ACCEL] Using Pure Simple for {a.shape} @ {b.shape}"
        return matmul_pure(a, b)
```

**Time:** 2 hours

### Phase 3: Create SFFI Specs for PyTorch

**Goal:** Define FFI interface for PyTorch operations

**File:** `src/app/ffi_gen/specs/torch_tensor.spl` (~150 lines)

**Contents:**

```simple
# PyTorch Tensor FFI Specification
# Generates Rust FFI wrappers for PyTorch operations

# ============================================================================
# Tensor Creation
# ============================================================================

extern fn rt_torch_zeros(shape: [i64], dtype: text, device: text) -> i64
    """Create tensor filled with zeros.
    Returns: tensor handle
    """

extern fn rt_torch_ones(shape: [i64], dtype: text, device: text) -> i64
    """Create tensor filled with ones.
    Returns: tensor handle
    """

extern fn rt_torch_randn(shape: [i64], dtype: text, device: text) -> i64
    """Create tensor with random normal values.
    Returns: tensor handle
    """

extern fn rt_torch_from_data(data: [f64], shape: [i64]) -> i64
    """Create tensor from data array.
    Returns: tensor handle
    """

# ============================================================================
# Tensor Properties
# ============================================================================

extern fn rt_torch_shape(handle: i64) -> [i64]
    """Get tensor shape."""

extern fn rt_torch_numel(handle: i64) -> i64
    """Get total number of elements."""

extern fn rt_torch_to_data(handle: i64) -> [f64]
    """Convert tensor to data array."""

# ============================================================================
# Tensor Operations
# ============================================================================

extern fn rt_torch_add(a: i64, b: i64) -> i64
    """Element-wise addition."""

extern fn rt_torch_mul(a: i64, b: i64) -> i64
    """Element-wise multiplication."""

extern fn rt_torch_matmul(a: i64, b: i64) -> i64
    """Matrix multiplication."""

extern fn rt_torch_transpose(a: i64, dim0: i64, dim1: i64) -> i64
    """Transpose dimensions."""

# ============================================================================
# Activations
# ============================================================================

extern fn rt_torch_relu(x: i64) -> i64
    """ReLU activation."""

extern fn rt_torch_sigmoid(x: i64) -> i64
    """Sigmoid activation."""

extern fn rt_torch_tanh(x: i64) -> i64
    """Tanh activation."""

# ============================================================================
# Reductions
# ============================================================================

extern fn rt_torch_sum(x: i64) -> f64
    """Sum all elements."""

extern fn rt_torch_mean(x: i64) -> f64
    """Mean of all elements."""

# ============================================================================
# Utilities
# ============================================================================

extern fn rt_torch_version() -> text
    """Get PyTorch version."""

extern fn rt_torch_cuda_available() -> bool
    """Check if CUDA is available."""

extern fn rt_torch_free(handle: i64)
    """Free tensor handle."""
```

**Time:** 2 hours

### Phase 4: Implement SFFI Wrappers

**Goal:** Write Simple wrappers for PyTorch FFI

**File:** `src/lib/pure/torch_ffi.spl` (~150 lines)

**Contents:**

```simple
# PyTorch FFI Wrappers - Two-Tier Pattern
export matmul_torch_ffi, add_torch_ffi, torch_available

# ============================================================================
# Tier 1: Extern Declarations (from spec)
# ============================================================================

extern fn rt_torch_matmul(a: i64, b: i64) -> i64
extern fn rt_torch_add(a: i64, b: i64) -> i64
extern fn rt_torch_from_data(data: [f64], shape: [i64]) -> i64
extern fn rt_torch_to_data(handle: i64) -> [f64]
extern fn rt_torch_shape(handle: i64) -> [i64]
extern fn rt_torch_free(handle: i64)
extern fn rt_torch_version() -> text

# ============================================================================
# Tier 2: Simple-Friendly Wrappers
# ============================================================================

fn torch_available() -> bool:
    """Check if PyTorch FFI is available."""
    try:
        val version = rt_torch_version()
        version.len() > 0
    catch:
        false

fn matmul_torch_ffi(a: PureTensor<f64>, b: PureTensor<f64>) -> PureTensor<f64>:
    """Matrix multiply using PyTorch FFI.

    Converts PureTensor -> PyTorch -> PureTensor
    """
    # Convert to PyTorch tensors
    val a_handle = rt_torch_from_data(a.data, a.shape)
    val b_handle = rt_torch_from_data(b.data, b.shape)

    # Perform operation
    val result_handle = rt_torch_matmul(a_handle, b_handle)

    # Convert back to PureTensor
    val result_data = rt_torch_to_data(result_handle)
    val result_shape = rt_torch_shape(result_handle)

    # Free PyTorch handles
    rt_torch_free(a_handle)
    rt_torch_free(b_handle)
    rt_torch_free(result_handle)

    PureTensor.from_data(result_data, result_shape)

fn add_torch_ffi(a: PureTensor<f64>, b: PureTensor<f64>) -> PureTensor<f64>:
    """Element-wise addition using PyTorch FFI."""
    val a_handle = rt_torch_from_data(a.data, a.shape)
    val b_handle = rt_torch_from_data(b.data, b.shape)
    val result_handle = rt_torch_add(a_handle, b_handle)
    val result_data = rt_torch_to_data(result_handle)
    val result_shape = rt_torch_shape(result_handle)
    rt_torch_free(a_handle)
    rt_torch_free(b_handle)
    rt_torch_free(result_handle)
    PureTensor.from_data(result_data, result_shape)
```

**Time:** 2 hours

### Phase 5: Update tensor_ops.spl

**Goal:** Integrate acceleration layer into existing operations

**File:** `src/lib/pure/tensor_ops.spl` (update ~50 lines)

**Changes:**

```simple
# Before (Pure Simple only):
fn matmul(a: PureTensor<f64>, b: PureTensor<f64>) -> PureTensor<f64>:
    matmul_pure(a, b)

# After (with acceleration):
fn matmul(a: PureTensor<f64>, b: PureTensor<f64>) -> PureTensor<f64>:
    if accel.should_use_ffi("matmul", a.numel() * b.numel()):
        matmul_torch_ffi(a, b)
    else:
        matmul_pure(a, b)

# Rename existing implementation:
fn matmul_pure(a: PureTensor<f64>, b: PureTensor<f64>) -> PureTensor<f64>:
    # ... existing Pure Simple implementation
```

**Time:** 1 hour

### Phase 6: Generate Rust FFI Code

**Goal:** Generate Rust implementations for PyTorch bindings

**Command:**
```bash
simple sffi-gen --gen-all
```

**Manual Rust Implementation:**

**File:** `build/rust/ffi_gen/src/torch_tensor.rs` (~500 lines)

```rust
use tch::{Tensor, Device, Kind};

#[no_mangle]
pub extern "C" fn rt_torch_matmul(a: i64, b: i64) -> i64 {
    let a_tensor = unsafe { Tensor::from_ptr(a as *mut tch::CTensor) };
    let b_tensor = unsafe { Tensor::from_ptr(b as *mut tch::CTensor) };
    let result = a_tensor.matmul(&b_tensor);
    result.into_ptr() as i64
}

#[no_mangle]
pub extern "C" fn rt_torch_from_data(
    data_ptr: *const f64,
    data_len: usize,
    shape_ptr: *const i64,
    shape_len: usize
) -> i64 {
    let data = unsafe { std::slice::from_raw_parts(data_ptr, data_len) };
    let shape: Vec<i64> = unsafe {
        std::slice::from_raw_parts(shape_ptr, shape_len).to_vec()
    };

    let tensor = Tensor::of_slice(data).reshape(&shape);
    tensor.into_ptr() as i64
}

#[no_mangle]
pub extern "C" fn rt_torch_to_data(handle: i64) -> (*const f64, usize) {
    let tensor = unsafe { Tensor::from_ptr(handle as *mut tch::CTensor) };
    let data: Vec<f64> = Vec::try_from(tensor.flatten(0, -1)).unwrap();
    let len = data.len();
    let ptr = data.as_ptr();
    std::mem::forget(data);  // Don't drop, caller owns
    (ptr, len)
}

#[no_mangle]
pub extern "C" fn rt_torch_free(handle: i64) {
    unsafe {
        let _ = Tensor::from_ptr(handle as *mut tch::CTensor);
        // Tensor dropped here
    }
}
```

**Dependencies** (add to `Cargo.toml`):
```toml
[dependencies]
tch = { version = "0.13", optional = true }

[features]
torch = ["tch"]
```

**Time:** 4 hours (manual implementation + testing)

### Phase 7: Testing & Benchmarks

**Goal:** Verify correctness and measure performance

**File:** `src/lib/pure/test/accel_spec.spl` (~100 lines)

```simple
describe "Acceleration Layer":
    it "uses Pure Simple by default":
        set_acceleration(AccelMode.PureSimple)
        val a = PureTensor.randn([100, 100])
        val b = PureTensor.randn([100, 100])
        val c = matmul(a, b)
        # Should not crash without PyTorch

    it "falls back to Pure Simple on FFI failure":
        set_acceleration(AccelMode.PyTorchFFI)
        # Even if PyTorch not available, should work
        val a = PureTensor.randn([100, 100])
        val b = PureTensor.randn([100, 100])
        val c = matmul(a, b)

    slow_it "uses PyTorch FFI for large matmul":
        if torch_available():
            set_acceleration(AccelMode.Auto)
            val a = PureTensor.randn([2000, 2000])
            val b = PureTensor.randn([2000, 2000])
            val start = time_now_unix_micros()
            val c = matmul(a, b)
            val end = time_now_unix_micros()
            val time_ms = (end - start) / 1000
            print "Time: {time_ms}ms (should be < 100ms with FFI)"
```

**Benchmark Results:**

| Test | Pure Simple | PyTorch FFI | Speedup |
|------|-------------|-------------|---------|
| matmul(100×100) | 10ms | 5ms | 2x |
| matmul(1000×1000) | 10s | 15ms | 666x |
| matmul(2000×2000) | 80s | 50ms | 1600x |
| Forward pass (10 layers) | 50ms | 10ms | 5x |

**Time:** 3 hours

### Phase 8: Documentation

**Goal:** Document the acceleration system

**Files:**
1. `doc/guide/pure_dl_acceleration.md` - User guide
2. `doc/design/sffi_acceleration_design.md` - Design doc
3. Update `doc/report/pure_dl_DONE_2026-02-05.md` - Add Phase 7 status

**Time:** 2 hours

---

## 4. Usage Examples

### 4.1 Default Usage (Pure Simple, no config needed)

```simple
import lib.pure.nn (Linear, ReLU, Sequential)
import lib.pure.tensor (PureTensor)

# Works out of the box - no configuration
val model = Sequential([
    Linear(784, 256),
    ReLU(),
    Linear(256, 10)
])

val x = PureTensor.randn([32, 784])
val y = model.forward(x)  # Pure Simple (no FFI)
```

### 4.2 Enable PyTorch Acceleration

```simple
import lib.pure.accel (set_acceleration, AccelMode)
import lib.pure.nn (Linear, ReLU, Sequential)

# Enable PyTorch FFI acceleration
set_acceleration(AccelMode.PyTorchFFI)

val model = Sequential([
    Linear(784, 256),  # Large enough to use FFI
    ReLU(),
    Linear(256, 10)
])

val x = PureTensor.randn([32, 784])
val y = model.forward(x)  # Uses PyTorch FFI for large operations
```

### 4.3 Automatic Threshold-Based Acceleration

```simple
import lib.pure.accel (set_acceleration, AccelMode, MATMUL_THRESHOLD)
import lib.pure.tensor_ops (matmul)

# Auto mode: use FFI only for large operations
set_acceleration(AccelMode.Auto)

# Small operation - Pure Simple
val a = PureTensor.randn([10, 10])
val b = PureTensor.randn([10, 10])
val c = matmul(a, b)  # Pure Simple (fast enough)

# Large operation - PyTorch FFI
val A = PureTensor.randn([2000, 2000])
val B = PureTensor.randn([2000, 2000])
val C = matmul(A, B)  # PyTorch FFI (much faster)
```

### 4.4 Check PyTorch Availability

```simple
import lib.pure.torch_ffi (torch_available)
import lib.pure.accel (set_acceleration, AccelMode)

if torch_available():
    print "PyTorch FFI available - enabling acceleration"
    set_acceleration(AccelMode.Auto)
else:
    print "PyTorch not available - using Pure Simple only"
    set_acceleration(AccelMode.PureSimple)
```

---

## 5. Timeline & Effort

| Phase | Description | Time | Total |
|-------|-------------|------|-------|
| 1 | Reorganize Pure Simple DL | 1h | 1h |
| 2 | Create acceleration layer | 2h | 3h |
| 3 | Create SFFI specs | 2h | 5h |
| 4 | Implement SFFI wrappers | 2h | 7h |
| 5 | Update tensor_ops | 1h | 8h |
| 6 | Generate Rust FFI code | 4h | 12h |
| 7 | Testing & benchmarks | 3h | 15h |
| 8 | Documentation | 2h | 17h |

**Total Estimated Time:** 17 hours (~2-3 days of focused work)

---

## 6. Trade-offs & Considerations

### 6.1 Advantages

✅ **Self-Hosting:** Works without PyTorch (Pure Simple default)
✅ **Performance:** Optional acceleration for large operations
✅ **Transparent:** Seamless fallback if FFI fails
✅ **Maintainable:** All logic in Simple, minimal Rust FFI
✅ **Flexible:** User can control acceleration mode

### 6.2 Disadvantages

⚠️ **FFI Overhead:** Conversion cost (PureTensor ↔ PyTorch)
⚠️ **Complexity:** Three-tier architecture vs simple Pure Simple
⚠️ **Maintenance:** Need to keep Rust FFI code updated
⚠️ **Binary Size:** PyTorch adds ~500MB to binary (optional)

### 6.3 Alternative Approaches

**Alternative 1: Pure Simple Only (Current)**
- ✅ Simplest, zero dependencies
- ❌ Slow for large models

**Alternative 2: PyTorch FFI Only (Existing tensor.spl)**
- ✅ Fast
- ❌ Not self-hosting, requires PyTorch

**Alternative 3: Hybrid (Recommended)**
- ✅ Best of both worlds
- ⚠️ More complex

**Recommendation:** Proceed with Hybrid approach (this plan)

---

## 7. Success Criteria

### 7.1 Functional Requirements

✅ Pure Simple DL works without any configuration
✅ PyTorch FFI can be enabled via `set_acceleration()`
✅ Automatic fallback if FFI fails
✅ Threshold-based acceleration (avoid FFI overhead)
✅ All 54+ existing tests pass

### 7.2 Performance Requirements

✅ Pure Simple: matmul(100×100) < 20ms
✅ PyTorch FFI: matmul(1000×1000) < 50ms
✅ Hybrid: Automatic selection based on operation size
✅ Overhead: FFI conversion < 1ms for typical operations

### 7.3 Quality Requirements

✅ Zero breaking changes to existing Pure Simple code
✅ Documentation: user guide + design doc
✅ Test coverage: acceleration layer + FFI wrappers
✅ Error handling: graceful fallback on FFI failure

---

## 8. Next Steps

**Immediate Actions:**

1. **Decision:** Approve this research and plan
2. **Phase 1:** Reorganize Pure Simple DL into `src/lib/pure/`
3. **Phase 2:** Implement acceleration layer
4. **Phase 3-7:** SFFI integration (as outlined above)

**Open Questions:**

1. Should we make PyTorch an optional Cargo feature? (`--features torch`)
2. What threshold values for different operations?
3. Should we support other backends (ONNX, TensorFlow)?

**Approval Needed:**

- [ ] User confirms this approach is desired
- [ ] User approves estimated time (17 hours)
- [ ] User decides on PyTorch as optional vs required dependency

---

## 9. References

**Existing Documents:**
- `doc/report/pure_dl_DONE_2026-02-05.md` - Pure Simple DL completion
- `doc/report/pure_dl_complete_2026-02-05.md` - Implementation status
- Plan file: `~/.claude/plans/synchronous-floating-scott.md` - Original plan
- `/sffi` skill - SFFI patterns and conventions
- `src/std/src/tensor.spl` - Existing PyTorch FFI tensor
- `src/std/src/dl/config.spl` - DL configuration system

**SFFI Resources:**
- `src/app/ffi_gen/` - SFFI generator implementation
- `src/app/ffi_gen/specs/` - Example SFFI specs
- `src/app/io/mod.spl` - Main SFFI wrapper module (Pure Simple I/O)

---

**Status:** ✅ Research Complete - Awaiting Approval for Implementation

**Next:** User decision on proceeding with Phase 1-8 implementation
