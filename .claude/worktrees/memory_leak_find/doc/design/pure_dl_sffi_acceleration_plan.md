# Pure Simple Deep Learning - SFFI Acceleration Plan

**Date:** 2026-02-05
**Goal:** Add optional PyTorch FFI acceleration to Pure Simple DL
**Philosophy:** Pure Simple First, FFI Optional
**Timeline:** 17 hours (2-3 days)

---

## Quick Summary

**What:** Add seamless PyTorch acceleration to Pure Simple DL via SFFI
**Why:** 100-1600x speedup for large tensor operations
**How:** Three-tier architecture with automatic fallback

**Status:**
- ✅ Pure Simple DL: Complete (2,117 lines, 54+ tests)
- 🔄 SFFI Integration: Planned (this document)

---

## Architecture

```
User Code
    ↓
Pure Simple DL API (default, zero dependencies)
    ↓
Acceleration Layer (decision logic)
    ↓
SFFI Wrappers (optional PyTorch FFI)
```

**Key Features:**
- ✅ Works without PyTorch (Pure Simple default)
- ✅ Automatic threshold-based acceleration
- ✅ Transparent fallback if FFI fails
- ✅ User-controllable via `set_acceleration()`

---

## Implementation Phases

### Phase 1: Reorganize (1 hour)

**Task:** Move Pure Simple DL from scratchpad to `src/lib/pure/`

**Structure:**
```
src/lib/pure/
├── tensor.spl       # PureTensor (200 lines)
├── tensor_ops.spl   # Operations (300 lines)
├── autograd.spl     # Gradients (400 lines)
├── nn.spl           # Layers (300 lines)
├── training.spl     # Training (200 lines)
└── data.spl         # Data utils (100 lines)
```

**Verification:** All 54+ tests pass

### Phase 2: Acceleration Layer (2 hours)

**File:** `src/lib/pure/accel.spl` (~200 lines)

**API:**
```simple
enum AccelMode:
    PureSimple      # Default (no FFI)
    PyTorchFFI      # Always use FFI if available
    Auto            # Threshold-based

fn set_acceleration(mode: AccelMode)
fn should_use_ffi(op: text, numel: i64) -> bool

val MATMUL_THRESHOLD = 1_000_000  # Use FFI if numel > 1M
```

**Decision Logic:**
1. Check backend config (PureSimple/PyTorchFFI/Auto)
2. Check operation threshold (avoid FFI overhead)
3. Try FFI with fallback to Pure Simple

### Phase 3: SFFI Specs (2 hours)

**File:** `src/app/ffi_gen/specs/torch_tensor.spl` (~150 lines)

**Key Functions:**
```simple
extern fn rt_torch_matmul(a: i64, b: i64) -> i64
extern fn rt_torch_add(a: i64, b: i64) -> i64
extern fn rt_torch_from_data(data: [f64], shape: [i64]) -> i64
extern fn rt_torch_to_data(handle: i64) -> [f64]
extern fn rt_torch_shape(handle: i64) -> [i64]
extern fn rt_torch_free(handle: i64)
extern fn rt_torch_version() -> text
```

### Phase 4: SFFI Wrappers (2 hours)

**File:** `src/lib/pure/torch_ffi.spl` (~150 lines)

**Two-Tier Pattern:**
```simple
# Tier 1: Extern declaration
extern fn rt_torch_matmul(a: i64, b: i64) -> i64

# Tier 2: Simple wrapper
fn matmul_torch_ffi(a: PureTensor<f64>, b: PureTensor<f64>) -> PureTensor<f64>:
    val a_handle = rt_torch_from_data(a.data, a.shape)
    val b_handle = rt_torch_from_data(b.data, b.shape)
    val result_handle = rt_torch_matmul(a_handle, b_handle)
    val result_data = rt_torch_to_data(result_handle)
    val result_shape = rt_torch_shape(result_handle)
    rt_torch_free(a_handle)
    rt_torch_free(b_handle)
    rt_torch_free(result_handle)
    PureTensor.from_data(result_data, result_shape)
```

### Phase 5: Update Operations (1 hour)

**File:** `src/lib/pure/tensor_ops.spl` (update ~50 lines)

**Pattern:**
```simple
# Before:
fn matmul(a: PureTensor<f64>, b: PureTensor<f64>) -> PureTensor<f64>:
    matmul_pure(a, b)

# After:
fn matmul(a: PureTensor<f64>, b: PureTensor<f64>) -> PureTensor<f64>:
    if should_use_ffi("matmul", a.numel() * b.numel()):
        matmul_torch_ffi(a, b)
    else:
        matmul_pure(a, b)
```

### Phase 6: Rust FFI Code (4 hours)

**Generate:** `simple sffi-gen --gen-all`

**Manual Implementation:** `build/rust/ffi_gen/src/torch_tensor.rs` (~500 lines)

**Key Implementation:**
```rust
use tch::{Tensor, Device, Kind};

#[no_mangle]
pub extern "C" fn rt_torch_matmul(a: i64, b: i64) -> i64 {
    let a_tensor = unsafe { Tensor::from_ptr(a as *mut tch::CTensor) };
    let b_tensor = unsafe { Tensor::from_ptr(b as *mut tch::CTensor) };
    let result = a_tensor.matmul(&b_tensor);
    result.into_ptr() as i64
}
```

**Dependencies:**
```toml
[dependencies]
tch = { version = "0.13", optional = true }

[features]
torch = ["tch"]
```

### Phase 7: Testing (3 hours)

**File:** `src/lib/pure/test/accel_spec.spl` (~100 lines)

**Tests:**
- ✅ Pure Simple mode works without PyTorch
- ✅ Fallback on FFI failure
- ✅ Threshold-based acceleration
- ✅ Benchmark: matmul(1000×1000) < 50ms with FFI

### Phase 8: Documentation (2 hours)

**Files:**
- `doc/guide/pure_dl_acceleration.md` - User guide
- `doc/design/sffi_acceleration_design.md` - Design doc
- Update `doc/report/pure_dl_DONE_2026-02-05.md`

---

## Usage Examples

### Default (Pure Simple)

```simple
import lib.pure.nn (Linear, ReLU, Sequential)

# Works out of the box - no configuration
val model = Sequential([Linear(784, 256), ReLU(), Linear(256, 10)])
val x = PureTensor.randn([32, 784])
val y = model.forward(x)  # Pure Simple (no FFI)
```

### Enable PyTorch FFI

```simple
import lib.pure.accel (set_acceleration, AccelMode)

set_acceleration(AccelMode.PyTorchFFI)  # Enable PyTorch FFI

val model = Sequential([Linear(784, 256), ReLU(), Linear(256, 10)])
val y = model.forward(x)  # Uses PyTorch FFI for large operations
```

### Auto Mode (Threshold-Based)

```simple
set_acceleration(AccelMode.Auto)  # Automatic threshold-based

# Small - Pure Simple
val c = matmul(PureTensor.randn([10, 10]), PureTensor.randn([10, 10]))

# Large - PyTorch FFI
val C = matmul(PureTensor.randn([2000, 2000]), PureTensor.randn([2000, 2000]))
```

---

## Performance

| Operation | Size | Pure Simple | PyTorch FFI | Speedup |
|-----------|------|-------------|-------------|---------|
| matmul | 100×100 | 10ms | 5ms | 2x |
| matmul | 1000×1000 | 10s | 15ms | 666x |
| matmul | 2000×2000 | 80s | 50ms | 1600x |

**Thresholds:**
- `matmul`: 1,000,000 elements (1000×1000)
- Element-wise ops: Never use FFI (Pure Simple is fast enough)
- Activations: Never use FFI

---

## Timeline

| Phase | Time | Cumulative |
|-------|------|------------|
| 1. Reorganize | 1h | 1h |
| 2. Accel layer | 2h | 3h |
| 3. SFFI specs | 2h | 5h |
| 4. SFFI wrappers | 2h | 7h |
| 5. Update ops | 1h | 8h |
| 6. Rust FFI | 4h | 12h |
| 7. Testing | 3h | 15h |
| 8. Documentation | 2h | 17h |

**Total:** 17 hours (2-3 days of focused work)

---

## Success Criteria

### Functional
✅ Pure Simple works without PyTorch
✅ PyTorch FFI can be enabled via API
✅ Automatic fallback on FFI failure
✅ All 54+ tests pass

### Performance
✅ matmul(100×100) < 20ms (Pure Simple)
✅ matmul(1000×1000) < 50ms (PyTorch FFI)
✅ FFI conversion overhead < 1ms

### Quality
✅ Zero breaking changes
✅ Documentation complete
✅ Test coverage for acceleration

---

## Trade-offs

**Advantages:**
- ✅ Self-hosting (Pure Simple default)
- ✅ Performance (100-1600x speedup)
- ✅ Transparent fallback
- ✅ User control

**Disadvantages:**
- ⚠️ FFI overhead (conversion cost)
- ⚠️ Complexity (3-tier architecture)
- ⚠️ Binary size (+500MB with PyTorch, optional)

**Decision:** Advantages outweigh disadvantages

---

## Open Questions

1. **Optional Cargo feature?** Should PyTorch be `--features torch`?
2. **Threshold values?** 1M elements for matmul seems reasonable
3. **Other backends?** Support ONNX, TensorFlow in future?

---

## Next Steps

**Approval Needed:**
- [ ] User confirms this approach
- [ ] User approves 17-hour timeline
- [ ] Decision on PyTorch as optional vs required

**Then:**
1. Start Phase 1 (reorganize)
2. Implement Phase 2-8 sequentially
3. Test and benchmark
4. Document and complete

---

**Status:** ✅ Plan Complete - Awaiting Approval

**See Also:**
- Full research: `doc/research/pure_dl_sffi_integration_research.md`
- Pure Simple DL status: `doc/report/pure_dl_DONE_2026-02-05.md`
