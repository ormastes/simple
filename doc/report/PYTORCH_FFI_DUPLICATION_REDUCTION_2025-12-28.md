# PyTorch FFI Code Duplication Reduction - Comprehensive Report

**Date:** 2025-12-28
**Status:** ✅ Complete
**Impact:** 484 lines removed (22% reduction)

## Executive Summary

Conducted comprehensive code duplication analysis and reduction across the Simple language codebase. Found that Simple language (.spl) files have no significant duplication (below 2% threshold), while Rust PyTorch FFI wrapper code had substantial duplication ranging from 33% to 145%. Successfully refactored 7 high-duplication files using declarative macros and helper functions, reducing codebase by 484 lines (22% reduction) while maintaining all functionality and FFI safety requirements.

## Duplication Analysis

### Simple Language Files
- **Result:** No significant duplication detected
- **Status:** ✅ Below 2% threshold
- **Conclusion:** Simple language code is well-structured with minimal duplication

### Rust Source Files - Initial Analysis
Identified 7 files with high duplication (>30%):

| File | Duplication % | Lines | Priority |
|------|--------------|-------|----------|
| ops_reduction.rs | 145.83% | 145 | Phase 1 |
| ops_matrix.rs | 119.35% | 93 | Phase 1 |
| modules/rnn.rs | 58.07% | 446 | Phase 1 |
| ops_shape.rs | 52.78% | 218 | Phase 2 |
| optimizer.rs | 50.31% | 799 | Phase 2 |
| ops_elementwise.rs | 36.69% | 279 | Phase 2 |
| ops_comparison.rs | 33.64% | 215 | Phase 2 |

## Refactoring Summary

### Phase 1: Initial High-Priority Files

#### 1. ops_reduction.rs
- **Before:** 145 lines (145.83% duplication)
- **After:** 57 lines
- **Reduction:** 88 lines (-61%)
- **Pattern:** Created `tensor_unary_op!` macro
- **Functions Refactored:** 6 (sum, mean, max, min, argmax, argmin)

**Key Changes:**
```rust
// Before: 24 lines per function
#[no_mangle]
pub extern "C" fn rt_torch_sum(tensor_handle: u64) -> u64 {
    #[cfg(feature = "pytorch")]
    {
        let registry = TENSOR_REGISTRY.lock();
        let Some(tensor) = registry.get(&tensor_handle).cloned() else { return 0; };
        drop(registry);
        let result = tensor.0.sum(tch::Kind::Float);
        let handle = next_handle();
        TENSOR_REGISTRY.lock().insert(handle, Arc::new(TensorWrapper(result)));
        tracing::debug!("rt_torch_sum: {} -> handle={}", tensor_handle, handle);
        handle
    }
    #[cfg(not(feature = "pytorch"))]
    { let _ = tensor_handle; 0 }
}

// After: 1 line per function
tensor_unary_op!(rt_torch_sum, "rt_torch_sum", |t: &Tensor| t.sum(tch::Kind::Float));
```

#### 2. ops_matrix.rs
- **Before:** 93 lines (119.35% duplication)
- **After:** 76 lines
- **Reduction:** 17 lines (-18%)
- **Pattern:** Created `tensor_binary_op!` macro
- **Functions Refactored:** 2 (matmul, bmm)

**Key Changes:**
```rust
// Before: 17 lines per function
// After: 1 line per function
tensor_binary_op!(rt_torch_matmul, "rt_torch_matmul", |a: &Tensor, b: &Tensor| a.matmul(b));
tensor_binary_op!(rt_torch_bmm, "rt_torch_bmm", |a: &Tensor, b: &Tensor| a.bmm(b));
```

#### 3. modules/rnn.rs
- **Before:** 446 lines (58.07% duplication)
- **After:** 401 lines
- **Reduction:** 45 lines (-10%)
- **Pattern:** Helper functions for common initialization logic
- **Functions Created:** 4 helpers (init_rnn_weights, init_rnn_layers, build_rnn_params, get_or_create_hidden_state)

**Key Changes:**
```rust
// Extracted shared initialization logic
fn init_rnn_layers(
    num_gates: i64,
    input_size: i64,
    hidden_size: i64,
    num_layers: i64,
    bidirectional: bool,
) -> Option<Vec<(u64, u64, u64, u64)>>

// Used by both LSTM (4 gates) and GRU (3 gates)
```

### Phase 2: Comprehensive Cleanup

#### 4. ops_shape.rs
- **Before:** 218 lines (52.78% duplication)
- **After:** 196 lines
- **Reduction:** 22 lines (-10%)
- **Patterns:**
  - Created `tensor_unary_i64_op!` macro for operations with single i64 parameter
  - Created `tensor_multi_op!` macro for cat/stack operations
- **Functions Refactored:** 3 (unsqueeze, cat, stack)

**Key Changes:**
```rust
// Single parameter operations
tensor_unary_i64_op!(rt_torch_unsqueeze, "rt_torch_unsqueeze", |t: &Tensor, dim| t.unsqueeze(dim));

// Multi-tensor operations
tensor_multi_op!(rt_torch_cat, "rt_torch_cat", |tensors: &Vec<&Tensor>, dim| Tensor::cat(tensors, dim));
tensor_multi_op!(rt_torch_stack, "rt_torch_stack", |tensors: &Vec<&Tensor>, dim| Tensor::stack(tensors, dim));
```

#### 5. optimizer.rs
- **Before:** 799 lines (50.31% duplication)
- **After:** 774 lines
- **Reduction:** 25 lines (-3%)
- **Pattern:** Helper function for optimizer creation
- **Functions Refactored:** 3 constructors (SGD, Adam, AdamW)

**Key Changes:**
```rust
// Extracted common validation and registration logic
fn create_optimizer<F>(
    params_ptr: *const u64,
    num_params: usize,
    lr: f64,
    create_type: F,
) -> u64
where F: FnOnce(usize) -> OptimizerType

// Simplified constructors
pub extern "C" fn rt_torch_sgd_new(...) -> u64 {
    let handle = create_optimizer(params_ptr, num_params, lr, |n| {
        OptimizerType::SGD { momentum, weight_decay, velocity: vec![None; n] }
    });
}
```

#### 6. ops_elementwise.rs
- **Before:** 279 lines (36.69% duplication)
- **After:** 138 lines
- **Reduction:** 141 lines (-50.5%)
- **Patterns:**
  - Created `tensor_binary_op!` macro for element-wise binary operations
  - Created `tensor_scalar_op!` macro for scalar operations
  - Created `tensor_unary_op!` macro for unary operations
- **Functions Refactored:** 12 (add, sub, mul, div, add_scalar, sub_scalar, mul_scalar, div_scalar, pow, sqrt, exp, log)

**Key Changes:**
```rust
// Binary operations (tensor + tensor)
tensor_binary_op!(rt_torch_add, |a: &Tensor, b: &Tensor| a + b);
tensor_binary_op!(rt_torch_sub, |a: &Tensor, b: &Tensor| a - b);

// Scalar operations (tensor + scalar)
tensor_scalar_op!(rt_torch_add_scalar, |t: &Tensor, s| t + s);
tensor_scalar_op!(rt_torch_mul_scalar, |t: &Tensor, s| t * s);

// Unary operations
tensor_unary_op!(rt_torch_sqrt, |t: &Tensor| t.sqrt());
tensor_unary_op!(rt_torch_exp, |t: &Tensor| t.exp());
```

#### 7. ops_comparison.rs
- **Before:** 215 lines (33.64% duplication)
- **After:** 69 lines
- **Reduction:** 146 lines (-68%)
- **Pattern:** Created `tensor_comparison_op!` macro
- **Functions Refactored:** 6 (eq, ne, gt, lt, ge, le)

**Key Changes:**
```rust
// Before: ~35 lines per function
// After: 1 line per function
tensor_comparison_op!(rt_torch_eq, "==", |a: &Tensor, b: &Tensor| a.eq_tensor(b));
tensor_comparison_op!(rt_torch_ne, "!=", |a: &Tensor, b: &Tensor| a.ne_tensor(b));
tensor_comparison_op!(rt_torch_gt, ">", |a: &Tensor, b: &Tensor| a.gt_tensor(b));
tensor_comparison_op!(rt_torch_lt, "<", |a: &Tensor, b: &Tensor| a.lt_tensor(b));
tensor_comparison_op!(rt_torch_ge, ">=", |a: &Tensor, b: &Tensor| a.ge_tensor(b));
tensor_comparison_op!(rt_torch_le, "<=", |a: &Tensor, b: &Tensor| a.le_tensor(b));
```

## Total Impact

### Overall Statistics
```
File                    Before  After   Reduction  Percentage
ops_reduction.rs        145     57      -88        -61%
ops_matrix.rs           93      76      -17        -18%
modules/rnn.rs          446     401     -45        -10%
ops_shape.rs            218     196     -22        -10%
optimizer.rs            799     774     -25        -3%
ops_elementwise.rs      279     138     -141       -50.5%
ops_comparison.rs       215     69      -146       -68%
─────────────────────────────────────────────────────────
TOTAL                   2195    1711    -484       -22%
```

### Files Modified
- 7 PyTorch FFI wrapper files in `src/runtime/src/value/torch/`
- All changes maintain FFI safety (#[no_mangle], extern "C")
- All changes preserve feature gates (#[cfg(feature = "pytorch")])
- No functionality changes - pure refactoring

## Refactoring Patterns Used

### 1. Declarative Macros
Most effective pattern for FFI functions with identical structure but different operations.

**Benefits:**
- Eliminated 90% of boilerplate code
- Consistent error handling
- Automatic debug logging
- Type-safe closures

**Usage:**
- `tensor_unary_op!` - Single tensor operations
- `tensor_binary_op!` - Two tensor operations
- `tensor_scalar_op!` - Tensor + scalar operations
- `tensor_comparison_op!` - Comparison operations
- `tensor_unary_i64_op!` - Single tensor + i64 parameter
- `tensor_multi_op!` - Multi-tensor operations (cat, stack)

### 2. Helper Functions
Used for complex initialization logic with shared patterns.

**Benefits:**
- Extracted common validation
- Reduced cognitive load
- Maintained readability

**Usage:**
- Optimizer creation and registration
- RNN weight initialization
- Hidden state management

## Verification

### Build Status
```bash
cargo build -p simple-runtime --lib
# Result: ✅ Success (Finished `dev` profile in 0.28s)
# Warnings: Pre-existing FFI warnings (not from refactoring)
```

### Test Status
```bash
cargo test -p simple-runtime --lib
# Result: ✅ All 154 tests passing
# No regressions introduced
```

## Lessons Learned

### What Worked Well
1. **Macro-first approach:** Declarative macros eliminated 60-68% of duplication in heavily duplicated files
2. **Incremental refactoring:** Phase 1 (highest duplication) → Phase 2 (remaining files)
3. **Closure-based abstraction:** Allowed operation-specific logic while maintaining common structure
4. **Consistent verification:** Build + test after each file ensured no regressions

### Challenges
1. **Optimizer.rs low reduction (3%):** Complex state management and different initialization logic limited macro applicability
2. **modules/rnn.rs moderate reduction (10%):** LSTM vs GRU differences required careful helper function design

### Best Practices
1. Use macros for purely structural duplication (FFI boilerplate)
2. Use helper functions for semantic duplication (initialization logic)
3. Always preserve FFI safety attributes in macro expansions
4. Keep operation-specific logic in closures for clarity
5. Maintain debug logging in macros for observability

## Recommendations

### Immediate
- ✅ All high-priority duplication addressed
- ✅ Build and tests verified
- ✅ Documentation updated

### Future Improvements
1. **Consider extracting macro definitions:** Move common macros to a shared `torch/macros.rs` module
2. **Monitor for new patterns:** As more PyTorch operations are added, watch for new duplication patterns
3. **Apply to other modules:** Consider similar refactoring for other runtime FFI modules if duplication emerges

### Maintenance
- Run `make duplication` periodically to catch new duplication
- Keep threshold at 2% to maintain code quality
- Document macro patterns for future contributors

## References

- Duplication detection: `.jscpd.json` (2% threshold, 5 minLines, 50 minTokens)
- Build command: `make check` (fmt + lint + test)
- Coverage command: `make coverage-all`
- Related report: `doc/report/CODE_DUPLICATION_REFACTORING_2025-12-28.md`

## Conclusion

Successfully reduced code duplication by 484 lines (22%) across 7 PyTorch FFI wrapper files. All functionality preserved, no regressions introduced, and code maintainability significantly improved. Simple language files confirmed to have excellent code structure with no significant duplication.

The refactoring establishes clear patterns for future PyTorch FFI development:
- Use declarative macros for FFI boilerplate
- Use helper functions for complex initialization
- Maintain FFI safety and feature gates
- Verify changes with comprehensive testing

**Status:** ✅ Complete - Ready for production
