# Simple Language API Consistency Report

**Generated:** 2026-01-25

## Executive Summary

| Category | Count | Short Forms | Status |
|----------|-------|-------------|--------|
| **Slicing/Indexing** | 3 syntax types | `[:]`, `[::-1]`, `[-1]` | ✅ Consistent |
| **Math Module** | 33 functions | N/A | ✅ Complete |
| **Torch Module** | ~98 functions | N/A | ✅ Consistent |
| **Collections** | 35+ functions | N/A | ✅ Complete |

---

## 1. Short Form Grammar Support

### Slicing Syntax (Python-like)

| Syntax | Meaning | Status |
|--------|---------|--------|
| `arr[i]` | Single index | ✅ Implemented |
| `arr[-1]` | Last element | ✅ Implemented |
| `arr[-n]` | n-th from end | ✅ Implemented |
| `arr[a:b]` | Slice from a to b | ✅ Implemented |
| `arr[:b]` | First b elements | ✅ Implemented |
| `arr[a:]` | From a to end | ✅ Implemented |
| `arr[:]` | Full copy | ✅ Implemented |
| `arr[::n]` | Every n-th element | ✅ Implemented |
| `arr[::-1]` | Reversed (arrays) | ✅ Implemented |
| `str[::-1]` | Reversed (strings) | ❌ Not implemented (step=1 only) |

### Other Short Forms

| Syntax | Meaning | Status |
|--------|---------|--------|
| `0..10` | Exclusive range | ✅ Implemented |
| `0..=10` | Inclusive range | ✅ Implemented |
| `obj?.field` | Optional chaining | ✅ Implemented |
| `x ?? default` | Null coalescing | ✅ Implemented |
| `opt.?` | Existence check | ✅ Implemented |
| `\x: expr` | Lambda | ✅ Implemented |

---

## 2. Math Module API (33 Functions)

**Location:** `src/rust/runtime/src/value/ffi/math.rs`

### Power & Roots
| Function | Signature | Description |
|----------|-----------|-------------|
| `rt_math_pow` | `(f64, f64) -> f64` | Power: x^y |
| `rt_math_sqrt` | `(f64) -> f64` | Square root |
| `rt_math_cbrt` | `(f64) -> f64` | Cube root |
| `rt_math_exp` | `(f64) -> f64` | Exponential e^x |

### Logarithms
| Function | Signature | Description |
|----------|-----------|-------------|
| `rt_math_log` | `(f64) -> f64` | Natural log (ln) |
| `rt_math_log10` | `(f64) -> f64` | Base-10 log |
| `rt_math_log2` | `(f64) -> f64` | Base-2 log |

### Trigonometry
| Function | Signature | Description |
|----------|-----------|-------------|
| `rt_math_sin` | `(f64) -> f64` | Sine |
| `rt_math_cos` | `(f64) -> f64` | Cosine |
| `rt_math_tan` | `(f64) -> f64` | Tangent |
| `rt_math_asin` | `(f64) -> f64` | Arcsine |
| `rt_math_acos` | `(f64) -> f64` | Arccosine |
| `rt_math_atan` | `(f64) -> f64` | Arctangent |
| `rt_math_atan2` | `(f64, f64) -> f64` | Two-argument arctangent |

### Hyperbolic
| Function | Signature | Description |
|----------|-----------|-------------|
| `rt_math_sinh` | `(f64) -> f64` | Hyperbolic sine |
| `rt_math_cosh` | `(f64) -> f64` | Hyperbolic cosine |
| `rt_math_tanh` | `(f64) -> f64` | Hyperbolic tangent |

### Rounding
| Function | Signature | Description |
|----------|-----------|-------------|
| `rt_math_floor` | `(f64) -> f64` | Round down |
| `rt_math_ceil` | `(f64) -> f64` | Round up |
| `rt_math_round` | `(f64) -> f64` | Round to nearest |
| `rt_math_trunc` | `(f64) -> f64` | Truncate toward zero |

### Basic Operations (NEW)
| Function | Signature | Description |
|----------|-----------|-------------|
| `rt_math_abs` | `(f64) -> f64` | Absolute value |
| `rt_math_hypot` | `(f64, f64) -> f64` | Hypotenuse sqrt(x²+y²) |
| `rt_math_gcd` | `(i64, i64) -> i64` | Greatest common divisor |
| `rt_math_lcm` | `(i64, i64) -> i64` | Least common multiple |
| `rt_math_min` | `(f64, f64) -> f64` | Minimum of two values |
| `rt_math_max` | `(f64, f64) -> f64` | Maximum of two values |
| `rt_math_clamp` | `(f64, f64, f64) -> f64` | Clamp to range |
| `rt_math_sign` | `(f64) -> f64` | Sign function (-1, 0, 1) |
| `rt_math_fract` | `(f64) -> f64` | Fractional part |
| `rt_math_rem` | `(f64, f64) -> f64` | Remainder/modulo |

### Special Values
| Function | Signature | Description |
|----------|-----------|-------------|
| `rt_math_nan` | `() -> f64` | Return NaN |
| `rt_math_inf` | `() -> f64` | Return infinity |
| `rt_math_is_nan` | `(f64) -> bool` | Check NaN |
| `rt_math_is_inf` | `(f64) -> bool` | Check infinity |
| `rt_math_is_finite` | `(f64) -> bool` | Check finite |

---

## 3. Torch Module API (~98 Functions)

**Location:** `src/rust/runtime/src/value/torch/`

### Tensor Creation (18 functions)
| Function | Description |
|----------|-------------|
| `rt_torch_zeros` | Create zero tensor |
| `rt_torch_ones` | Create ones tensor |
| `rt_torch_randn` | Random normal tensor |
| `rt_torch_arange` | Range tensor |
| `rt_torch_tensor` | From data array |
| `rt_torch_zeros_1d/2d/3d` | Dimension-specific zeros |
| `rt_torch_ones_1d/2d/3d` | Dimension-specific ones |
| `rt_torch_randn_1d/2d/3d` | Dimension-specific random |

### Element-wise Math (13 functions)
| Function | Description |
|----------|-------------|
| `rt_torch_add/sub/mul/div` | Binary operations |
| `rt_torch_add_scalar/sub_scalar/mul_scalar/div_scalar` | Scalar operations |
| `rt_torch_sqrt/exp/log/pow` | Math functions |
| `rt_torch_clamp` | Clamp to range |

### Matrix Operations (6 functions)
| Function | Description |
|----------|-------------|
| `rt_torch_matmul` | Matrix multiplication |
| `rt_torch_bmm` | Batch matrix multiplication |
| `rt_torch_transpose` | Transpose dimensions |
| `rt_torch_linalg_det` | Determinant |
| `rt_torch_linalg_inv` | Matrix inverse |
| `rt_torch_linalg_solve` | Linear solve Ax=b |

### Shape Operations (8 functions)
| Function | Description |
|----------|-------------|
| `rt_torch_slice` | **Slice with step support** |
| `rt_torch_reshape` | Reshape tensor |
| `rt_torch_permute` | Permute dimensions |
| `rt_torch_squeeze/unsqueeze` | Add/remove dims |
| `rt_torch_cat/stack` | Concatenate tensors |
| `rt_torch_one_hot` | One-hot encoding |

### Reductions (6 functions)
| Function | Description |
|----------|-------------|
| `rt_torch_sum` | Sum all elements |
| `rt_torch_mean` | Mean of elements |
| `rt_torch_max/min` | Maximum/minimum value |
| `rt_torch_argmax/argmin` | Index of max/min |

### Comparisons (8 functions)
| Function | Description |
|----------|-------------|
| `rt_torch_eq/ne` | Equal/not equal |
| `rt_torch_gt/lt` | Greater/less than |
| `rt_torch_ge/le` | Greater/less or equal |
| `rt_torch_where` | Conditional selection |
| `rt_torch_allclose` | Approximate equality |

### Activations (11 functions)
| Function | Description |
|----------|-------------|
| `rt_torch_relu/sigmoid/tanh` | Classic activations |
| `rt_torch_gelu/elu/silu/mish` | Modern activations |
| `rt_torch_leaky_relu/softplus` | Variants |
| `rt_torch_softmax/log_softmax` | Probability functions |

### Loss Functions (3 functions)
| Function | Description |
|----------|-------------|
| `rt_torch_mse_loss` | Mean squared error |
| `rt_torch_cross_entropy` | Cross entropy loss |
| `rt_torch_nll_loss` | Negative log likelihood |

### Normalization (3 functions)
| Function | Description |
|----------|-------------|
| `rt_torch_batch_norm2d_forward` | Batch normalization |
| `rt_torch_layer_norm` | Layer normalization |
| `rt_torch_dropout` | Dropout regularization |

### Initialization (4 functions)
| Function | Description |
|----------|-------------|
| `rt_torch_normal_` | Normal distribution init |
| `rt_torch_uniform_` | Uniform distribution init |
| `rt_torch_xavier_uniform_` | Xavier/Glorot init |
| `rt_torch_kaiming_uniform_` | Kaiming/He init |

### Autograd (11 functions)
| Function | Description |
|----------|-------------|
| `rt_torch_backward` | Backpropagation |
| `rt_torch_set_requires_grad` | Enable gradients |
| `rt_torch_requires_grad` | Check gradient status |
| `rt_torch_grad/zero_grad` | Access/clear gradients |
| `rt_torch_retain_grad` | Retain non-leaf gradients |
| `rt_torch_detach` | Detach from graph |
| `rt_torch_set_grad_enabled` | Toggle gradient mode |
| `rt_torch_is_grad_enabled` | Check gradient mode |
| `rt_torch_shallow_clone` | Clone for gradients |

### Device Operations (3 functions)
| Function | Description |
|----------|-------------|
| `rt_torch_to_device` | Move to device |
| `rt_torch_to_cpu` | Move to CPU |
| `rt_torch_to_cuda` | Move to CUDA |

### FFT (7 functions)
| Function | Description |
|----------|-------------|
| `rt_torch_fft/ifft` | 1D FFT |
| `rt_torch_rfft/irfft` | Real FFT |
| `rt_torch_fftn` | N-D FFT |
| `rt_torch_fftshift/ifftshift` | Shift operations |

### Optimizers (~15 functions)
| Type | Functions |
|------|-----------|
| SGD | `new`, `step`, `zero_grad`, `set_lr`, `get_lr`, `free` |
| Adam | `new`, `step`, `zero_grad`, `set_lr`, `get_lr`, `free` |
| AdamW | `new`, `step`, `zero_grad`, `set_lr`, `get_lr`, `free` |

### Schedulers (~12 functions)
| Type | Description |
|------|-------------|
| Exponential | Exponential decay |
| Cosine | Cosine annealing |
| Plateau | Reduce on plateau |
| StepLR | Step-based decay |

### Neural Network Modules (8 types)
| Module | Description |
|--------|-------------|
| Linear | Fully connected layer |
| Conv2d | 2D convolution |
| BatchNorm2d | Batch normalization |
| LayerNorm | Layer normalization |
| LSTM | LSTM recurrent layer |
| GRU | GRU recurrent layer |
| Dropout | Dropout layer |
| Embedding | Embedding layer |

---

## 4. Collection APIs (35+ Functions)

### Core Array Operations
| Function | Signature | Description |
|----------|-----------|-------------|
| `rt_array_new` | `(i64) -> handle` | Create array |
| `rt_array_len` | `(handle) -> i64` | Get length |
| `rt_array_push` | `(handle, value) -> bool` | Append element |
| `rt_array_pop` | `(handle) -> value` | Remove last |
| `rt_array_get` | `(handle, i64) -> value` | Get by index |
| `rt_array_set` | `(handle, i64, value) -> bool` | Set by index |
| `rt_array_clear` | `(handle) -> void` | Clear all |
| `rt_slice` | `(handle, start, end, step) -> handle` | Slice array |
| `rt_index_get` | `(handle, i64) -> value` | Generic index |
| `rt_index_set` | `(handle, i64, value) -> bool` | Generic set |
| `rt_contains` | `(handle, value) -> bool` | Check membership |

### Array Utility Functions (NEW)
| Function | Signature | Description |
|----------|-----------|-------------|
| `rt_array_first` | `(handle) -> value` | Get first element |
| `rt_array_last` | `(handle) -> value` | Get last element |
| `rt_array_copy` | `(handle) -> handle` | Shallow copy |
| `rt_array_concat` | `(handle, handle) -> handle` | Concatenate arrays |
| `rt_array_reverse` | `(handle) -> bool` | Reverse in place |
| `rt_array_reversed` | `(handle) -> handle` | New reversed array |
| `rt_array_sort` | `(handle) -> bool` | Sort in place (ascending) |
| `rt_array_sorted` | `(handle) -> handle` | New sorted array |
| `rt_array_sort_desc` | `(handle) -> bool` | Sort descending |

### Array Search & Count (NEW)
| Function | Signature | Description |
|----------|-----------|-------------|
| `rt_array_index_of` | `(handle, value) -> i64` | Find first index |
| `rt_array_last_index_of` | `(handle, value) -> i64` | Find last index |
| `rt_array_count` | `(handle, value) -> i64` | Count occurrences |

### Array Aggregation (NEW)
| Function | Signature | Description |
|----------|-----------|-------------|
| `rt_array_sum` | `(handle) -> value` | Sum all elements |
| `rt_array_min` | `(handle) -> value` | Minimum element |
| `rt_array_max` | `(handle) -> value` | Maximum element |
| `rt_array_all_truthy` | `(handle) -> i64` | All elements truthy |
| `rt_array_any_truthy` | `(handle) -> i64` | Any element truthy |

### Array Transformation (NEW)
| Function | Signature | Description |
|----------|-----------|-------------|
| `rt_array_zip` | `(handle, handle) -> handle` | Zip into tuples |
| `rt_array_enumerate` | `(handle) -> handle` | Add indices as tuples |
| `rt_array_flatten` | `(handle) -> handle` | Flatten one level |
| `rt_array_unique` | `(handle) -> handle` | Remove duplicates |
| `rt_array_take` | `(handle, i64) -> handle` | Take first n |
| `rt_array_drop` | `(handle, i64) -> handle` | Drop first n |
| `rt_array_join` | `(handle, str) -> str` | Join with separator |

### Array Creation (NEW)
| Function | Signature | Description |
|----------|-----------|-------------|
| `rt_array_range` | `(start, end, step) -> handle` | Create range array |
| `rt_array_repeat` | `(value, count) -> handle` | Repeat value n times |
| `rt_array_fill` | `(handle, value) -> bool` | Fill with value |

### High-Performance Collections
| Type | Operations |
|------|------------|
| HashMap | `new`, `get`, `set`, `remove`, `keys`, `values`, `items` |
| HashSet | `new`, `add`, `remove`, `contains`, `to_array` |
| BTreeMap | `new`, `get`, `set`, `remove`, `keys`, `values`, `items` |
| BTreeSet | `new`, `add`, `remove`, `contains`, `to_array` |

---

## 5. Consistency Analysis

### ✅ Consistent Areas

1. **Naming Convention:** All FFI functions use `rt_` prefix consistently
2. **Return Types:** Handle-based for complex types, primitives for simple values
3. **Error Handling:** Returns NIL/-1/false for errors consistently
4. **Slicing:** Consistent `start:end:step` pattern across arrays/tensors
5. **Torch API:** Mirrors PyTorch naming closely (`matmul`, `relu`, `backward`)

### ⚠️ Gaps / Inconsistencies

| Area | Issue | Recommendation |
|------|-------|----------------|
| String slicing | Step ≠ 1 not supported | Implement step support |
| String reversal | `[::-1]` returns empty | Implement negative step |
| Tuple slicing | Not supported | Add tuple slice support |
| Higher-order functions | `map/filter/reduce` not in runtime | Add to collection FFI |

---

## 6. Missing APIs (vs Python/NumPy)

### Math Module - ✅ COMPLETE
All essential math functions are now implemented (33 functions).

### Collection Module - ✅ COMPLETE
All essential collection functions are now implemented (35+ functions).

Implemented: `sort`, `sorted`, `reverse`, `reversed`, `zip`, `enumerate`, `first`, `last`,
`index_of`, `concat`, `copy`, `sum`, `min`, `max`, `count`, `flatten`, `unique`,
`take`, `drop`, `join`, `range`, `repeat`, `fill`, `all_truthy`, `any_truthy`.

### Higher-Order Functions (Require Callback Support)
| Function | Status | Notes |
|----------|--------|-------|
| `rt_array_map` | Planned | Requires callback FFI |
| `rt_array_filter` | Planned | Requires callback FFI |
| `rt_array_reduce` | Planned | Requires callback FFI |

Note: Higher-order functions like `map`, `filter`, `reduce` require a callback mechanism
to call back into the interpreter/JIT. These are typically implemented at the language
level using comprehensions or explicit loops rather than FFI.

---

## 7. Summary

The Simple language has **comprehensive and consistent** APIs for:
- **Math operations** (33 functions - complete coverage)
- **Collection operations** (35+ functions - complete coverage)
- **Torch/ML operations** (~98 functions, full deep learning support)
- **Slicing syntax** (Python-like, works for arrays)

**Key Strengths:**
- Consistent `rt_` naming convention
- Full PyTorch FFI integration with autograd, optimizers, schedulers
- Negative indexing support
- Step-based slicing for arrays and tensors
- Complete math library (abs, round, trunc, hypot, gcd, lcm, min, max, clamp, sign, fract, rem)
- Complete collection library (sort, reverse, zip, enumerate, flatten, unique, take, drop, etc.)

**Areas for Improvement:**
- String slicing with step (currently step=1 only)
- Higher-order functions (map/filter/reduce) require language-level implementation

---

## Appendix: File Locations

| Component | Location |
|-----------|----------|
| Math FFI | `src/rust/runtime/src/value/ffi/math.rs` |
| Torch FFI | `src/rust/runtime/src/value/torch/` |
| Collections FFI | `src/rust/runtime/src/value/collections.rs` |
| Slice Parser | `src/rust/parser/src/expressions/postfix.rs` |
| Slice Runtime | `src/rust/runtime/src/value/collections.rs:rt_slice` |
