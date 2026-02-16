# PyTorch FFI Integration Guide

## Current Status

**PyTorch FFI Library:** ✅ Built successfully at `.build/rust/ffi_torch/target/release/libsimple_torch_ffi.so` (400KB)

**Runtime Integration:** ❌ Not currently integrated with `bin/release/simple`

**Reason:** The Simple runtime (`bin/release/simple`) is pre-built and does not include PyTorch FFI symbols. The `extern fn rt_torch_*` declarations in `src/lib/torch/ffi.spl` expect these functions to be statically linked into the runtime binary.

## Available Functions

The FFI library exports 100+ tensor operations organized into categories:

### Library Information
- `rt_torch_available()` - Check if PyTorch is available
- `rt_torch_version()` - Get PyTorch version string
- `rt_torch_cuda_available()` - Check if CUDA is available

### Tensor Creation (10 functions)
- `rt_torch_tensor_zeros`, `rt_torch_tensor_ones`, `rt_torch_tensor_randn`, `rt_torch_tensor_rand`
- `rt_torch_tensor_full`, `rt_torch_tensor_from_data`, `rt_torch_tensor_arange`
- `rt_torch_tensor_linspace`, `rt_torch_tensor_eye`, `rt_torch_tensor_empty`

### Arithmetic Operations (12 functions)
- Element-wise: `add`, `sub`, `mul`, `div`, `pow`, `neg`, `abs`, `sqrt`, `exp`, `log`
- Scalar operations: `add_scalar`, `mul_scalar`

### Activation Functions (7 functions)
- `relu`, `sigmoid`, `tanh`, `leaky_relu`, `gelu`, `softmax`, `log_softmax`

### Linear Algebra (9 functions)
- `matmul`, `dot`, `transpose`, `t`, `norm`, `det`, `inverse`, `svd`, `eig`

### Reduction Operations (12 functions)
- `sum`, `sum_dim`, `mean`, `mean_dim`, `max`, `max_dim`, `min`, `min_dim`
- `argmax`, `argmin`, `std`, `var`

### Shape Manipulation (11 functions)
- `ndim`, `numel`, `shape`, `reshape`, `view`, `permute`
- `squeeze`, `squeeze_dim`, `unsqueeze`, `flatten`, `contiguous`

### Neural Network Operations (8 functions)
- `conv2d`, `max_pool2d`, `avg_pool2d`, `batch_norm`, `layer_norm`
- `dropout`, `linear`, `embedding`

### Loss Functions (4 functions)
- `mse_loss`, `cross_entropy`, `binary_cross_entropy`, `nll_loss`

### Autograd Operations (7 functions)
- `set_requires_grad`, `requires_grad`, `grad`, `backward`, `zero_grad`
- `detach`, `no_grad_begin/end`

### Device Management (7 functions)
- `cuda`, `cpu`, `is_cuda`, `device`, `to_stream`, `clone`, memory operations

### CUDA Streams (4 functions)
- `stream_create`, `sync`, `query`, `free`

**Total: 100+ FFI functions** defined in `src/lib/torch/ffi.spl`

## Integration Options

### Option 1: Rebuild Runtime with PyTorch FFI (Recommended for Production)

Rebuild the Simple runtime with PyTorch FFI statically linked:

```bash
# 1. Build PyTorch FFI library
cd .build/rust/ffi_torch
cargo build --release

# 2. Rebuild Simple runtime with FFI linked
# (Requires modifying seed compiler build script to link libsimple_torch_ffi.so)
cd /home/ormastes/dev/pub/simple
# TODO: Add linker flags to seed build:
#   -L.build/rust/ffi_torch/target/release -lsimple_torch_ffi

# 3. Verify symbols are present
nm bin/release/simple | grep rt_torch_tensor_zeros
# Should show: T rt_torch_tensor_zeros
```

**Status:** Not yet implemented - requires build system changes.

### Option 2: Dynamic FFI Loading (Future Enhancement)

Add dynamic library loading support to Simple runtime:

```simple
# Hypothetical API (not yet implemented):
extern fn rt_dlopen(path: text, flags: i64) -> i64
extern fn rt_dlsym(handle: i64, symbol: text) -> i64
extern fn rt_dlclose(handle: i64) -> bool

fn load_torch_ffi():
    val lib = rt_dlopen(".build/rust/ffi_torch/target/release/libsimple_torch_ffi.so", 0x00001)
    if lib == 0:
        print "Failed to load PyTorch FFI"
        return false

    # Load each function symbol...
    # (Complex - requires function pointer support)
    true
```

**Status:** Not yet implemented - requires new runtime FFI functions.

### Option 3: Use Stub Mode (Current State)

The current PyTorch module (`src/lib/torch/mod.spl`) is designed to work in "stub mode" where `torch_available()` returns `false` and all operations return placeholder tensors:

```simple
use lib.torch.{torch_available, Tensor}

fn main():
    if torch_available():
        # Real PyTorch backend
        val t = Tensor.zeros([3, 3])
        print t.shape()  # [3, 3]
    else:
        # Stub mode - operations are no-ops
        print "Running in stub mode (PyTorch not available)"
```

**Current behavior:** All examples will print "PyTorch not available" and return early.

## Testing Strategy

Until runtime integration is complete, use the comprehensive test suite to verify:
1. Module structure and imports
2. API surface area completeness
3. Function signatures match FFI declarations
4. Stub mode graceful degradation

See `test/system/dl_examples_system_spec.spl` for full test coverage.

## Examples

The repository includes 5 PyTorch examples in `examples/torch/`:

### Basic Examples (3 files)
1. **01_tensor_creation.spl** - Creating tensors with different initialization
2. **02_tensor_operations.spl** - Arithmetic and matrix operations
3. **03_device_selection.spl** - CPU/GPU device management

### Training Examples (2 files)
4. **mnist_classifier.spl** - MNIST digit classification
5. **xor_pytorch.spl** - XOR problem with PyTorch

**Expected Output (Current):**
```
=== PyTorch Tensor Creation ===
Backend Check:
  torch_available() = false
  ⚠ Running in stub mode (PyTorch not installed)
```

**Expected Output (After Integration):**
```
=== PyTorch Tensor Creation ===
Backend Check:
  torch_available() = true
  torch_version() = 2.1.0+cu118
  ✓ PyTorch FFI backend ready

Creating tensors...
1. Zeros tensor [3, 4]:
   Shape: [3, 4]
   Dimensions: 2D
   Total elements: 12
```

## Workaround for Development

For immediate testing of PyTorch operations, use one of these approaches:

### A. Python-based testing
```bash
# Test FFI library directly via Python/ctypes
python3 test_torch_ffi.py
```

### B. Standalone C++ test harness
```bash
# Link test program against FFI library
g++ test_torch.cpp -L.build/rust/ffi_torch/target/release -lsimple_torch_ffi -o test_torch
LD_LIBRARY_PATH=.build/rust/ffi_torch/target/release ./test_torch
```

### C. Mock testing in Simple
```simple
# Test the Simple API layer without real tensor operations
use lib.torch.{Tensor, Linear}

# All operations work, but return stub values
val layer = Linear.create(128, 64)
val x = Tensor.zeros([32, 128])
val y = layer.forward(x)
print y.shape()  # [32, 64] - shape tracking works
```

## Next Steps

To enable full PyTorch integration:

1. **Modify seed compiler build** to link `libsimple_torch_ffi.so`
2. **Rebuild runtime** with `scripts/install.sh` (or equivalent)
3. **Verify symbols** with `nm bin/release/simple | grep rt_torch`
4. **Test examples** with `bin/simple examples/torch/basics/01_tensor_creation.spl`
5. **Run test suite** with `bin/simple test test/system/dl_examples_system_spec.spl`

## File Locations

- **FFI declarations:** `src/lib/torch/ffi.spl` (390 lines, 100+ extern functions)
- **Simple API:** `src/lib/torch/mod.spl` (803 lines, Tensor class + NN layers)
- **FFI library:** `.build/rust/ffi_torch/target/release/libsimple_torch_ffi.so` (400KB)
- **Examples:** `examples/torch/` (5 files)
- **Runtime:** `bin/release/simple` (27MB, pre-built without PyTorch FFI)

## Known Issues

1. **Import system:** `use lib.torch.{torch_available}` fails due to SIMPLE_LIB path resolution bug (see MEMORY.md). Workaround: Create local symlinks or declare functions inline.

2. **Function name mismatch:** Examples use `TorchTensorWrapper` but module exports `Tensor`. Fixed by adding alias: `val TorchTensorWrapper = Tensor`.

3. **No dynamic loading:** Runtime doesn't support `dlopen`/`dlsym` pattern for loading external `.so` files at runtime.

## Conclusion

The PyTorch FFI integration is **architecturally complete** but **not runtime-integrated**. All pieces exist:
- ✅ FFI library built (400KB .so with 100+ functions)
- ✅ Simple API layer (`Tensor`, `Linear`, optimizers, losses)
- ✅ Example programs (5 files covering basics + training)
- ❌ Runtime linkage (requires rebuild)

To make it work: rebuild `bin/release/simple` with `-lsimple_torch_ffi` linker flag.
