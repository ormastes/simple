# PyTorch SFFI Naming Convention Fix

**Date:** 2026-02-09
**Status:** ✅ Complete
**Related Plan:** `fizzy-booping-ocean.md` (PyTorch FFI Integration)

## Summary

Fixed SFFI wrapper generator to use correct `rt_*` naming convention instead of `simple_*` prefix for C ABI exports, ensuring compliance with SFFI three-tier architecture standards.

## Issues Found and Fixed

### Issue 1: Wrong C ABI Prefix (Generator Bug)

**Problem:** Wrapper generator created Tier 1 C ABI exports with `simple_` prefix instead of SFFI standard `rt_` prefix.

**Root Cause:** `src/app/wrapper_gen/tier1_gen.spl` was hardcoded to use `simple_` for all C ABI function exports.

**Fix:** Modified 4 locations in tier1_gen.spl:

1. **Line 176** - Library available function:
   ```simple
   # Before:
   pub extern "C" fn simple_{spec.name}_available() -> bool

   # After:
   pub extern "C" fn rt_{spec.name}_available() -> bool
   ```

2. **Line 181** - Library version function:
   ```simple
   # Before:
   pub extern "C" fn simple_{spec.name}_version() -> *mut c_char

   # After:
   pub extern "C" fn rt_{spec.name}_version() -> *mut c_char
   ```

3. **Line 190** - Handle free functions:
   ```simple
   # Before:
   pub extern "C" fn simple_{spec.name}_{h_lower}_free(ptr: *mut Simple{handle.name})

   # After:
   pub extern "C" fn rt_{spec.name}_{h_lower}_free(ptr: *mut Simple{handle.name})
   ```

4. **Line 247** - Function exports:
   ```simple
   # Before:
   pub extern "C" fn simple_{spec.name}_{func.name}(

   # After:
   pub extern "C" fn rt_{spec.name}_{func.name}(
   ```

5. **Line 347** - Method exports:
   ```simple
   # Before:
   pub extern "C" fn simple_{spec.name}_{h_lower}_{method.name}(

   # After:
   pub extern "C" fn rt_{spec.name}_{h_lower}_{method.name}(
   ```

### Issue 2: Wrong drop_fn in Spec File

**Problem:** `examples/torch.wrapper_spec` specified `drop_fn: "rt_torch_tensor_free"` but Tier 1 generator creates `rt_torch_torchtensor_free()`.

**Root Cause:** Spec file didn't account for the handle name being interpolated into the free function name pattern: `rt_{spec.name}_{handle.lower()}_free()`.

**Fix:** Updated torch.wrapper_spec line 15:
```yaml
# Before:
drop_fn: "rt_torch_tensor_free"

# After:
drop_fn: "rt_torch_torchtensor_free"
```

## Files Modified

### Generator Source (Permanent Fix)
- `src/app/wrapper_gen/tier1_gen.spl` - Fixed C ABI naming pattern

### Specification (Input File)
- `examples/torch.wrapper_spec` - Corrected drop_fn name

### Generated Code (Auto-Regenerated)
- `.build/rust/ffi_torch/src/lib.rs` - Tier 1 Rust wrapper
- `.build/rust/ffi_torch/src/bridge.h` - C++ bridge header
- `.build/rust/ffi_torch/src/bridge.cpp` - C++ bridge implementation
- `.build/rust/ffi_torch/Cargo.toml` - Rust package manifest
- `.build/rust/ffi_torch/build.rs` - Build script
- `src/lib/torch/ffi.spl` - Tier 2 SFFI declarations
- `src/lib/torch/mod.spl` - Tier 3 Simple API

## Verification

### Command Used
```bash
bin/simple src/app/wrapper_gen/mod.spl examples/torch.wrapper_spec
```

### Output
```
Tier 1 generated: .build/rust/ffi_torch/
✓ Tier 2 generated: src/lib/torch/ffi.spl
✓ Tier 3 generated: src/lib/torch/mod.spl
Wrapper generation complete for 'torch'
```

### Function Count Verification
```bash
$ grep "pub extern \"C\" fn rt_torch" .build/rust/ffi_torch/src/lib.rs | wc -l
15  # ✅ All Tier 1 exports use rt_ prefix

$ grep "extern fn rt_torch" src/lib/torch/ffi.spl | wc -l
14  # ✅ Tier 2 declarations (minus free, which is internal)

$ grep "rt_torch" src/lib/torch/mod.spl | wc -l
15  # ✅ Tier 3 calls all functions correctly
```

### Naming Consistency Check
```bash
# Tier 1 Exports
$ grep "pub extern \"C\" fn rt_torch_" .build/rust/ffi_torch/src/lib.rs | sed 's/pub extern "C" fn //' | sed 's/(.*/()/' | sort
rt_torch_available()
rt_torch_tensor_ones()
rt_torch_tensor_randn()
rt_torch_tensor_zeros()
rt_torch_torchtensor_add()
rt_torch_torchtensor_free()      # ← Used internally by Tier 3 drop()
rt_torch_torchtensor_matmul()
rt_torch_torchtensor_mul()
rt_torch_torchtensor_ndim()
rt_torch_torchtensor_numel()
rt_torch_torchtensor_relu()
rt_torch_torchtensor_shape()
rt_torch_torchtensor_sigmoid()
rt_torch_torchtensor_tanh()
rt_torch_version()

# Tier 2 Declarations (14 functions - free is omitted, used only in Tier 3)
$ grep "extern fn rt_torch" src/lib/torch/ffi.spl
extern fn rt_torch_available() -> bool
extern fn rt_torch_version() -> text
extern fn rt_torch_tensor_zeros(dims: [i64]) -> TorchTensor
extern fn rt_torch_tensor_ones(dims: [i64]) -> TorchTensor
extern fn rt_torch_tensor_randn(dims: [i64]) -> TorchTensor
extern fn rt_torch_torchtensor_add(handle: TorchTensor, other: TorchTensor) -> TorchTensor
extern fn rt_torch_torchtensor_mul(handle: TorchTensor, other: TorchTensor) -> TorchTensor
extern fn rt_torch_torchtensor_matmul(handle: TorchTensor, other: TorchTensor) -> TorchTensor
extern fn rt_torch_torchtensor_ndim(handle: TorchTensor) -> i64
extern fn rt_torch_torchtensor_numel(handle: TorchTensor) -> i64
extern fn rt_torch_torchtensor_shape(handle: TorchTensor) -> [i64]
extern fn rt_torch_torchtensor_relu(handle: TorchTensor) -> TorchTensor
extern fn rt_torch_torchtensor_sigmoid(handle: TorchTensor) -> TorchTensor
extern fn rt_torch_torchtensor_tanh(handle: TorchTensor) -> TorchTensor

# Tier 3 drop() Method
$ grep -A3 "fn drop():" src/lib/torch/mod.spl
    fn drop():
        """Automatically free memory when object goes out of scope."""
        if self.owns_handle:
            rt_torch_torchtensor_free(self.handle)  # ✅ Correct!
```

## Architecture Layers (Final)

```
┌─────────────────────────────────────────────────────────────────┐
│ Layer 4: Simple User API (Tier 3)                              │
│ File: src/lib/torch/mod.spl                                     │
│ Example: TorchTensorWrapper.tensor_zeros([2, 3])               │
│          calls: rt_torch_tensor_zeros()                         │
└────────────────────────────┬────────────────────────────────────┘
                             ↓
┌─────────────────────────────────────────────────────────────────┐
│ Layer 3: SFFI Declarations (Tier 2)                            │
│ File: src/lib/torch/ffi.spl                                     │
│ Declares: extern fn rt_torch_tensor_zeros(dims: [i64]) -> ...  │
│ Links to: Tier 1 C ABI exports                                 │
└────────────────────────────┬────────────────────────────────────┘
                             ↓
┌─────────────────────────────────────────────────────────────────┐
│ Layer 2: Rust C ABI Exports (Tier 1)                           │
│ File: .build/rust/ffi_torch/src/lib.rs                         │
│ Exports: #[no_mangle] pub extern "C" fn rt_torch_tensor_zeros( │
│            dims: *const i64, dims_len: usize                    │
│          ) -> *mut SimpleTorchTensor { ... }                    │
└────────────────────────────┬────────────────────────────────────┘
                             ↓
┌─────────────────────────────────────────────────────────────────┐
│ Layer 1: Rust cxx Bridge (Tier 1)                              │
│ File: .build/rust/ffi_torch/src/lib.rs (ffi module)            │
│ Calls: ffi::torch_tensor_zeros(dims_slice)                     │
│ Returns: UniquePtr<TorchTensor>                                │
└────────────────────────────┬────────────────────────────────────┘
                             ↓
┌─────────────────────────────────────────────────────────────────┐
│ Layer 0: C++ Bridge (Tier 1)                                   │
│ Files: .build/rust/ffi_torch/src/bridge.{h,cpp}                │
│ Implements: std::unique_ptr<TorchTensor>                       │
│             torch_tensor_zeros(rust::Slice<const int64_t> dims)│
│ Calls (if HAS_TORCH): torch::zeros(dims_vec)                   │
│ Calls (if stub): return std::make_unique<TorchTensor>()        │
└────────────────────────────┬────────────────────────────────────┘
                             ↓
┌─────────────────────────────────────────────────────────────────┐
│ Layer -1: PyTorch C++ API (External Library)                   │
│ Library: libtorch.so                                            │
│ Functions: torch::zeros(), torch::Tensor::add(), etc.          │
└─────────────────────────────────────────────────────────────────┘
```

## Naming Convention Rules (Established)

### SFFI Standard Pattern

1. **C ABI Exports** (Tier 1 Rust `#[no_mangle]`):
   - Pattern: `rt_{library}_{function}()`
   - Example: `rt_torch_tensor_zeros()`, `rt_torch_torchtensor_add()`

2. **SFFI Declarations** (Tier 2 Simple `extern fn`):
   - Pattern: `extern fn rt_{library}_{function}()`
   - Example: `extern fn rt_torch_tensor_zeros(dims: [i64]) -> TorchTensor`

3. **User API** (Tier 3 Simple public functions):
   - Pattern: Natural Simple naming
   - Example: `TorchTensorWrapper.tensor_zeros()`, `.add()`

4. **Internal C++ Bridge** (Tier 1 cxx bridge):
   - Pattern: `{library}_{function}()` (no `rt_` prefix)
   - Example: `torch_tensor_zeros()`, `torch_torchtensor_add()`
   - Reason: Internal layer, not exposed to Simple code

5. **Internal Rust Types** (Tier 1 structs):
   - Pattern: `Simple{HandleName}`
   - Example: `SimpleTorchTensor`
   - Reason: Internal wrapper struct, not exposed to Simple code

### What NOT to Use

❌ `simple_{library}_*` - Old pattern, replaced by `rt_*`
❌ `ffi_{library}_*` - Never used
❌ Inconsistent capitalization (e.g., `rt_torch_Tensor_free`)

## Testing Status

### Generator Tests
- ✅ Wrapper generator runs without errors
- ✅ All three tiers generate successfully
- ✅ Generated code uses consistent naming
- ✅ Function signatures match across tiers

### Integration Tests
- ⏸️ **Pending:** Build Rust FFI with Simple build system
- ⏸️ **Pending:** Test SFFI linking with Simple runtime
- ⏸️ **Pending:** Verify GPU support with PyTorch installed
- ⏸️ **Pending:** Test graceful fallback when PyTorch unavailable

## Next Steps

1. **Build Integration:**
   - Use Simple build system (NOT cargo directly) to compile Tier 1
   - Link generated FFI library with Simple runtime
   - Verify all `rt_torch_*` symbols are exported and accessible

2. **Runtime Testing:**
   - Test backend detection: `torch_available()` returns correct value
   - Test tensor creation: `TorchTensorWrapper.tensor_zeros([2, 3])`
   - Test operations: `.add()`, `.mul()`, `.matmul()`
   - Test RAII memory management: verify `drop()` calls free correctly

3. **GPU Testing:**
   - Install PyTorch with CUDA support
   - Test GPU detection: `torch_cuda_available()`
   - Test GPU tensor creation
   - Verify GPU operations work correctly

4. **Fallback Testing:**
   - Build without PyTorch (stub mode)
   - Verify graceful degradation
   - Confirm Pure Simple fallback works

## Impact

### Benefits
- ✅ SFFI naming convention standardized
- ✅ Generator produces correct code automatically
- ✅ Future wrapper specs will use correct naming
- ✅ All layers properly separated and testable
- ✅ Documentation matches implementation

### Breaking Changes
- None (this was a fix for auto-generated code)
- Existing manually-written SFFI wrappers unaffected
- Only PyTorch wrapper was being generated (new code)

## Related Documentation

- Plan: `.claude/plans/fizzy-booping-ocean.md` - Original PyTorch FFI integration plan
- Pattern: `doc/design/sffi_external_library_pattern.md` - Three-tier SFFI design
- Guide: `doc/guide/sffi_gen_guide.md` - Wrapper generator usage guide
- Skills: `.claude/skills/sffi.md` - SFFI patterns and examples
