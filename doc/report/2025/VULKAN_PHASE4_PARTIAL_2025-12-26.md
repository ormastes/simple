# Vulkan Phase 4: Compiler Integration (Partial Complete)

**Date:** 2025-12-26
**Phase:** 4/6 - Compiler Pipeline Integration
**Status:** 🔄 Partial (FFI Registration & SPIR-V Fixes Complete)

## Summary

Completed the first two sub-tasks of Phase 4: registered all 12 Vulkan FFI functions in the compiler's runtime function registry and fixed all pre-existing SPIR-V generation errors. The compiler now builds successfully with the `vulkan` feature enabled.

## Work Completed

### 1. FFI Function Registration

**File Modified:** `src/compiler/src/codegen/runtime_ffi.rs`

**Changes:**
- Added 12 Vulkan FFI function specifications to `RUNTIME_FUNCS` array
- Organized as a new section "Vulkan GPU backend operations" after existing GPU functions

**Functions Registered:**
```rust
RuntimeFuncSpec::new("rt_vk_available", &[], &[I32]),                      // () -> available
RuntimeFuncSpec::new("rt_vk_device_create", &[], &[I64]),                  // () -> device_handle
RuntimeFuncSpec::new("rt_vk_device_free", &[I64], &[I32]),                 // device_handle -> status
RuntimeFuncSpec::new("rt_vk_device_sync", &[I64], &[I32]),                 // device_handle -> status
RuntimeFuncSpec::new("rt_vk_buffer_alloc", &[I64, I64], &[I64]),           // (device, size) -> buffer_handle
RuntimeFuncSpec::new("rt_vk_buffer_free", &[I64], &[I32]),                 // buffer_handle -> status
RuntimeFuncSpec::new("rt_vk_buffer_upload", &[I64, I64, I64], &[I32]),     // (buffer, data_ptr, size) -> status
RuntimeFuncSpec::new("rt_vk_buffer_download", &[I64, I64, I64], &[I32]),   // (buffer, data_ptr, size) -> status
RuntimeFuncSpec::new("rt_vk_kernel_compile", &[I64, I64, I64], &[I64]),    // (device, spirv_ptr, len) -> pipeline_handle
RuntimeFuncSpec::new("rt_vk_kernel_free", &[I64], &[I32]),                 // pipeline_handle -> status
RuntimeFuncSpec::new("rt_vk_kernel_launch", &[I64, I64, I64, I32, I32, I32, I32, I32, I32], &[I32]), // 3D launch
RuntimeFuncSpec::new("rt_vk_kernel_launch_1d", &[I64, I64, I64, I32], &[I32]), // Simplified 1D launch
```

**Lines Added:** 13 (12 function specs + 1 section comment)

### 2. SPIR-V Generation Error Fixes

**Files Modified:**
- `src/compiler/src/codegen/vulkan/spirv_builder.rs` (7 fixes)
- `src/compiler/src/error.rs` (1 addition)

#### Fix 1: LiteralInt32 → LiteralBit32 (3 occurrences)

**Issue:** rspirv 0.12 renamed `Operand::LiteralInt32` to `Operand::LiteralBit32`

**Locations Fixed:**
- Line 205: `Decoration::Offset` member decoration
- Line 218: `Decoration::DescriptorSet` decoration
- Line 224: `Decoration::Binding` decoration

**Change:**
```rust
// Before
vec![rspirv::dr::Operand::LiteralInt32(0)]

// After
vec![rspirv::dr::Operand::LiteralBit32(0)]
```

#### Fix 2: BlockId Type Conversion (2 occurrences)

**Issue:** `BlockId(u32)` but `enumerate()` returns `usize`

**Locations Fixed:**
- Line 243: Block label pre-allocation
- Line 250: Block compilation loop

**Change:**
```rust
// Before
let block_id = BlockId(i);

// After
let block_id = BlockId(i.try_into().unwrap());
```

#### Fix 3: Module Import Path

**Issue:** `crate::hir::types::TypeId` - `types` module is private

**Location:** Line 7

**Change:**
```rust
// Before
use crate::hir::types::TypeId;

// After
use crate::hir::{BinOp, TypeId};  // Consolidated import
```

**Rationale:** HIR module re-exports types with `pub use types::*;`

#### Fix 4: Result Error Handling in Match Expression

**Issue:** Match expression returned `(TypeId, u32, Result<u32>)` but tried to call `.map_err()` on the tuple

**Locations Fixed:** All 30+ match arms in binary operation lowering (lines 382-538)

**Changes:**
1. Added `?` operator to all `self.builder.*()` calls to unwrap Results within match arms
2. Removed the outer `.map_err()` call after the match expression

**Example:**
```rust
// Before
(BinOp::Add, TypeId::I32 | TypeId::I64) => {
    let ty = self.type_id_to_spirv(left_type)?;
    (left_type, ty, self.builder.i_add(ty, None, left_id, right_id))
}
// ... (30 more arms)
}.map_err(|e| CompileError::Codegen(format!("Failed to emit binary op: {}", e)))?;

// After
(BinOp::Add, TypeId::I32 | TypeId::I64) => {
    let ty = self.type_id_to_spirv(left_type)?;
    (left_type, ty, self.builder.i_add(ty, None, left_id, right_id)?)
}
// ... (30 more arms with ? added)
};  // No .map_err()
```

#### Fix 5: Error Type Conversion

**Issue:** `?` operator couldn't convert `rspirv::dr::Error` to `CompileError`

**File:** `src/compiler/src/error.rs` (lines 539-545)

**Change:** Added `From` trait implementation
```rust
// SPIR-V error conversion (for Vulkan backend)
#[cfg(feature = "vulkan")]
impl From<rspirv::dr::Error> for CompileError {
    fn from(e: rspirv::dr::Error) -> Self {
        Self::Codegen(format!("SPIR-V error: {}", e))
    }
}
```

#### Fix 6: Double Mutable Borrow

**Issue:** Line 756 borrowed `self` mutably twice in same expression

**Location:** `spirv_builder.rs:756`

**Change:**
```rust
// Before
let zero = self.builder.constant_bit32(self.get_u32_type(), 0);

// After
let u32_type = self.get_u32_type();
let zero = self.builder.constant_bit32(u32_type, 0);
```

### Build Status

**Before Fixes:**
```
error: could not compile `simple-compiler` (lib) due to 6 previous errors
```

**After All Fixes:**
```
✅ Finished `dev` profile [unoptimized + debuginfo] target(s) in 16.30s
```

**Command:** `cargo build -p simple-compiler --features vulkan`

**Warnings:** 107 warnings (pre-existing, unrelated to Vulkan)

## Files Modified Summary

| File | Lines Changed | Description |
|------|---------------|-------------|
| `src/compiler/src/codegen/runtime_ffi.rs` | +13 | Added 12 FFI function specs |
| `src/compiler/src/codegen/vulkan/spirv_builder.rs` | ~60 modified | Fixed 6 types of errors |
| `src/compiler/src/error.rs` | +7 | Added rspirv error conversion |

**Total:** ~80 lines changed/added across 3 files

## Remaining Phase 4 Work

### Next Sub-task: Backend Selection

**Goal:** Wire Vulkan backend into compiler's backend selection logic

**Key Changes Needed:**

1. **Add VulkanBackend enum variant** (`src/compiler/src/codegen/backend_trait.rs`)
   ```rust
   pub enum BackendKind {
       Cranelift,
       Llvm,
       Vulkan,  // NEW
       Software,  // Explicit fallback
   }
   ```

2. **Implement backend selection** (same file)
   ```rust
   impl BackendKind {
       pub fn for_gpu_kernel(target: &Target) -> Self {
           if cfg!(feature = "vulkan") && VulkanBackend::supports_target(target) {
               BackendKind::Vulkan
           } else {
               tracing::warn!("Vulkan unavailable, using software GPU backend");
               BackendKind::Software
           }
       }
   }
   ```

3. **Integrate with pipeline** (`src/compiler/src/pipeline.rs`)
   - Route `#[gpu]` functions to `BackendKind::for_gpu_kernel()`
   - Pass SPIR-V bytecode to runtime for compilation
   - Store compiled kernels in module metadata

**Estimated Lines:** ~150 lines across 2-3 files

**Estimated Time:** 1-2 hours

## Testing Status

- ✅ **Compilation:** Builds successfully with `--features vulkan`
- ✅ **Runtime:** Builds successfully (verified in Phase 3)
- ⏸️ **Integration:** Pending backend selection implementation
- ⏸️ **Unit Tests:** Scheduled for Phase 5
- ⏸️ **SPIR-V Validation:** Pending spirv-val integration (Phase 1 task)

## Technical Notes

### Error Handling Pattern

All SPIR-V builder calls now use inline `?` operator for error propagation:
```rust
let result = self.builder.some_operation(...)
    ?  // Automatically converts rspirv::dr::Error → CompileError
```

This pattern:
- Relies on the `From<rspirv::dr::Error>` trait implementation
- Provides automatic error conversion
- Results in cleaner code compared to explicit `.map_err()`
- Only works when the From trait is in scope (feature-gated)

### Pointer Type Mapping

All FFI parameters use Cranelift types:
- `u64` handles → `I64`
- `*const u8`, `*mut u8` → `I64` (pointer size)
- `u32` work group sizes → `I32`
- `i32` status codes → `I32`

### Feature Gating

All Vulkan-related code properly gated:
- `#[cfg(feature = "vulkan")]` on From impl
- Dependency optional in Cargo.toml
- Runtime FFI exports conditional

## Next Steps

1. **Backend Selection** - Wire Vulkan into compiler pipeline (~150 lines, 1-2 hours)
2. **Testing** - Phase 5 comprehensive test suite (unit + integration)
3. **Documentation** - Phase 6 user guides and examples

## References

- Phase 3 Report: `doc/report/VULKAN_PHASE3_FFI_BRIDGE_2025-12-26.md`
- Implementation Plan: `.claude/plans/cheerful-stirring-backus.md`
- Runtime FFI Documentation: `src/compiler/src/codegen/runtime_ffi.rs` (comments)
