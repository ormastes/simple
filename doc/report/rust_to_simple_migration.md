# Rust to Simple Migration Status

## Summary

- **Total Rust modules**: 1233
- **Should stay in Rust**: 350
- **Should migrate to Simple**: 207
  - Migrated: 0
  - Not migrated: 207
- **Needs review**: 676

## Unmigrated Modules (Should Be in Simple)

### compiler/codegen/backend_trait
- **Rust path**: `rust/compiler/src/codegen/backend_trait.rs`
- **Expected Simple path**: `src/compiler/codegen/backend_trait.spl` or `src/app/codegen/backend_trait.spl`
- **Status**: ❌ Not migrated

### compiler/codegen/buffer_pool
- **Rust path**: `rust/compiler/src/codegen/buffer_pool.rs`
- **Expected Simple path**: `src/compiler/codegen/buffer_pool.spl` or `src/app/codegen/buffer_pool.spl`
- **Status**: ❌ Not migrated

### compiler/codegen/codegen_instr_tests
- **Rust path**: `rust/compiler/src/codegen/codegen_instr_tests.rs`
- **Expected Simple path**: `src/compiler/codegen/codegen_instr_tests.spl` or `src/app/codegen/codegen_instr_tests.spl`
- **Status**: ❌ Not migrated

### compiler/codegen/codegen_shared_tests
- **Rust path**: `rust/compiler/src/codegen/codegen_shared_tests.rs`
- **Expected Simple path**: `src/compiler/codegen/codegen_shared_tests.spl` or `src/app/codegen/codegen_shared_tests.spl`
- **Status**: ❌ Not migrated

### compiler/codegen/common_backend
- **Rust path**: `rust/compiler/src/codegen/common_backend.rs`
- **Expected Simple path**: `src/compiler/codegen/common_backend.spl` or `src/app/codegen/common_backend.spl`
- **Status**: ❌ Not migrated

### compiler/codegen/cranelift
- **Rust path**: `rust/compiler/src/codegen/cranelift.rs`
- **Expected Simple path**: `src/compiler/codegen/cranelift.spl` or `src/app/codegen/cranelift.spl`
- **Status**: ❌ Not migrated

### compiler/codegen/cranelift_emitter
- **Rust path**: `rust/compiler/src/codegen/cranelift_emitter.rs`
- **Expected Simple path**: `src/compiler/codegen/cranelift_emitter.spl` or `src/app/codegen/cranelift_emitter.spl`
- **Status**: ❌ Not migrated

### compiler/codegen/dispatch
- **Rust path**: `rust/compiler/src/codegen/dispatch.rs`
- **Expected Simple path**: `src/compiler/codegen/dispatch.spl` or `src/app/codegen/dispatch.spl`
- **Status**: ❌ Not migrated

### compiler/codegen/emitter_trait
- **Rust path**: `rust/compiler/src/codegen/emitter_trait.rs`
- **Expected Simple path**: `src/compiler/codegen/emitter_trait.spl` or `src/app/codegen/emitter_trait.spl`
- **Status**: ❌ Not migrated

### compiler/codegen/instr_gpu
- **Rust path**: `rust/compiler/src/codegen/instr_gpu.rs`
- **Expected Simple path**: `src/compiler/codegen/instr_gpu.spl` or `src/app/codegen/instr_gpu.spl`
- **Status**: ❌ Not migrated

### compiler/codegen/instr_special
- **Rust path**: `rust/compiler/src/codegen/instr_special.rs`
- **Expected Simple path**: `src/compiler/codegen/instr_special.spl` or `src/app/codegen/instr_special.spl`
- **Status**: ❌ Not migrated

### compiler/codegen/jit_tests
- **Rust path**: `rust/compiler/src/codegen/jit_tests.rs`
- **Expected Simple path**: `src/compiler/codegen/jit_tests.spl` or `src/app/codegen/jit_tests.spl`
- **Status**: ❌ Not migrated

### compiler/codegen/llvm_test_utils
- **Rust path**: `rust/compiler/src/codegen/llvm_test_utils.rs`
- **Expected Simple path**: `src/compiler/codegen/llvm_test_utils.spl` or `src/app/codegen/llvm_test_utils.spl`
- **Status**: ❌ Not migrated

### compiler/codegen/mir_interpreter
- **Rust path**: `rust/compiler/src/codegen/mir_interpreter.rs`
- **Expected Simple path**: `src/compiler/codegen/mir_interpreter.spl` or `src/app/codegen/mir_interpreter.spl`
- **Status**: ❌ Not migrated

### compiler/codegen/mod
- **Rust path**: `rust/compiler/src/codegen/mod.rs`
- **Expected Simple path**: `src/compiler/codegen/mod.spl` or `src/app/codegen/mod.spl`
- **Status**: ❌ Not migrated

### compiler/codegen/parallel
- **Rust path**: `rust/compiler/src/codegen/parallel.rs`
- **Expected Simple path**: `src/compiler/codegen/parallel.spl` or `src/app/codegen/parallel.spl`
- **Status**: ❌ Not migrated

### compiler/codegen/shared
- **Rust path**: `rust/compiler/src/codegen/shared.rs`
- **Expected Simple path**: `src/compiler/codegen/shared.spl` or `src/app/codegen/shared.spl`
- **Status**: ❌ Not migrated

### compiler/codegen/types_util
- **Rust path**: `rust/compiler/src/codegen/types_util.rs`
- **Expected Simple path**: `src/compiler/codegen/types_util.spl` or `src/app/codegen/types_util.spl`
- **Status**: ❌ Not migrated

### compiler/codegen/wasm_bindgen_gen
- **Rust path**: `rust/compiler/src/codegen/wasm_bindgen_gen.rs`
- **Expected Simple path**: `src/compiler/codegen/wasm_bindgen_gen.spl` or `src/app/codegen/wasm_bindgen_gen.spl`
- **Status**: ❌ Not migrated

### compiler/codegen/runtime_ffi
- **Rust path**: `rust/compiler/src/codegen/runtime_ffi.rs`
- **Expected Simple path**: `src/compiler/codegen/runtime_ffi.spl` or `src/app/codegen/runtime_ffi.spl`
- **Status**: ❌ Not migrated

### compiler/codegen/cranelift_tests
- **Rust path**: `rust/compiler/src/codegen/cranelift_tests.rs`
- **Expected Simple path**: `src/compiler/codegen/cranelift_tests.spl` or `src/app/codegen/cranelift_tests.spl`
- **Status**: ❌ Not migrated

### compiler/codegen/jit
- **Rust path**: `rust/compiler/src/codegen/jit.rs`
- **Expected Simple path**: `src/compiler/codegen/jit.spl` or `src/app/codegen/jit.spl`
- **Status**: ❌ Not migrated

### compiler/codegen/cranelift_ffi
- **Rust path**: `rust/compiler/src/codegen/cranelift_ffi.rs`
- **Expected Simple path**: `src/compiler/codegen/cranelift_ffi.spl` or `src/app/codegen/cranelift_ffi.spl`
- **Status**: ❌ Not migrated

### compiler/codegen/bytecode/compiler
- **Rust path**: `rust/compiler/src/codegen/bytecode/compiler.rs`
- **Expected Simple path**: `src/compiler/codegen/bytecode/compiler.spl` or `src/app/codegen/bytecode/compiler.spl`
- **Status**: ❌ Not migrated

### compiler/codegen/bytecode/compiler_tests
- **Rust path**: `rust/compiler/src/codegen/bytecode/compiler_tests.rs`
- **Expected Simple path**: `src/compiler/codegen/bytecode/compiler_tests.spl` or `src/app/codegen/bytecode/compiler_tests.spl`
- **Status**: ❌ Not migrated

### compiler/codegen/bytecode/mod
- **Rust path**: `rust/compiler/src/codegen/bytecode/mod.rs`
- **Expected Simple path**: `src/compiler/codegen/bytecode/mod.spl` or `src/app/codegen/bytecode/mod.spl`
- **Status**: ❌ Not migrated

### compiler/codegen/instr/actors
- **Rust path**: `rust/compiler/src/codegen/instr/actors.rs`
- **Expected Simple path**: `src/compiler/codegen/instr/actors.spl` or `src/app/codegen/instr/actors.spl`
- **Status**: ❌ Not migrated

### compiler/codegen/instr/async_ops
- **Rust path**: `rust/compiler/src/codegen/instr/async_ops.rs`
- **Expected Simple path**: `src/compiler/codegen/instr/async_ops.spl` or `src/app/codegen/instr/async_ops.spl`
- **Status**: ❌ Not migrated

### compiler/codegen/instr/basic_ops
- **Rust path**: `rust/compiler/src/codegen/instr/basic_ops.rs`
- **Expected Simple path**: `src/compiler/codegen/instr/basic_ops.spl` or `src/app/codegen/instr/basic_ops.spl`
- **Status**: ❌ Not migrated

### compiler/codegen/instr/body
- **Rust path**: `rust/compiler/src/codegen/instr/body.rs`
- **Expected Simple path**: `src/compiler/codegen/instr/body.spl` or `src/app/codegen/instr/body.spl`
- **Status**: ❌ Not migrated

### compiler/codegen/instr/calls
- **Rust path**: `rust/compiler/src/codegen/instr/calls.rs`
- **Expected Simple path**: `src/compiler/codegen/instr/calls.spl` or `src/app/codegen/instr/calls.spl`
- **Status**: ❌ Not migrated

### compiler/codegen/instr/closures_structs
- **Rust path**: `rust/compiler/src/codegen/instr/closures_structs.rs`
- **Expected Simple path**: `src/compiler/codegen/instr/closures_structs.spl` or `src/app/codegen/instr/closures_structs.spl`
- **Status**: ❌ Not migrated

### compiler/codegen/instr/collections
- **Rust path**: `rust/compiler/src/codegen/instr/collections.rs`
- **Expected Simple path**: `src/compiler/codegen/instr/collections.spl` or `src/app/codegen/instr/collections.spl`
- **Status**: ❌ Not migrated

### compiler/codegen/instr/constants
- **Rust path**: `rust/compiler/src/codegen/instr/constants.rs`
- **Expected Simple path**: `src/compiler/codegen/instr/constants.spl` or `src/app/codegen/instr/constants.spl`
- **Status**: ❌ Not migrated

### compiler/codegen/instr/contracts
- **Rust path**: `rust/compiler/src/codegen/instr/contracts.rs`
- **Expected Simple path**: `src/compiler/codegen/instr/contracts.spl` or `src/app/codegen/instr/contracts.spl`
- **Status**: ❌ Not migrated

### compiler/codegen/instr/core
- **Rust path**: `rust/compiler/src/codegen/instr/core.rs`
- **Expected Simple path**: `src/compiler/codegen/instr/core.spl` or `src/app/codegen/instr/core.spl`
- **Status**: ❌ Not migrated

### compiler/codegen/instr/coverage
- **Rust path**: `rust/compiler/src/codegen/instr/coverage.rs`
- **Expected Simple path**: `src/compiler/codegen/instr/coverage.spl` or `src/app/codegen/instr/coverage.spl`
- **Status**: ❌ Not migrated

### compiler/codegen/instr/enum_union
- **Rust path**: `rust/compiler/src/codegen/instr/enum_union.rs`
- **Expected Simple path**: `src/compiler/codegen/instr/enum_union.spl` or `src/app/codegen/instr/enum_union.spl`
- **Status**: ❌ Not migrated

### compiler/codegen/instr/extern_classes
- **Rust path**: `rust/compiler/src/codegen/instr/extern_classes.rs`
- **Expected Simple path**: `src/compiler/codegen/instr/extern_classes.spl` or `src/app/codegen/instr/extern_classes.spl`
- **Status**: ❌ Not migrated

### compiler/codegen/instr/fields
- **Rust path**: `rust/compiler/src/codegen/instr/fields.rs`
- **Expected Simple path**: `src/compiler/codegen/instr/fields.spl` or `src/app/codegen/instr/fields.spl`
- **Status**: ❌ Not migrated

### compiler/codegen/instr/helpers
- **Rust path**: `rust/compiler/src/codegen/instr/helpers.rs`
- **Expected Simple path**: `src/compiler/codegen/instr/helpers.spl` or `src/app/codegen/instr/helpers.spl`
- **Status**: ❌ Not migrated

### compiler/codegen/instr/interpreter
- **Rust path**: `rust/compiler/src/codegen/instr/interpreter.rs`
- **Expected Simple path**: `src/compiler/codegen/instr/interpreter.spl` or `src/app/codegen/instr/interpreter.spl`
- **Status**: ❌ Not migrated

### compiler/codegen/instr/memory
- **Rust path**: `rust/compiler/src/codegen/instr/memory.rs`
- **Expected Simple path**: `src/compiler/codegen/instr/memory.spl` or `src/app/codegen/instr/memory.spl`
- **Status**: ❌ Not migrated

### compiler/codegen/instr/methods
- **Rust path**: `rust/compiler/src/codegen/instr/methods.rs`
- **Expected Simple path**: `src/compiler/codegen/instr/methods.spl` or `src/app/codegen/instr/methods.spl`
- **Status**: ❌ Not migrated

### compiler/codegen/instr/mod
- **Rust path**: `rust/compiler/src/codegen/instr/mod.rs`
- **Expected Simple path**: `src/compiler/codegen/instr/mod.spl` or `src/app/codegen/instr/mod.spl`
- **Status**: ❌ Not migrated

### compiler/codegen/instr/parallel
- **Rust path**: `rust/compiler/src/codegen/instr/parallel.rs`
- **Expected Simple path**: `src/compiler/codegen/instr/parallel.spl` or `src/app/codegen/instr/parallel.spl`
- **Status**: ❌ Not migrated

### compiler/codegen/instr/pattern
- **Rust path**: `rust/compiler/src/codegen/instr/pattern.rs`
- **Expected Simple path**: `src/compiler/codegen/instr/pattern.spl` or `src/app/codegen/instr/pattern.spl`
- **Status**: ❌ Not migrated

### compiler/codegen/instr/pointers
- **Rust path**: `rust/compiler/src/codegen/instr/pointers.rs`
- **Expected Simple path**: `src/compiler/codegen/instr/pointers.spl` or `src/app/codegen/instr/pointers.spl`
- **Status**: ❌ Not migrated

### compiler/codegen/instr/result
- **Rust path**: `rust/compiler/src/codegen/instr/result.rs`
- **Expected Simple path**: `src/compiler/codegen/instr/result.spl` or `src/app/codegen/instr/result.spl`
- **Status**: ❌ Not migrated

### compiler/codegen/instr/simd_stubs
- **Rust path**: `rust/compiler/src/codegen/instr/simd_stubs.rs`
- **Expected Simple path**: `src/compiler/codegen/instr/simd_stubs.spl` or `src/app/codegen/instr/simd_stubs.spl`
- **Status**: ❌ Not migrated

### compiler/codegen/instr/units
- **Rust path**: `rust/compiler/src/codegen/instr/units.rs`
- **Expected Simple path**: `src/compiler/codegen/instr/units.spl` or `src/app/codegen/instr/units.spl`
- **Status**: ❌ Not migrated

### compiler/codegen/lean/contracts
- **Rust path**: `rust/compiler/src/codegen/lean/contracts.rs`
- **Expected Simple path**: `src/compiler/codegen/lean/contracts.spl` or `src/app/codegen/lean/contracts.spl`
- **Status**: ❌ Not migrated

### compiler/codegen/lean/emitter
- **Rust path**: `rust/compiler/src/codegen/lean/emitter.rs`
- **Expected Simple path**: `src/compiler/codegen/lean/emitter.spl` or `src/app/codegen/lean/emitter.spl`
- **Status**: ❌ Not migrated

### compiler/codegen/lean/expressions
- **Rust path**: `rust/compiler/src/codegen/lean/expressions.rs`
- **Expected Simple path**: `src/compiler/codegen/lean/expressions.spl` or `src/app/codegen/lean/expressions.spl`
- **Status**: ❌ Not migrated

### compiler/codegen/lean/functions
- **Rust path**: `rust/compiler/src/codegen/lean/functions.rs`
- **Expected Simple path**: `src/compiler/codegen/lean/functions.spl` or `src/app/codegen/lean/functions.spl`
- **Status**: ❌ Not migrated

### compiler/codegen/lean/memory_safety
- **Rust path**: `rust/compiler/src/codegen/lean/memory_safety.rs`
- **Expected Simple path**: `src/compiler/codegen/lean/memory_safety.spl` or `src/app/codegen/lean/memory_safety.spl`
- **Status**: ❌ Not migrated

### compiler/codegen/lean/mod
- **Rust path**: `rust/compiler/src/codegen/lean/mod.rs`
- **Expected Simple path**: `src/compiler/codegen/lean/mod.spl` or `src/app/codegen/lean/mod.spl`
- **Status**: ❌ Not migrated

### compiler/codegen/lean/naming
- **Rust path**: `rust/compiler/src/codegen/lean/naming.rs`
- **Expected Simple path**: `src/compiler/codegen/lean/naming.spl` or `src/app/codegen/lean/naming.spl`
- **Status**: ❌ Not migrated

### compiler/codegen/lean/runner
- **Rust path**: `rust/compiler/src/codegen/lean/runner.rs`
- **Expected Simple path**: `src/compiler/codegen/lean/runner.spl` or `src/app/codegen/lean/runner.spl`
- **Status**: ❌ Not migrated

### compiler/codegen/lean/traits
- **Rust path**: `rust/compiler/src/codegen/lean/traits.rs`
- **Expected Simple path**: `src/compiler/codegen/lean/traits.spl` or `src/app/codegen/lean/traits.spl`
- **Status**: ❌ Not migrated

### compiler/codegen/lean/types
- **Rust path**: `rust/compiler/src/codegen/lean/types.rs`
- **Expected Simple path**: `src/compiler/codegen/lean/types.spl` or `src/app/codegen/lean/types.spl`
- **Status**: ❌ Not migrated

### compiler/codegen/lean/verification_checker
- **Rust path**: `rust/compiler/src/codegen/lean/verification_checker.rs`
- **Expected Simple path**: `src/compiler/codegen/lean/verification_checker.spl` or `src/app/codegen/lean/verification_checker.spl`
- **Status**: ❌ Not migrated

### compiler/codegen/lean/verification_diagnostics
- **Rust path**: `rust/compiler/src/codegen/lean/verification_diagnostics.rs`
- **Expected Simple path**: `src/compiler/codegen/lean/verification_diagnostics.spl` or `src/app/codegen/lean/verification_diagnostics.spl`
- **Status**: ❌ Not migrated

### compiler/codegen/llvm/backend
- **Rust path**: `rust/compiler/src/codegen/llvm/backend.rs`
- **Expected Simple path**: `src/compiler/codegen/llvm/backend.spl` or `src/app/codegen/llvm/backend.spl`
- **Status**: ❌ Not migrated

### compiler/codegen/llvm/backend_core
- **Rust path**: `rust/compiler/src/codegen/llvm/backend_core.rs`
- **Expected Simple path**: `src/compiler/codegen/llvm/backend_core.spl` or `src/app/codegen/llvm/backend_core.spl`
- **Status**: ❌ Not migrated

### compiler/codegen/llvm/compiler
- **Rust path**: `rust/compiler/src/codegen/llvm/compiler.rs`
- **Expected Simple path**: `src/compiler/codegen/llvm/compiler.spl` or `src/app/codegen/llvm/compiler.spl`
- **Status**: ❌ Not migrated

### compiler/codegen/llvm/compiler_test_helpers
- **Rust path**: `rust/compiler/src/codegen/llvm/compiler_test_helpers.rs`
- **Expected Simple path**: `src/compiler/codegen/llvm/compiler_test_helpers.spl` or `src/app/codegen/llvm/compiler_test_helpers.spl`
- **Status**: ❌ Not migrated

### compiler/codegen/llvm/emitter
- **Rust path**: `rust/compiler/src/codegen/llvm/emitter.rs`
- **Expected Simple path**: `src/compiler/codegen/llvm/emitter.spl` or `src/app/codegen/llvm/emitter.spl`
- **Status**: ❌ Not migrated

### compiler/codegen/llvm/functions
- **Rust path**: `rust/compiler/src/codegen/llvm/functions.rs`
- **Expected Simple path**: `src/compiler/codegen/llvm/functions.spl` or `src/app/codegen/llvm/functions.spl`
- **Status**: ❌ Not migrated

### compiler/codegen/llvm/gpu
- **Rust path**: `rust/compiler/src/codegen/llvm/gpu.rs`
- **Expected Simple path**: `src/compiler/codegen/llvm/gpu.spl` or `src/app/codegen/llvm/gpu.spl`
- **Status**: ❌ Not migrated

### compiler/codegen/llvm/gpu_instructions
- **Rust path**: `rust/compiler/src/codegen/llvm/gpu_instructions.rs`
- **Expected Simple path**: `src/compiler/codegen/llvm/gpu_instructions.spl` or `src/app/codegen/llvm/gpu_instructions.spl`
- **Status**: ❌ Not migrated

### compiler/codegen/llvm/gpu_intrinsics
- **Rust path**: `rust/compiler/src/codegen/llvm/gpu_intrinsics.rs`
- **Expected Simple path**: `src/compiler/codegen/llvm/gpu_intrinsics.spl` or `src/app/codegen/llvm/gpu_intrinsics.spl`
- **Status**: ❌ Not migrated

### compiler/codegen/llvm/instructions
- **Rust path**: `rust/compiler/src/codegen/llvm/instructions.rs`
- **Expected Simple path**: `src/compiler/codegen/llvm/instructions.spl` or `src/app/codegen/llvm/instructions.spl`
- **Status**: ❌ Not migrated

### compiler/codegen/llvm/mod
- **Rust path**: `rust/compiler/src/codegen/llvm/mod.rs`
- **Expected Simple path**: `src/compiler/codegen/llvm/mod.spl` or `src/app/codegen/llvm/mod.spl`
- **Status**: ❌ Not migrated

### compiler/codegen/llvm/native_impl
- **Rust path**: `rust/compiler/src/codegen/llvm/native_impl.rs`
- **Expected Simple path**: `src/compiler/codegen/llvm/native_impl.spl` or `src/app/codegen/llvm/native_impl.spl`
- **Status**: ❌ Not migrated

### compiler/codegen/llvm/types
- **Rust path**: `rust/compiler/src/codegen/llvm/types.rs`
- **Expected Simple path**: `src/compiler/codegen/llvm/types.spl` or `src/app/codegen/llvm/types.spl`
- **Status**: ❌ Not migrated

### compiler/codegen/llvm/wasm_imports
- **Rust path**: `rust/compiler/src/codegen/llvm/wasm_imports.rs`
- **Expected Simple path**: `src/compiler/codegen/llvm/wasm_imports.spl` or `src/app/codegen/llvm/wasm_imports.spl`
- **Status**: ❌ Not migrated

### compiler/codegen/llvm/wasm_tests
- **Rust path**: `rust/compiler/src/codegen/llvm/wasm_tests.rs`
- **Expected Simple path**: `src/compiler/codegen/llvm/wasm_tests.spl` or `src/app/codegen/llvm/wasm_tests.spl`
- **Status**: ❌ Not migrated

### compiler/codegen/llvm/functions/calls
- **Rust path**: `rust/compiler/src/codegen/llvm/functions/calls.rs`
- **Expected Simple path**: `src/compiler/codegen/llvm/functions/calls.spl` or `src/app/codegen/llvm/functions/calls.spl`
- **Status**: ❌ Not migrated

### compiler/codegen/llvm/functions/casts
- **Rust path**: `rust/compiler/src/codegen/llvm/functions/casts.rs`
- **Expected Simple path**: `src/compiler/codegen/llvm/functions/casts.spl` or `src/app/codegen/llvm/functions/casts.spl`
- **Status**: ❌ Not migrated

### compiler/codegen/llvm/functions/collections
- **Rust path**: `rust/compiler/src/codegen/llvm/functions/collections.rs`
- **Expected Simple path**: `src/compiler/codegen/llvm/functions/collections.spl` or `src/app/codegen/llvm/functions/collections.spl`
- **Status**: ❌ Not migrated

### compiler/codegen/llvm/functions/consts
- **Rust path**: `rust/compiler/src/codegen/llvm/functions/consts.rs`
- **Expected Simple path**: `src/compiler/codegen/llvm/functions/consts.spl` or `src/app/codegen/llvm/functions/consts.spl`
- **Status**: ❌ Not migrated

### compiler/codegen/llvm/functions/memory
- **Rust path**: `rust/compiler/src/codegen/llvm/functions/memory.rs`
- **Expected Simple path**: `src/compiler/codegen/llvm/functions/memory.spl` or `src/app/codegen/llvm/functions/memory.spl`
- **Status**: ❌ Not migrated

### compiler/codegen/llvm/functions/objects
- **Rust path**: `rust/compiler/src/codegen/llvm/functions/objects.rs`
- **Expected Simple path**: `src/compiler/codegen/llvm/functions/objects.spl` or `src/app/codegen/llvm/functions/objects.spl`
- **Status**: ❌ Not migrated

### compiler/codegen/llvm_tests/backend_creation
- **Rust path**: `rust/compiler/src/codegen/llvm_tests/backend_creation.rs`
- **Expected Simple path**: `src/compiler/codegen/llvm_tests/backend_creation.spl` or `src/app/codegen/llvm_tests/backend_creation.spl`
- **Status**: ❌ Not migrated

### compiler/codegen/llvm_tests/binop
- **Rust path**: `rust/compiler/src/codegen/llvm_tests/binop.rs`
- **Expected Simple path**: `src/compiler/codegen/llvm_tests/binop.spl` or `src/app/codegen/llvm_tests/binop.spl`
- **Status**: ❌ Not migrated

### compiler/codegen/llvm_tests/compilation
- **Rust path**: `rust/compiler/src/codegen/llvm_tests/compilation.rs`
- **Expected Simple path**: `src/compiler/codegen/llvm_tests/compilation.spl` or `src/app/codegen/llvm_tests/compilation.spl`
- **Status**: ❌ Not migrated

### compiler/codegen/llvm_tests/control_flow
- **Rust path**: `rust/compiler/src/codegen/llvm_tests/control_flow.rs`
- **Expected Simple path**: `src/compiler/codegen/llvm_tests/control_flow.spl` or `src/app/codegen/llvm_tests/control_flow.spl`
- **Status**: ❌ Not migrated

### compiler/codegen/llvm_tests/function_compilation
- **Rust path**: `rust/compiler/src/codegen/llvm_tests/function_compilation.rs`
- **Expected Simple path**: `src/compiler/codegen/llvm_tests/function_compilation.spl` or `src/app/codegen/llvm_tests/function_compilation.spl`
- **Status**: ❌ Not migrated

### compiler/codegen/llvm_tests/helpers
- **Rust path**: `rust/compiler/src/codegen/llvm_tests/helpers.rs`
- **Expected Simple path**: `src/compiler/codegen/llvm_tests/helpers.spl` or `src/app/codegen/llvm_tests/helpers.spl`
- **Status**: ❌ Not migrated

### compiler/codegen/llvm_tests/ir_generation
- **Rust path**: `rust/compiler/src/codegen/llvm_tests/ir_generation.rs`
- **Expected Simple path**: `src/compiler/codegen/llvm_tests/ir_generation.spl` or `src/app/codegen/llvm_tests/ir_generation.spl`
- **Status**: ❌ Not migrated

### compiler/codegen/llvm_tests/mir_compilation
- **Rust path**: `rust/compiler/src/codegen/llvm_tests/mir_compilation.rs`
- **Expected Simple path**: `src/compiler/codegen/llvm_tests/mir_compilation.spl` or `src/app/codegen/llvm_tests/mir_compilation.spl`
- **Status**: ❌ Not migrated

### compiler/codegen/llvm_tests/mod
- **Rust path**: `rust/compiler/src/codegen/llvm_tests/mod.rs`
- **Expected Simple path**: `src/compiler/codegen/llvm_tests/mod.spl` or `src/app/codegen/llvm_tests/mod.spl`
- **Status**: ❌ Not migrated

### compiler/codegen/llvm_tests/object_emission
- **Rust path**: `rust/compiler/src/codegen/llvm_tests/object_emission.rs`
- **Expected Simple path**: `src/compiler/codegen/llvm_tests/object_emission.spl` or `src/app/codegen/llvm_tests/object_emission.spl`
- **Status**: ❌ Not migrated

### compiler/codegen/llvm_tests/type_mapping
- **Rust path**: `rust/compiler/src/codegen/llvm_tests/type_mapping.rs`
- **Expected Simple path**: `src/compiler/codegen/llvm_tests/type_mapping.spl` or `src/app/codegen/llvm_tests/type_mapping.spl`
- **Status**: ❌ Not migrated

### compiler/codegen/vulkan/backend
- **Rust path**: `rust/compiler/src/codegen/vulkan/backend.rs`
- **Expected Simple path**: `src/compiler/codegen/vulkan/backend.spl` or `src/app/codegen/vulkan/backend.spl`
- **Status**: ❌ Not migrated

### compiler/codegen/vulkan/emitter
- **Rust path**: `rust/compiler/src/codegen/vulkan/emitter.rs`
- **Expected Simple path**: `src/compiler/codegen/vulkan/emitter.spl` or `src/app/codegen/vulkan/emitter.spl`
- **Status**: ❌ Not migrated

### compiler/codegen/vulkan/instr_compute
- **Rust path**: `rust/compiler/src/codegen/vulkan/instr_compute.rs`
- **Expected Simple path**: `src/compiler/codegen/vulkan/instr_compute.spl` or `src/app/codegen/vulkan/instr_compute.spl`
- **Status**: ❌ Not migrated

### compiler/codegen/vulkan/instr_graphics
- **Rust path**: `rust/compiler/src/codegen/vulkan/instr_graphics.rs`
- **Expected Simple path**: `src/compiler/codegen/vulkan/instr_graphics.spl` or `src/app/codegen/vulkan/instr_graphics.spl`
- **Status**: ❌ Not migrated

### compiler/codegen/vulkan/mod
- **Rust path**: `rust/compiler/src/codegen/vulkan/mod.rs`
- **Expected Simple path**: `src/compiler/codegen/vulkan/mod.spl` or `src/app/codegen/vulkan/mod.spl`
- **Status**: ❌ Not migrated

### compiler/codegen/vulkan/spirv_builder
- **Rust path**: `rust/compiler/src/codegen/vulkan/spirv_builder.rs`
- **Expected Simple path**: `src/compiler/codegen/vulkan/spirv_builder.spl` or `src/app/codegen/vulkan/spirv_builder.spl`
- **Status**: ❌ Not migrated

### compiler/codegen/vulkan/spirv_instructions
- **Rust path**: `rust/compiler/src/codegen/vulkan/spirv_instructions.rs`
- **Expected Simple path**: `src/compiler/codegen/vulkan/spirv_instructions.spl` or `src/app/codegen/vulkan/spirv_instructions.spl`
- **Status**: ❌ Not migrated

### compiler/codegen/vulkan/types
- **Rust path**: `rust/compiler/src/codegen/vulkan/types.rs`
- **Expected Simple path**: `src/compiler/codegen/vulkan/types.spl` or `src/app/codegen/vulkan/types.spl`
- **Status**: ❌ Not migrated

### compiler/hir/arena
- **Rust path**: `rust/compiler/src/hir/arena.rs`
- **Expected Simple path**: `src/compiler/hir/arena.spl` or `src/app/hir/arena.spl`
- **Status**: ❌ Not migrated

### compiler/hir/capability
- **Rust path**: `rust/compiler/src/hir/capability.rs`
- **Expected Simple path**: `src/compiler/hir/capability.spl` or `src/app/hir/capability.spl`
- **Status**: ❌ Not migrated

### compiler/hir/gpu_intrinsics
- **Rust path**: `rust/compiler/src/hir/gpu_intrinsics.rs`
- **Expected Simple path**: `src/compiler/hir/gpu_intrinsics.spl` or `src/app/hir/gpu_intrinsics.spl`
- **Status**: ❌ Not migrated

### compiler/hir/lifetime
- **Rust path**: `rust/compiler/src/hir/lifetime.rs`
- **Expected Simple path**: `src/compiler/hir/lifetime.spl` or `src/app/hir/lifetime.spl`
- **Status**: ❌ Not migrated

### compiler/hir/memory_model
- **Rust path**: `rust/compiler/src/hir/memory_model.rs`
- **Expected Simple path**: `src/compiler/hir/memory_model.spl` or `src/app/hir/memory_model.spl`
- **Status**: ❌ Not migrated

### compiler/hir/mod
- **Rust path**: `rust/compiler/src/hir/mod.rs`
- **Expected Simple path**: `src/compiler/hir/mod.spl` or `src/app/hir/mod.spl`
- **Status**: ❌ Not migrated

### compiler/hir/operators
- **Rust path**: `rust/compiler/src/hir/operators.rs`
- **Expected Simple path**: `src/compiler/hir/operators.spl` or `src/app/hir/operators.spl`
- **Status**: ❌ Not migrated

### compiler/hir/type_registry
- **Rust path**: `rust/compiler/src/hir/type_registry.rs`
- **Expected Simple path**: `src/compiler/hir/type_registry.spl` or `src/app/hir/type_registry.spl`
- **Status**: ❌ Not migrated

### compiler/hir/analysis/ghost_checker
- **Rust path**: `rust/compiler/src/hir/analysis/ghost_checker.rs`
- **Expected Simple path**: `src/compiler/hir/analysis/ghost_checker.spl` or `src/app/hir/analysis/ghost_checker.spl`
- **Status**: ❌ Not migrated

### compiler/hir/analysis/mod
- **Rust path**: `rust/compiler/src/hir/analysis/mod.rs`
- **Expected Simple path**: `src/compiler/hir/analysis/mod.spl` or `src/app/hir/analysis/mod.spl`
- **Status**: ❌ Not migrated

### compiler/hir/lower/context
- **Rust path**: `rust/compiler/src/hir/lower/context.rs`
- **Expected Simple path**: `src/compiler/hir/lower/context.spl` or `src/app/hir/lower/context.spl`
- **Status**: ❌ Not migrated

### compiler/hir/lower/deprecation_warning
- **Rust path**: `rust/compiler/src/hir/lower/deprecation_warning.rs`
- **Expected Simple path**: `src/compiler/hir/lower/deprecation_warning.spl` or `src/app/hir/lower/deprecation_warning.spl`
- **Status**: ❌ Not migrated

### compiler/hir/lower/error
- **Rust path**: `rust/compiler/src/hir/lower/error.rs`
- **Expected Simple path**: `src/compiler/hir/lower/error.spl` or `src/app/hir/lower/error.spl`
- **Status**: ❌ Not migrated

### compiler/hir/lower/import_loader
- **Rust path**: `rust/compiler/src/hir/lower/import_loader.rs`
- **Expected Simple path**: `src/compiler/hir/lower/import_loader.spl` or `src/app/hir/lower/import_loader.spl`
- **Status**: ❌ Not migrated

### compiler/hir/lower/lowerer
- **Rust path**: `rust/compiler/src/hir/lower/lowerer.rs`
- **Expected Simple path**: `src/compiler/hir/lower/lowerer.spl` or `src/app/hir/lower/lowerer.spl`
- **Status**: ❌ Not migrated

### compiler/hir/lower/memory_check
- **Rust path**: `rust/compiler/src/hir/lower/memory_check.rs`
- **Expected Simple path**: `src/compiler/hir/lower/memory_check.spl` or `src/app/hir/lower/memory_check.spl`
- **Status**: ❌ Not migrated

### compiler/hir/lower/memory_warning
- **Rust path**: `rust/compiler/src/hir/lower/memory_warning.rs`
- **Expected Simple path**: `src/compiler/hir/lower/memory_warning.spl` or `src/app/hir/lower/memory_warning.spl`
- **Status**: ❌ Not migrated

### compiler/hir/lower/mod
- **Rust path**: `rust/compiler/src/hir/lower/mod.rs`
- **Expected Simple path**: `src/compiler/hir/lower/mod.spl` or `src/app/hir/lower/mod.spl`
- **Status**: ❌ Not migrated

### compiler/hir/lower/parallel
- **Rust path**: `rust/compiler/src/hir/lower/parallel.rs`
- **Expected Simple path**: `src/compiler/hir/lower/parallel.spl` or `src/app/hir/lower/parallel.spl`
- **Status**: ❌ Not migrated

### compiler/hir/lower/type_registration
- **Rust path**: `rust/compiler/src/hir/lower/type_registration.rs`
- **Expected Simple path**: `src/compiler/hir/lower/type_registration.spl` or `src/app/hir/lower/type_registration.spl`
- **Status**: ❌ Not migrated

### compiler/hir/lower/type_resolver
- **Rust path**: `rust/compiler/src/hir/lower/type_resolver.rs`
- **Expected Simple path**: `src/compiler/hir/lower/type_resolver.spl` or `src/app/hir/lower/type_resolver.spl`
- **Status**: ❌ Not migrated

### compiler/hir/lower/stmt_lowering
- **Rust path**: `rust/compiler/src/hir/lower/stmt_lowering.rs`
- **Expected Simple path**: `src/compiler/hir/lower/stmt_lowering.spl` or `src/app/hir/lower/stmt_lowering.spl`
- **Status**: ❌ Not migrated

### compiler/hir/lower/expr/access
- **Rust path**: `rust/compiler/src/hir/lower/expr/access.rs`
- **Expected Simple path**: `src/compiler/hir/lower/expr/access.spl` or `src/app/hir/lower/expr/access.spl`
- **Status**: ❌ Not migrated

### compiler/hir/lower/expr/calls
- **Rust path**: `rust/compiler/src/hir/lower/expr/calls.rs`
- **Expected Simple path**: `src/compiler/hir/lower/expr/calls.spl` or `src/app/hir/lower/expr/calls.spl`
- **Status**: ❌ Not migrated

### compiler/hir/lower/expr/collections
- **Rust path**: `rust/compiler/src/hir/lower/expr/collections.rs`
- **Expected Simple path**: `src/compiler/hir/lower/expr/collections.spl` or `src/app/hir/lower/expr/collections.spl`
- **Status**: ❌ Not migrated

### compiler/hir/lower/expr/contracts
- **Rust path**: `rust/compiler/src/hir/lower/expr/contracts.rs`
- **Expected Simple path**: `src/compiler/hir/lower/expr/contracts.spl` or `src/app/hir/lower/expr/contracts.spl`
- **Status**: ❌ Not migrated

### compiler/hir/lower/expr/control
- **Rust path**: `rust/compiler/src/hir/lower/expr/control.rs`
- **Expected Simple path**: `src/compiler/hir/lower/expr/control.spl` or `src/app/hir/lower/expr/control.spl`
- **Status**: ❌ Not migrated

### compiler/hir/lower/expr/helpers
- **Rust path**: `rust/compiler/src/hir/lower/expr/helpers.rs`
- **Expected Simple path**: `src/compiler/hir/lower/expr/helpers.spl` or `src/app/hir/lower/expr/helpers.spl`
- **Status**: ❌ Not migrated

### compiler/hir/lower/expr/inference
- **Rust path**: `rust/compiler/src/hir/lower/expr/inference.rs`
- **Expected Simple path**: `src/compiler/hir/lower/expr/inference.spl` or `src/app/hir/lower/expr/inference.spl`
- **Status**: ❌ Not migrated

### compiler/hir/lower/expr/literals
- **Rust path**: `rust/compiler/src/hir/lower/expr/literals.rs`
- **Expected Simple path**: `src/compiler/hir/lower/expr/literals.spl` or `src/app/hir/lower/expr/literals.spl`
- **Status**: ❌ Not migrated

### compiler/hir/lower/expr/memory
- **Rust path**: `rust/compiler/src/hir/lower/expr/memory.rs`
- **Expected Simple path**: `src/compiler/hir/lower/expr/memory.spl` or `src/app/hir/lower/expr/memory.spl`
- **Status**: ❌ Not migrated

### compiler/hir/lower/expr/mod
- **Rust path**: `rust/compiler/src/hir/lower/expr/mod.rs`
- **Expected Simple path**: `src/compiler/hir/lower/expr/mod.spl` or `src/app/hir/lower/expr/mod.spl`
- **Status**: ❌ Not migrated

### compiler/hir/lower/expr/operators
- **Rust path**: `rust/compiler/src/hir/lower/expr/operators.rs`
- **Expected Simple path**: `src/compiler/hir/lower/expr/operators.spl` or `src/app/hir/lower/expr/operators.spl`
- **Status**: ❌ Not migrated

### compiler/hir/lower/expr/simd
- **Rust path**: `rust/compiler/src/hir/lower/expr/simd.rs`
- **Expected Simple path**: `src/compiler/hir/lower/expr/simd.spl` or `src/app/hir/lower/expr/simd.spl`
- **Status**: ❌ Not migrated

### compiler/hir/lower/expr/tensor
- **Rust path**: `rust/compiler/src/hir/lower/expr/tensor.rs`
- **Expected Simple path**: `src/compiler/hir/lower/expr/tensor.spl` or `src/app/hir/lower/expr/tensor.spl`
- **Status**: ❌ Not migrated

### compiler/hir/lower/module_lowering/aop
- **Rust path**: `rust/compiler/src/hir/lower/module_lowering/aop.rs`
- **Expected Simple path**: `src/compiler/hir/lower/module_lowering/aop.spl` or `src/app/hir/lower/module_lowering/aop.spl`
- **Status**: ❌ Not migrated

### compiler/hir/lower/module_lowering/contract
- **Rust path**: `rust/compiler/src/hir/lower/module_lowering/contract.rs`
- **Expected Simple path**: `src/compiler/hir/lower/module_lowering/contract.spl` or `src/app/hir/lower/module_lowering/contract.spl`
- **Status**: ❌ Not migrated

### compiler/hir/lower/module_lowering/function
- **Rust path**: `rust/compiler/src/hir/lower/module_lowering/function.rs`
- **Expected Simple path**: `src/compiler/hir/lower/module_lowering/function.spl` or `src/app/hir/lower/module_lowering/function.spl`
- **Status**: ❌ Not migrated

### compiler/hir/lower/module_lowering/import
- **Rust path**: `rust/compiler/src/hir/lower/module_lowering/import.rs`
- **Expected Simple path**: `src/compiler/hir/lower/module_lowering/import.spl` or `src/app/hir/lower/module_lowering/import.spl`
- **Status**: ❌ Not migrated

### compiler/hir/lower/module_lowering/mock
- **Rust path**: `rust/compiler/src/hir/lower/module_lowering/mock.rs`
- **Expected Simple path**: `src/compiler/hir/lower/module_lowering/mock.spl` or `src/app/hir/lower/module_lowering/mock.spl`
- **Status**: ❌ Not migrated

### compiler/hir/lower/module_lowering/mod
- **Rust path**: `rust/compiler/src/hir/lower/module_lowering/mod.rs`
- **Expected Simple path**: `src/compiler/hir/lower/module_lowering/mod.spl` or `src/app/hir/lower/module_lowering/mod.spl`
- **Status**: ❌ Not migrated

### compiler/hir/lower/module_lowering/validation
- **Rust path**: `rust/compiler/src/hir/lower/module_lowering/validation.rs`
- **Expected Simple path**: `src/compiler/hir/lower/module_lowering/validation.spl` or `src/app/hir/lower/module_lowering/validation.spl`
- **Status**: ❌ Not migrated

### compiler/hir/lower/module_lowering/module_pass
- **Rust path**: `rust/compiler/src/hir/lower/module_lowering/module_pass.rs`
- **Expected Simple path**: `src/compiler/hir/lower/module_lowering/module_pass.spl` or `src/app/hir/lower/module_lowering/module_pass.spl`
- **Status**: ❌ Not migrated

### compiler/hir/types/aop
- **Rust path**: `rust/compiler/src/hir/types/aop.rs`
- **Expected Simple path**: `src/compiler/hir/types/aop.spl` or `src/app/hir/types/aop.spl`
- **Status**: ❌ Not migrated

### compiler/hir/types/code_layout
- **Rust path**: `rust/compiler/src/hir/types/code_layout.rs`
- **Expected Simple path**: `src/compiler/hir/types/code_layout.spl` or `src/app/hir/types/code_layout.spl`
- **Status**: ❌ Not migrated

### compiler/hir/types/contracts
- **Rust path**: `rust/compiler/src/hir/types/contracts.rs`
- **Expected Simple path**: `src/compiler/hir/types/contracts.spl` or `src/app/hir/types/contracts.spl`
- **Status**: ❌ Not migrated

### compiler/hir/types/expressions
- **Rust path**: `rust/compiler/src/hir/types/expressions.rs`
- **Expected Simple path**: `src/compiler/hir/types/expressions.spl` or `src/app/hir/types/expressions.spl`
- **Status**: ❌ Not migrated

### compiler/hir/types/functions
- **Rust path**: `rust/compiler/src/hir/types/functions.rs`
- **Expected Simple path**: `src/compiler/hir/types/functions.spl` or `src/app/hir/types/functions.spl`
- **Status**: ❌ Not migrated

### compiler/hir/types/layout
- **Rust path**: `rust/compiler/src/hir/types/layout.rs`
- **Expected Simple path**: `src/compiler/hir/types/layout.spl` or `src/app/hir/types/layout.spl`
- **Status**: ❌ Not migrated

### compiler/hir/types/layout_config
- **Rust path**: `rust/compiler/src/hir/types/layout_config.rs`
- **Expected Simple path**: `src/compiler/hir/types/layout_config.spl` or `src/app/hir/types/layout_config.spl`
- **Status**: ❌ Not migrated

### compiler/hir/types/mod
- **Rust path**: `rust/compiler/src/hir/types/mod.rs`
- **Expected Simple path**: `src/compiler/hir/types/mod.spl` or `src/app/hir/types/mod.spl`
- **Status**: ❌ Not migrated

### compiler/hir/types/module
- **Rust path**: `rust/compiler/src/hir/types/module.rs`
- **Expected Simple path**: `src/compiler/hir/types/module.spl` or `src/app/hir/types/module.spl`
- **Status**: ❌ Not migrated

### compiler/hir/types/statements
- **Rust path**: `rust/compiler/src/hir/types/statements.rs`
- **Expected Simple path**: `src/compiler/hir/types/statements.spl` or `src/app/hir/types/statements.spl`
- **Status**: ❌ Not migrated

### compiler/hir/types/type_system
- **Rust path**: `rust/compiler/src/hir/types/type_system.rs`
- **Expected Simple path**: `src/compiler/hir/types/type_system.spl` or `src/app/hir/types/type_system.spl`
- **Status**: ❌ Not migrated

### compiler/hir/types/verification
- **Rust path**: `rust/compiler/src/hir/types/verification.rs`
- **Expected Simple path**: `src/compiler/hir/types/verification.spl` or `src/app/hir/types/verification.spl`
- **Status**: ❌ Not migrated

### compiler/mir/arena
- **Rust path**: `rust/compiler/src/mir/arena.rs`
- **Expected Simple path**: `src/compiler/mir/arena.spl` or `src/app/mir/arena.spl`
- **Status**: ❌ Not migrated

### compiler/mir/async_sm
- **Rust path**: `rust/compiler/src/mir/async_sm.rs`
- **Expected Simple path**: `src/compiler/mir/async_sm.spl` or `src/app/mir/async_sm.spl`
- **Status**: ❌ Not migrated

### compiler/mir/blocks
- **Rust path**: `rust/compiler/src/mir/blocks.rs`
- **Expected Simple path**: `src/compiler/mir/blocks.spl` or `src/app/mir/blocks.spl`
- **Status**: ❌ Not migrated

### compiler/mir/effects
- **Rust path**: `rust/compiler/src/mir/effects.rs`
- **Expected Simple path**: `src/compiler/mir/effects.spl` or `src/app/mir/effects.spl`
- **Status**: ❌ Not migrated

### compiler/mir/function
- **Rust path**: `rust/compiler/src/mir/function.rs`
- **Expected Simple path**: `src/compiler/mir/function.spl` or `src/app/mir/function.spl`
- **Status**: ❌ Not migrated

### compiler/mir/generator
- **Rust path**: `rust/compiler/src/mir/generator.rs`
- **Expected Simple path**: `src/compiler/mir/generator.spl` or `src/app/mir/generator.spl`
- **Status**: ❌ Not migrated

### compiler/mir/ghost_erasure
- **Rust path**: `rust/compiler/src/mir/ghost_erasure.rs`
- **Expected Simple path**: `src/compiler/mir/ghost_erasure.spl` or `src/app/mir/ghost_erasure.spl`
- **Status**: ❌ Not migrated

### compiler/mir/hybrid
- **Rust path**: `rust/compiler/src/mir/hybrid.rs`
- **Expected Simple path**: `src/compiler/mir/hybrid.spl` or `src/app/mir/hybrid.spl`
- **Status**: ❌ Not migrated

### compiler/mir/inst_effects
- **Rust path**: `rust/compiler/src/mir/inst_effects.rs`
- **Expected Simple path**: `src/compiler/mir/inst_effects.spl` or `src/app/mir/inst_effects.spl`
- **Status**: ❌ Not migrated

### compiler/mir/inst_enum
- **Rust path**: `rust/compiler/src/mir/inst_enum.rs`
- **Expected Simple path**: `src/compiler/mir/inst_enum.spl` or `src/app/mir/inst_enum.spl`
- **Status**: ❌ Not migrated

### compiler/mir/inst_helpers
- **Rust path**: `rust/compiler/src/mir/inst_helpers.rs`
- **Expected Simple path**: `src/compiler/mir/inst_helpers.spl` or `src/app/mir/inst_helpers.spl`
- **Status**: ❌ Not migrated

### compiler/mir/inst_types
- **Rust path**: `rust/compiler/src/mir/inst_types.rs`
- **Expected Simple path**: `src/compiler/mir/inst_types.spl` or `src/app/mir/inst_types.spl`
- **Status**: ❌ Not migrated

### compiler/mir/instructions
- **Rust path**: `rust/compiler/src/mir/instructions.rs`
- **Expected Simple path**: `src/compiler/mir/instructions.spl` or `src/app/mir/instructions.spl`
- **Status**: ❌ Not migrated

### compiler/mir/lower_contract
- **Rust path**: `rust/compiler/src/mir/lower_contract.rs`
- **Expected Simple path**: `src/compiler/mir/lower_contract.spl` or `src/app/mir/lower_contract.spl`
- **Status**: ❌ Not migrated

### compiler/mir/mod
- **Rust path**: `rust/compiler/src/mir/mod.rs`
- **Expected Simple path**: `src/compiler/mir/mod.spl` or `src/app/mir/mod.spl`
- **Status**: ❌ Not migrated

### compiler/mir/parallel
- **Rust path**: `rust/compiler/src/mir/parallel.rs`
- **Expected Simple path**: `src/compiler/mir/parallel.spl` or `src/app/mir/parallel.spl`
- **Status**: ❌ Not migrated

### compiler/mir/state_machine_utils
- **Rust path**: `rust/compiler/src/mir/state_machine_utils.rs`
- **Expected Simple path**: `src/compiler/mir/state_machine_utils.spl` or `src/app/mir/state_machine_utils.spl`
- **Status**: ❌ Not migrated

### compiler/mir/lower/lowering_contracts
- **Rust path**: `rust/compiler/src/mir/lower/lowering_contracts.rs`
- **Expected Simple path**: `src/compiler/mir/lower/lowering_contracts.spl` or `src/app/mir/lower/lowering_contracts.spl`
- **Status**: ❌ Not migrated

### compiler/mir/lower/lowering_core
- **Rust path**: `rust/compiler/src/mir/lower/lowering_core.rs`
- **Expected Simple path**: `src/compiler/mir/lower/lowering_core.spl` or `src/app/mir/lower/lowering_core.spl`
- **Status**: ❌ Not migrated

### compiler/mir/lower/lowering_coverage
- **Rust path**: `rust/compiler/src/mir/lower/lowering_coverage.rs`
- **Expected Simple path**: `src/compiler/mir/lower/lowering_coverage.spl` or `src/app/mir/lower/lowering_coverage.spl`
- **Status**: ❌ Not migrated

### compiler/mir/lower/lowering_di
- **Rust path**: `rust/compiler/src/mir/lower/lowering_di.rs`
- **Expected Simple path**: `src/compiler/mir/lower/lowering_di.spl` or `src/app/mir/lower/lowering_di.spl`
- **Status**: ❌ Not migrated

### compiler/mir/lower/lowering_expr
- **Rust path**: `rust/compiler/src/mir/lower/lowering_expr.rs`
- **Expected Simple path**: `src/compiler/mir/lower/lowering_expr.spl` or `src/app/mir/lower/lowering_expr.spl`
- **Status**: ❌ Not migrated

### compiler/mir/lower/lowering_gpu
- **Rust path**: `rust/compiler/src/mir/lower/lowering_gpu.rs`
- **Expected Simple path**: `src/compiler/mir/lower/lowering_gpu.spl` or `src/app/mir/lower/lowering_gpu.spl`
- **Status**: ❌ Not migrated

### compiler/mir/lower/lowering_stmt
- **Rust path**: `rust/compiler/src/mir/lower/lowering_stmt.rs`
- **Expected Simple path**: `src/compiler/mir/lower/lowering_stmt.spl` or `src/app/mir/lower/lowering_stmt.spl`
- **Status**: ❌ Not migrated

### compiler/mir/lower/lowering_types
- **Rust path**: `rust/compiler/src/mir/lower/lowering_types.rs`
- **Expected Simple path**: `src/compiler/mir/lower/lowering_types.spl` or `src/app/mir/lower/lowering_types.spl`
- **Status**: ❌ Not migrated

### compiler/mir/lower/mod
- **Rust path**: `rust/compiler/src/mir/lower/mod.rs`
- **Expected Simple path**: `src/compiler/mir/lower/mod.spl` or `src/app/mir/lower/mod.spl`
- **Status**: ❌ Not migrated

### parser/ast/aop
- **Rust path**: `rust/parser/src/ast/aop.rs`
- **Expected Simple path**: `src/compiler/ast/aop.spl` or `src/app/ast/aop.spl`
- **Status**: ❌ Not migrated

### parser/ast/enums
- **Rust path**: `rust/parser/src/ast/enums.rs`
- **Expected Simple path**: `src/compiler/ast/enums.spl` or `src/app/ast/enums.spl`
- **Status**: ❌ Not migrated

### parser/ast/ffi
- **Rust path**: `rust/parser/src/ast/ffi.rs`
- **Expected Simple path**: `src/compiler/ast/ffi.spl` or `src/app/ast/ffi.spl`
- **Status**: ❌ Not migrated

### parser/ast/mod
- **Rust path**: `rust/parser/src/ast/mod.rs`
- **Expected Simple path**: `src/compiler/ast/mod.spl` or `src/app/ast/mod.spl`
- **Status**: ❌ Not migrated

### parser/ast/nodes_units
- **Rust path**: `rust/parser/src/ast/nodes_units.rs`
- **Expected Simple path**: `src/compiler/ast/nodes_units.spl` or `src/app/ast/nodes_units.spl`
- **Status**: ❌ Not migrated

### parser/ast/tests
- **Rust path**: `rust/parser/src/ast/tests.rs`
- **Expected Simple path**: `src/compiler/ast/tests.spl` or `src/app/ast/tests.spl`
- **Status**: ❌ Not migrated

### parser/ast/nodes/const_meta
- **Rust path**: `rust/parser/src/ast/nodes/const_meta.rs`
- **Expected Simple path**: `src/compiler/ast/nodes/const_meta.spl` or `src/app/ast/nodes/const_meta.spl`
- **Status**: ❌ Not migrated

### parser/ast/nodes/contracts
- **Rust path**: `rust/parser/src/ast/nodes/contracts.rs`
- **Expected Simple path**: `src/compiler/ast/nodes/contracts.spl` or `src/app/ast/nodes/contracts.spl`
- **Status**: ❌ Not migrated

### parser/ast/nodes/effects
- **Rust path**: `rust/parser/src/ast/nodes/effects.rs`
- **Expected Simple path**: `src/compiler/ast/nodes/effects.spl` or `src/app/ast/nodes/effects.spl`
- **Status**: ❌ Not migrated

### parser/ast/nodes/mod
- **Rust path**: `rust/parser/src/ast/nodes/mod.rs`
- **Expected Simple path**: `src/compiler/ast/nodes/mod.spl` or `src/app/ast/nodes/mod.spl`
- **Status**: ❌ Not migrated

### parser/ast/nodes/test_meta
- **Rust path**: `rust/parser/src/ast/nodes/test_meta.rs`
- **Expected Simple path**: `src/compiler/ast/nodes/test_meta.spl` or `src/app/ast/nodes/test_meta.spl`
- **Status**: ❌ Not migrated

### parser/ast/nodes/core
- **Rust path**: `rust/parser/src/ast/nodes/core.rs`
- **Expected Simple path**: `src/compiler/ast/nodes/core.spl` or `src/app/ast/nodes/core.spl`
- **Status**: ❌ Not migrated

### parser/ast/nodes/modules
- **Rust path**: `rust/parser/src/ast/nodes/modules.rs`
- **Expected Simple path**: `src/compiler/ast/nodes/modules.spl` or `src/app/ast/nodes/modules.spl`
- **Status**: ❌ Not migrated

### parser/ast/nodes/definitions
- **Rust path**: `rust/parser/src/ast/nodes/definitions.rs`
- **Expected Simple path**: `src/compiler/ast/nodes/definitions.spl` or `src/app/ast/nodes/definitions.spl`
- **Status**: ❌ Not migrated

### parser/ast/nodes/statements
- **Rust path**: `rust/parser/src/ast/nodes/statements.rs`
- **Expected Simple path**: `src/compiler/ast/nodes/statements.spl` or `src/app/ast/nodes/statements.spl`
- **Status**: ❌ Not migrated

### parser/lexer/comments
- **Rust path**: `rust/parser/src/lexer/comments.rs`
- **Expected Simple path**: `src/compiler/lexer/comments.spl` or `src/app/lexer/comments.spl`
- **Status**: ❌ Not migrated

### parser/lexer/escapes
- **Rust path**: `rust/parser/src/lexer/escapes.rs`
- **Expected Simple path**: `src/compiler/lexer/escapes.spl` or `src/app/lexer/escapes.spl`
- **Status**: ❌ Not migrated

### parser/lexer/i18n
- **Rust path**: `rust/parser/src/lexer/i18n.rs`
- **Expected Simple path**: `src/compiler/lexer/i18n.spl` or `src/app/lexer/i18n.spl`
- **Status**: ❌ Not migrated

### parser/lexer/indentation
- **Rust path**: `rust/parser/src/lexer/indentation.rs`
- **Expected Simple path**: `src/compiler/lexer/indentation.spl` or `src/app/lexer/indentation.spl`
- **Status**: ❌ Not migrated

### parser/lexer/mod
- **Rust path**: `rust/parser/src/lexer/mod.rs`
- **Expected Simple path**: `src/compiler/lexer/mod.spl` or `src/app/lexer/mod.spl`
- **Status**: ❌ Not migrated

### parser/lexer/numbers
- **Rust path**: `rust/parser/src/lexer/numbers.rs`
- **Expected Simple path**: `src/compiler/lexer/numbers.spl` or `src/app/lexer/numbers.spl`
- **Status**: ❌ Not migrated

### parser/lexer/strings
- **Rust path**: `rust/parser/src/lexer/strings.rs`
- **Expected Simple path**: `src/compiler/lexer/strings.spl` or `src/app/lexer/strings.spl`
- **Status**: ❌ Not migrated

### parser/lexer/identifiers
- **Rust path**: `rust/parser/src/lexer/identifiers.rs`
- **Expected Simple path**: `src/compiler/lexer/identifiers.spl` or `src/app/lexer/identifiers.spl`
- **Status**: ❌ Not migrated

## Needs Review

- ❌ `common/file_reader` → `rust/common/src/file_reader.rs`
- ❌ `common/actor` → `rust/common/src/actor.rs`
- ❌ `common/config_env` → `rust/common/src/config_env.rs`
- ❌ `common/manual` → `rust/common/src/manual.rs`
- ❌ `common/manual_mem` → `rust/common/src/manual_mem.rs`
- ❌ `common/target` → `rust/common/src/target.rs`
- ❌ `common/safety_macros` → `rust/common/src/safety_macros.rs`
- ❌ `common/safety` → `rust/common/src/safety.rs`
- ❌ `common/diagnostic` → `rust/common/src/diagnostic.rs`
- ❌ `common/fix_applicator` → `rust/common/src/fix_applicator.rs`
- ❌ `common/easy_fix_rules` → `rust/common/src/easy_fix_rules.rs`
- ❌ `common/runtime_symbols` → `rust/common/src/runtime_symbols.rs`
- ❌ `common/protocol/mod` → `rust/common/src/protocol/mod.rs`
- ❌ `common/protocol/transport` → `rust/common/src/protocol/transport.rs`
- ❌ `common/safety_examples` → `rust/common/examples/safety_examples.rs`
- ❌ `compiler/aop_config` → `rust/compiler/src/aop_config.rs`
- ✅ `compiler/api_surface` → `rust/compiler/src/api_surface.rs`
  - Simple: `src/compiler/api_surface.spl`
- ✅ `compiler/arch_rules` → `rust/compiler/src/arch_rules.rs`
  - Simple: `src/compiler/arch_rules.spl`
- ✅ `compiler/build_log` → `rust/compiler/src/build_log.rs`
  - Simple: `src/compiler/build_log.spl`
- ✅ `compiler/build_mode` → `rust/compiler/src/build_mode.rs`
  - Simple: `src/compiler/build_mode.spl`
- ✅ `compiler/compilation_context` → `rust/compiler/src/compilation_context.rs`
  - Simple: `src/compiler/compilation_context.spl`
- ✅ `compiler/context_pack` → `rust/compiler/src/context_pack.rs`
  - Simple: `src/compiler/context_pack.spl`
- ✅ `compiler/di` → `rust/compiler/src/di.rs`
  - Simple: `src/compiler/di.spl`
- ✅ `compiler/effects` → `rust/compiler/src/effects.rs`
  - Simple: `src/compiler/effects.spl`
- ✅ `compiler/effects_cache` → `rust/compiler/src/effects_cache.rs`
  - Simple: `src/compiler/effects_cache.spl`
- ✅ `compiler/error_explanations` → `rust/compiler/src/error_explanations.rs`
  - Simple: `src/compiler/error_explanations.spl`
- ❌ `compiler/extern_registry` → `rust/compiler/src/extern_registry.rs`
- ❌ `compiler/formatter` → `rust/compiler/src/formatter.rs`
- ✅ `compiler/hydration_manifest` → `rust/compiler/src/hydration_manifest.rs`
  - Simple: `src/compiler/hydration_manifest.spl`
- ❌ `compiler/import_loader` → `rust/compiler/src/import_loader.rs`
- ✅ `compiler/incremental` → `rust/compiler/src/incremental.rs`
  - Simple: `src/compiler/incremental.spl`
- ✅ `compiler/incremental_builder` → `rust/compiler/src/incremental_builder.rs`
  - Simple: `src/compiler/incremental_builder.spl`
- ❌ `compiler/interpreter_context` → `rust/compiler/src/interpreter_context.rs`
- ❌ `compiler/interpreter_contract` → `rust/compiler/src/interpreter_contract.rs`
- ❌ `compiler/interpreter_debug` → `rust/compiler/src/interpreter_debug.rs`
- ❌ `compiler/interpreter_helpers_option_result` → `rust/compiler/src/interpreter_helpers_option_result.rs`
- ❌ `compiler/interpreter_macro_invocation` → `rust/compiler/src/interpreter_macro_invocation.rs`
- ❌ `compiler/interpreter_state` → `rust/compiler/src/interpreter_state.rs`
- ❌ `compiler/interpreter_unit` → `rust/compiler/src/interpreter_unit.rs`
- ❌ `compiler/interpreter_utils` → `rust/compiler/src/interpreter_utils.rs`
- ❌ `compiler/ir_export` → `rust/compiler/src/ir_export.rs`
- ✅ `compiler/layout_recorder` → `rust/compiler/src/layout_recorder.rs`
  - Simple: `src/compiler/layout_recorder.spl`
- ✅ `compiler/macro_validation` → `rust/compiler/src/macro_validation.rs`
  - Simple: `src/compiler/macro_validation.spl`
- ❌ `compiler/mock` → `rust/compiler/src/mock.rs`
- ✅ `compiler/parallel` → `rust/compiler/src/parallel.rs`
  - Simple: `src/compiler/parallel.spl`
- ✅ `compiler/pattern_analysis` → `rust/compiler/src/pattern_analysis.rs`
  - Simple: `src/compiler/pattern_analysis.spl`
- ❌ `compiler/pipeline_parallel` → `rust/compiler/src/pipeline_parallel.rs`
- ✅ `compiler/predicate` → `rust/compiler/src/predicate.rs`
  - Simple: `src/compiler/predicate.spl`
- ✅ `compiler/predicate_parser` → `rust/compiler/src/predicate_parser.rs`
  - Simple: `src/compiler/predicate_parser.spl`
- ❌ `compiler/runtime_bridge` → `rust/compiler/src/runtime_bridge.rs`
- ❌ `compiler/smf_builder` → `rust/compiler/src/smf_builder.rs`
- ✅ `compiler/smf_writer` → `rust/compiler/src/smf_writer.rs`
  - Simple: `src/compiler/smf_writer.spl`
- ❌ `compiler/spec_coverage` → `rust/compiler/src/spec_coverage.rs`
- ✅ `compiler/symbol_analyzer` → `rust/compiler/src/symbol_analyzer.rs`
  - Simple: `src/compiler/symbol_analyzer.spl`
- ✅ `compiler/text_diff` → `rust/compiler/src/text_diff.rs`
  - Simple: `src/compiler/text_diff.spl`
- ❌ `compiler/type_inference_config` → `rust/compiler/src/type_inference_config.rs`
- ❌ `compiler/value_async` → `rust/compiler/src/value_async.rs`
- ✅ `compiler/verification_checker` → `rust/compiler/src/verification_checker.rs`
  - Simple: `src/compiler/verification_checker.spl`
- ❌ `compiler/web_compiler` → `rust/compiler/src/web_compiler.rs`
- ✅ `compiler/pretty_printer` → `rust/compiler/src/pretty_printer.rs`
  - Simple: `src/compiler/pretty_printer.spl`
- ❌ `compiler/value` → `rust/compiler/src/value.rs`
- ❌ `compiler/value_pointers` → `rust/compiler/src/value_pointers.rs`
- ❌ `compiler/value_bridge` → `rust/compiler/src/value_bridge.rs`
- ❌ `compiler/error` → `rust/compiler/src/error.rs`
- ❌ `compiler/interpreter_patterns` → `rust/compiler/src/interpreter_patterns.rs`
- ❌ `compiler/value_mock` → `rust/compiler/src/value_mock.rs`
- ✅ `compiler/macro_contracts` → `rust/compiler/src/macro_contracts.rs`
  - Simple: `src/compiler/macro_contracts.spl`
- ❌ `compiler/value_impl` → `rust/compiler/src/value_impl.rs`
- ❌ `compiler/module_cache` → `rust/compiler/src/module_cache.rs`
- ✅ `compiler/semantic_diff` → `rust/compiler/src/semantic_diff.rs`
  - Simple: `src/compiler/semantic_diff.spl`
- ❌ `compiler/mcp` → `rust/compiler/src/mcp.rs`
- ❌ `compiler/repl_runner` → `rust/compiler/src/repl_runner.rs`
- ✅ `compiler/trait_coherence` → `rust/compiler/src/trait_coherence.rs`
  - Simple: `src/compiler/trait_coherence.spl`
- ❌ `compiler/interpreter_types` → `rust/compiler/src/interpreter_types.rs`
- ❌ `compiler/elf_utils` → `rust/compiler/src/elf_utils.rs`
- ✅ `compiler/project` → `rust/compiler/src/project.rs`
  - Simple: `src/compiler/project.spl`
- ✅ `compiler/coverage` → `rust/compiler/src/coverage.rs`
  - Simple: `src/compiler/coverage.spl`
- ❌ `compiler/interpreter_control` → `rust/compiler/src/interpreter_control.rs`
- ✅ `compiler/compilability` → `rust/compiler/src/compilability.rs`
  - Simple: `src/compiler/compilability.spl`
- ❌ `compiler/watchdog` → `rust/compiler/src/watchdog.rs`
- ❌ `compiler/interpreter_eval` → `rust/compiler/src/interpreter_eval.rs`
- ❌ `compiler/aop/error` → `rust/compiler/src/aop/error.rs`
- ❌ `compiler/aop/matcher` → `rust/compiler/src/aop/matcher.rs`
- ❌ `compiler/aop/mod` → `rust/compiler/src/aop/mod.rs`
- ❌ `compiler/aop/registry` → `rust/compiler/src/aop/registry.rs`
- ❌ `compiler/aop/selector` → `rust/compiler/src/aop/selector.rs`
- ❌ `compiler/aop/validate` → `rust/compiler/src/aop/validate.rs`
- ❌ `compiler/aop/weaver` → `rust/compiler/src/aop/weaver.rs`
- ❌ `compiler/blocks/regex` → `rust/compiler/src/blocks/regex.rs`
- ❌ `compiler/blocks/shell` → `rust/compiler/src/blocks/shell.rs`
- ❌ `compiler/blocks/sql` → `rust/compiler/src/blocks/sql.rs`
- ❌ `compiler/blocks/render_mode` → `rust/compiler/src/blocks/render_mode.rs`
- ✅ `compiler/blocks/mod` → `rust/compiler/src/blocks/mod.rs`
  - Simple: `src/compiler/blocks/mod.spl`
- ❌ `compiler/blocks/math/lexer` → `rust/compiler/src/blocks/math/lexer.rs`
- ❌ `compiler/blocks/math/parser` → `rust/compiler/src/blocks/math/parser.rs`
- ❌ `compiler/blocks/math/ast` → `rust/compiler/src/blocks/math/ast.rs`
- ❌ `compiler/blocks/math/mod` → `rust/compiler/src/blocks/math/mod.rs`
- ❌ `compiler/blocks/math/eval/binders` → `rust/compiler/src/blocks/math/eval/binders.rs`
- ❌ `compiler/blocks/math/eval/core_ops` → `rust/compiler/src/blocks/math/eval/core_ops.rs`
- ❌ `compiler/blocks/math/eval/standard_math` → `rust/compiler/src/blocks/math/eval/standard_math.rs`
- ❌ `compiler/blocks/math/eval/tensor_functions` → `rust/compiler/src/blocks/math/eval/tensor_functions.rs`
- ❌ `compiler/blocks/math/eval/tensor_broadcasting` → `rust/compiler/src/blocks/math/eval/tensor_broadcasting.rs`
- ❌ `compiler/blocks/math/eval/mod` → `rust/compiler/src/blocks/math/eval/mod.rs`
- ❌ `compiler/blocks/math/tensor/broadcast` → `rust/compiler/src/blocks/math/tensor/broadcast.rs`
- ❌ `compiler/blocks/math/tensor/core` → `rust/compiler/src/blocks/math/tensor/core.rs`
- ❌ `compiler/blocks/math/tensor/creation` → `rust/compiler/src/blocks/math/tensor/creation.rs`
- ❌ `compiler/blocks/math/tensor/elementwise` → `rust/compiler/src/blocks/math/tensor/elementwise.rs`
- ❌ `compiler/blocks/math/tensor/indexing` → `rust/compiler/src/blocks/math/tensor/indexing.rs`
- ❌ `compiler/blocks/math/tensor/matrix` → `rust/compiler/src/blocks/math/tensor/matrix.rs`
- ❌ `compiler/blocks/math/tensor/mod` → `rust/compiler/src/blocks/math/tensor/mod.rs`
- ❌ `compiler/blocks/math/tensor/reduction` → `rust/compiler/src/blocks/math/tensor/reduction.rs`
- ❌ `compiler/blocks/math/rendering/mod` → `rust/compiler/src/blocks/math/rendering/mod.rs`
- ❌ `compiler/blocks/math/rendering/mathml` → `rust/compiler/src/blocks/math/rendering/mathml.rs`
- ❌ `compiler/blocks/math/rendering/unicode_text` → `rust/compiler/src/blocks/math/rendering/unicode_text.rs`
- ❌ `compiler/blocks/math/rendering/lean` → `rust/compiler/src/blocks/math/rendering/lean.rs`
- ❌ `compiler/blocks/math/backend/auto_select` → `rust/compiler/src/blocks/math/backend/auto_select.rs`
- ❌ `compiler/blocks/math/backend/torch_eval` → `rust/compiler/src/blocks/math/backend/torch_eval.rs`
- ❌ `compiler/blocks/math/backend/mod` → `rust/compiler/src/blocks/math/backend/mod.rs`
- ❌ `compiler/blocks/math/backend/cuda_eval` → `rust/compiler/src/blocks/math/backend/cuda_eval.rs`
- ❌ `compiler/concurrent_providers/mod` → `rust/compiler/src/concurrent_providers/mod.rs`
- ❌ `compiler/concurrent_providers/registry` → `rust/compiler/src/concurrent_providers/registry.rs`
- ❌ `compiler/concurrent_providers/std_impl` → `rust/compiler/src/concurrent_providers/std_impl.rs`
- ❌ `compiler/i18n/locale` → `rust/compiler/src/i18n/locale.rs`
- ❌ `compiler/i18n/mod` → `rust/compiler/src/i18n/mod.rs`
- ❌ `compiler/i18n/registry` → `rust/compiler/src/i18n/registry.rs`
- ❌ `compiler/i18n/extractor` → `rust/compiler/src/i18n/extractor.rs`
- ❌ `compiler/interpreter/async_support` → `rust/compiler/src/interpreter/async_support.rs`
- ❌ `compiler/interpreter/block_exec` → `rust/compiler/src/interpreter/block_exec.rs`
- ❌ `compiler/interpreter/core_types` → `rust/compiler/src/interpreter/core_types.rs`
- ❌ `compiler/interpreter/coverage_helpers` → `rust/compiler/src/interpreter/coverage_helpers.rs`
- ❌ `compiler/interpreter/error_macros` → `rust/compiler/src/interpreter/error_macros.rs`
- ❌ `compiler/interpreter/public_api` → `rust/compiler/src/interpreter/public_api.rs`
- ❌ `compiler/interpreter/node_exec` → `rust/compiler/src/interpreter/node_exec.rs`
- ❌ `compiler/interpreter/expr` → `rust/compiler/src/interpreter/expr.rs`
- ❌ `compiler/interpreter/mod` → `rust/compiler/src/interpreter/mod.rs`
- ❌ `compiler/interpreter/expr/casting` → `rust/compiler/src/interpreter/expr/casting.rs`
- ❌ `compiler/interpreter/expr/control` → `rust/compiler/src/interpreter/expr/control.rs`
- ❌ `compiler/interpreter/expr/units` → `rust/compiler/src/interpreter/expr/units.rs`
- ✅ `compiler/interpreter/expr/literals` → `rust/compiler/src/interpreter/expr/literals.rs`
  - Simple: `src/app/interpreter/expr/literals.spl`
- ❌ `compiler/interpreter/expr/ops` → `rust/compiler/src/interpreter/expr/ops.rs`
- ✅ `compiler/interpreter/expr/collections` → `rust/compiler/src/interpreter/expr/collections.rs`
  - Simple: `src/app/interpreter/expr/collections.spl`
- ✅ `compiler/interpreter/expr/calls` → `rust/compiler/src/interpreter/expr/calls.rs`
  - Simple: `src/app/interpreter/expr/calls.spl`
- ❌ `compiler/interpreter/macros/mod` → `rust/compiler/src/interpreter/macros/mod.rs`
- ❌ `compiler/interpreter_call/mock` → `rust/compiler/src/interpreter_call/mock.rs`
- ❌ `compiler/interpreter_call/builtins` → `rust/compiler/src/interpreter_call/builtins.rs`
- ❌ `compiler/interpreter_call/block_execution` → `rust/compiler/src/interpreter_call/block_execution.rs`
- ❌ `compiler/interpreter_call/bdd` → `rust/compiler/src/interpreter_call/bdd.rs`
- ❌ `compiler/interpreter_call/mod` → `rust/compiler/src/interpreter_call/mod.rs`
- ❌ `compiler/interpreter_call/core/aop_advice` → `rust/compiler/src/interpreter_call/core/aop_advice.rs`
- ❌ `compiler/interpreter_call/core/arg_eval` → `rust/compiler/src/interpreter_call/core/arg_eval.rs`
- ❌ `compiler/interpreter_call/core/async_support` → `rust/compiler/src/interpreter_call/core/async_support.rs`
- ❌ `compiler/interpreter_call/core/class_instantiation` → `rust/compiler/src/interpreter_call/core/class_instantiation.rs`
- ❌ `compiler/interpreter_call/core/di_injection` → `rust/compiler/src/interpreter_call/core/di_injection.rs`
- ❌ `compiler/interpreter_call/core/lambda` → `rust/compiler/src/interpreter_call/core/lambda.rs`
- ❌ `compiler/interpreter_call/core/macros` → `rust/compiler/src/interpreter_call/core/macros.rs`
- ❌ `compiler/interpreter_call/core/mod` → `rust/compiler/src/interpreter_call/core/mod.rs`
- ❌ `compiler/interpreter_call/core/arg_binding` → `rust/compiler/src/interpreter_call/core/arg_binding.rs`
- ❌ `compiler/interpreter_call/core/function_exec` → `rust/compiler/src/interpreter_call/core/function_exec.rs`
- ❌ `compiler/interpreter_extern/atomic` → `rust/compiler/src/interpreter_extern/atomic.rs`
- ❌ `compiler/interpreter_extern/collections` → `rust/compiler/src/interpreter_extern/collections.rs`
- ❌ `compiler/interpreter_extern/concurrency` → `rust/compiler/src/interpreter_extern/concurrency.rs`
- ❌ `compiler/interpreter_extern/conversion` → `rust/compiler/src/interpreter_extern/conversion.rs`
- ❌ `compiler/interpreter_extern/coverage` → `rust/compiler/src/interpreter_extern/coverage.rs`
- ❌ `compiler/interpreter_extern/cranelift` → `rust/compiler/src/interpreter_extern/cranelift.rs`
- ❌ `compiler/interpreter_extern/diagram` → `rust/compiler/src/interpreter_extern/diagram.rs`
- ❌ `compiler/interpreter_extern/filesystem` → `rust/compiler/src/interpreter_extern/filesystem.rs`
- ❌ `compiler/interpreter_extern/gpu` → `rust/compiler/src/interpreter_extern/gpu.rs`
- ❌ `compiler/interpreter_extern/i18n` → `rust/compiler/src/interpreter_extern/i18n.rs`
- ❌ `compiler/interpreter_extern/layout` → `rust/compiler/src/interpreter_extern/layout.rs`
- ❌ `compiler/interpreter_extern/math` → `rust/compiler/src/interpreter_extern/math.rs`
- ❌ `compiler/interpreter_extern/mock_policy` → `rust/compiler/src/interpreter_extern/mock_policy.rs`
- ❌ `compiler/interpreter_extern/process` → `rust/compiler/src/interpreter_extern/process.rs`
- ❌ `compiler/interpreter_extern/random` → `rust/compiler/src/interpreter_extern/random.rs`
- ❌ `compiler/interpreter_extern/sandbox` → `rust/compiler/src/interpreter_extern/sandbox.rs`
- ❌ `compiler/interpreter_extern/sdn` → `rust/compiler/src/interpreter_extern/sdn.rs`
- ❌ `compiler/interpreter_extern/terminal` → `rust/compiler/src/interpreter_extern/terminal.rs`
- ❌ `compiler/interpreter_extern/tui` → `rust/compiler/src/interpreter_extern/tui.rs`
- ❌ `compiler/interpreter_extern/time` → `rust/compiler/src/interpreter_extern/time.rs`
- ❌ `compiler/interpreter_extern/package` → `rust/compiler/src/interpreter_extern/package.rs`
- ❌ `compiler/interpreter_extern/regex` → `rust/compiler/src/interpreter_extern/regex.rs`
- ❌ `compiler/interpreter_extern/cargo` → `rust/compiler/src/interpreter_extern/cargo.rs`
- ❌ `compiler/interpreter_extern/repl` → `rust/compiler/src/interpreter_extern/repl.rs`
- ❌ `compiler/interpreter_extern/system` → `rust/compiler/src/interpreter_extern/system.rs`
- ❌ `compiler/interpreter_extern/cli` → `rust/compiler/src/interpreter_extern/cli.rs`
- ❌ `compiler/interpreter_extern/memory` → `rust/compiler/src/interpreter_extern/memory.rs`
- ❌ `compiler/interpreter_extern/rc` → `rust/compiler/src/interpreter_extern/rc.rs`
- ❌ `compiler/interpreter_extern/mod` → `rust/compiler/src/interpreter_extern/mod.rs`
- ❌ `compiler/interpreter_extern/file_io` → `rust/compiler/src/interpreter_extern/file_io.rs`
- ❌ `compiler/interpreter_extern/common/arg_extract` → `rust/compiler/src/interpreter_extern/common/arg_extract.rs`
- ❌ `compiler/interpreter_extern/common/effect_check` → `rust/compiler/src/interpreter_extern/common/effect_check.rs`
- ❌ `compiler/interpreter_extern/common/error_utils` → `rust/compiler/src/interpreter_extern/common/error_utils.rs`
- ❌ `compiler/interpreter_extern/common/mod` → `rust/compiler/src/interpreter_extern/common/mod.rs`
- ❌ `compiler/interpreter_extern/io/input` → `rust/compiler/src/interpreter_extern/io/input.rs`
- ❌ `compiler/interpreter_extern/io/mod` → `rust/compiler/src/interpreter_extern/io/mod.rs`
- ❌ `compiler/interpreter_extern/io/print` → `rust/compiler/src/interpreter_extern/io/print.rs`
- ❌ `compiler/interpreter_extern/network/http` → `rust/compiler/src/interpreter_extern/network/http.rs`
- ❌ `compiler/interpreter_extern/network/mod` → `rust/compiler/src/interpreter_extern/network/mod.rs`
- ❌ `compiler/interpreter_extern/network/tcp` → `rust/compiler/src/interpreter_extern/network/tcp.rs`
- ❌ `compiler/interpreter_extern/network/udp` → `rust/compiler/src/interpreter_extern/network/udp.rs`
- ❌ `compiler/interpreter_helpers/args` → `rust/compiler/src/interpreter_helpers/args.rs`
- ❌ `compiler/interpreter_helpers/mod` → `rust/compiler/src/interpreter_helpers/mod.rs`
- ❌ `compiler/interpreter_helpers/objects` → `rust/compiler/src/interpreter_helpers/objects.rs`
- ❌ `compiler/interpreter_helpers/patterns` → `rust/compiler/src/interpreter_helpers/patterns.rs`
- ❌ `compiler/interpreter_helpers/utilities` → `rust/compiler/src/interpreter_helpers/utilities.rs`
- ❌ `compiler/interpreter_helpers/method_dispatch` → `rust/compiler/src/interpreter_helpers/method_dispatch.rs`
- ❌ `compiler/interpreter_helpers/collections` → `rust/compiler/src/interpreter_helpers/collections.rs`
- ❌ `compiler/interpreter_method/primitives` → `rust/compiler/src/interpreter_method/primitives.rs`
- ❌ `compiler/interpreter_method/string` → `rust/compiler/src/interpreter_method/string.rs`
- ❌ `compiler/interpreter_method/collections` → `rust/compiler/src/interpreter_method/collections.rs`
- ❌ `compiler/interpreter_method/mod` → `rust/compiler/src/interpreter_method/mod.rs`
- ❌ `compiler/interpreter_method/special/concurrency` → `rust/compiler/src/interpreter_method/special/concurrency.rs`
- ❌ `compiler/interpreter_method/special/execution` → `rust/compiler/src/interpreter_method/special/execution.rs`
- ❌ `compiler/interpreter_method/special/mock` → `rust/compiler/src/interpreter_method/special/mock.rs`
- ❌ `compiler/interpreter_method/special/mod` → `rust/compiler/src/interpreter_method/special/mod.rs`
- ❌ `compiler/interpreter_method/special/objects` → `rust/compiler/src/interpreter_method/special/objects.rs`
- ❌ `compiler/interpreter_method/special/types` → `rust/compiler/src/interpreter_method/special/types.rs`
- ❌ `compiler/interpreter_module/export_handler` → `rust/compiler/src/interpreter_module/export_handler.rs`
- ❌ `compiler/interpreter_module/module_merger` → `rust/compiler/src/interpreter_module/module_merger.rs`
- ❌ `compiler/interpreter_module/module_evaluator` → `rust/compiler/src/interpreter_module/module_evaluator.rs`
- ❌ `compiler/interpreter_module/module_loader` → `rust/compiler/src/interpreter_module/module_loader.rs`
- ❌ `compiler/interpreter_module/path_resolution` → `rust/compiler/src/interpreter_module/path_resolution.rs`
- ❌ `compiler/interpreter_module/mod` → `rust/compiler/src/interpreter_module/mod.rs`
- ❌ `compiler/interpreter_module/module_evaluator/evaluation_helpers` → `rust/compiler/src/interpreter_module/module_evaluator/evaluation_helpers.rs`
- ❌ `compiler/linker/builder` → `rust/compiler/src/linker/builder.rs`
- ❌ `compiler/linker/builder_macros` → `rust/compiler/src/linker/builder_macros.rs`
- ❌ `compiler/linker/error` → `rust/compiler/src/linker/error.rs`
- ❌ `compiler/linker/interner` → `rust/compiler/src/linker/interner.rs`
- ❌ `compiler/linker/layout` → `rust/compiler/src/linker/layout.rs`
- ✅ `compiler/linker/lazy_instantiator` → `rust/compiler/src/linker/lazy_instantiator.rs`
  - Simple: `src/compiler/linker/lazy_instantiator.spl`
- ✅ `compiler/linker/mod` → `rust/compiler/src/linker/mod.rs`
  - Simple: `src/compiler/linker/mod.spl`
- ❌ `compiler/linker/object_parser` → `rust/compiler/src/linker/object_parser.rs`
- ❌ `compiler/linker/parallel` → `rust/compiler/src/linker/parallel.rs`
- ✅ `compiler/linker/smf_writer` → `rust/compiler/src/linker/smf_writer.rs`
  - Simple: `src/compiler/linker/smf_writer.spl`
- ❌ `compiler/linker/analysis/analyzer` → `rust/compiler/src/linker/analysis/analyzer.rs`
- ❌ `compiler/linker/analysis/graph` → `rust/compiler/src/linker/analysis/graph.rs`
- ❌ `compiler/linker/analysis/mod` → `rust/compiler/src/linker/analysis/mod.rs`
- ❌ `compiler/linker/analysis/stats` → `rust/compiler/src/linker/analysis/stats.rs`
- ❌ `compiler/linker/analysis/symbol` → `rust/compiler/src/linker/analysis/symbol.rs`
- ❌ `compiler/linker/analysis/types` → `rust/compiler/src/linker/analysis/types.rs`
- ❌ `compiler/lint/diagnostics` → `rust/compiler/src/lint/diagnostics.rs`
- ❌ `compiler/lint/rules` → `rust/compiler/src/lint/rules.rs`
- ❌ `compiler/lint/types` → `rust/compiler/src/lint/types.rs`
- ❌ `compiler/lint/config` → `rust/compiler/src/lint/config.rs`
- ❌ `compiler/lint/mod` → `rust/compiler/src/lint/mod.rs`
- ❌ `compiler/lint/checker` → `rust/compiler/src/lint/checker.rs`
- ❌ `compiler/lsp_mcp/mod` → `rust/compiler/src/lsp_mcp/mod.rs`
- ❌ `compiler/lsp_mcp/tools` → `rust/compiler/src/lsp_mcp/tools.rs`
- ❌ `compiler/lsp_mcp/types` → `rust/compiler/src/lsp_mcp/types.rs`
- ❌ `compiler/macro/expansion` → `rust/compiler/src/macro/expansion.rs`
- ❌ `compiler/macro/helpers` → `rust/compiler/src/macro/helpers.rs`
- ❌ `compiler/macro/invocation` → `rust/compiler/src/macro/invocation.rs`
- ❌ `compiler/macro/mod` → `rust/compiler/src/macro/mod.rs`
- ❌ `compiler/macro/state` → `rust/compiler/src/macro/state.rs`
- ❌ `compiler/macro/hygiene` → `rust/compiler/src/macro/hygiene.rs`
- ❌ `compiler/macro/substitution` → `rust/compiler/src/macro/substitution.rs`
- ❌ `compiler/method_registry/builtins` → `rust/compiler/src/method_registry/builtins.rs`
- ❌ `compiler/method_registry/mod` → `rust/compiler/src/method_registry/mod.rs`
- ❌ `compiler/method_registry/registry` → `rust/compiler/src/method_registry/registry.rs`
- ❌ `compiler/mock_helper/api_scanner` → `rust/compiler/src/mock_helper/api_scanner.rs`
- ❌ `compiler/mock_helper/coverage` → `rust/compiler/src/mock_helper/coverage.rs`
- ❌ `compiler/mock_helper/mock_policy` → `rust/compiler/src/mock_helper/mock_policy.rs`
- ❌ `compiler/mock_helper/mod` → `rust/compiler/src/mock_helper/mod.rs`
- ❌ `compiler/mock_helper/fluent` → `rust/compiler/src/mock_helper/fluent.rs`
- ❌ `compiler/mock_helper/coverage_extended/display` → `rust/compiler/src/mock_helper/coverage_extended/display.rs`
- ❌ `compiler/mock_helper/coverage_extended/metrics` → `rust/compiler/src/mock_helper/coverage_extended/metrics.rs`
- ❌ `compiler/mock_helper/coverage_extended/mod` → `rust/compiler/src/mock_helper/coverage_extended/mod.rs`
- ❌ `compiler/mock_helper/coverage_extended/types` → `rust/compiler/src/mock_helper/coverage_extended/types.rs`
- ❌ `compiler/mock_helper/coverage_extended/utils` → `rust/compiler/src/mock_helper/coverage_extended/utils.rs`
- ❌ `compiler/mock_helper/coverage_extended/analyzer` → `rust/compiler/src/mock_helper/coverage_extended/analyzer.rs`
- ❌ `compiler/mock_helper/coverage_extended/report` → `rust/compiler/src/mock_helper/coverage_extended/report.rs`
- ❌ `compiler/module_resolver/manifest` → `rust/compiler/src/module_resolver/manifest.rs`
- ❌ `compiler/module_resolver/mod` → `rust/compiler/src/module_resolver/mod.rs`
- ❌ `compiler/module_resolver/resolution` → `rust/compiler/src/module_resolver/resolution.rs`
- ❌ `compiler/module_resolver/types` → `rust/compiler/src/module_resolver/types.rs`
- ✅ `compiler/monomorphize/binding_specializer` → `rust/compiler/src/monomorphize/binding_specializer.rs`
  - Simple: `src/compiler/monomorphize/binding_specializer.spl`
- ❌ `compiler/monomorphize/cycle_detector` → `rust/compiler/src/monomorphize/cycle_detector.rs`
- ❌ `compiler/monomorphize/hot_reload` → `rust/compiler/src/monomorphize/hot_reload.rs`
- ❌ `compiler/monomorphize/metadata` → `rust/compiler/src/monomorphize/metadata.rs`
- ❌ `compiler/monomorphize/mod` → `rust/compiler/src/monomorphize/mod.rs`
- ❌ `compiler/monomorphize/note_sdn` → `rust/compiler/src/monomorphize/note_sdn.rs`
- ❌ `compiler/monomorphize/parallel` → `rust/compiler/src/monomorphize/parallel.rs`
- ❌ `compiler/monomorphize/partition` → `rust/compiler/src/monomorphize/partition.rs`
- ❌ `compiler/monomorphize/table` → `rust/compiler/src/monomorphize/table.rs`
- ❌ `compiler/monomorphize/tracker` → `rust/compiler/src/monomorphize/tracker.rs`
- ❌ `compiler/monomorphize/types` → `rust/compiler/src/monomorphize/types.rs`
- ❌ `compiler/monomorphize/deferred` → `rust/compiler/src/monomorphize/deferred.rs`
- ✅ `compiler/monomorphize/cache` → `rust/compiler/src/monomorphize/cache.rs`
  - Simple: `src/compiler/monomorphize/cache.spl`
- ❌ `compiler/monomorphize/util` → `rust/compiler/src/monomorphize/util.rs`
- ✅ `compiler/monomorphize/analyzer` → `rust/compiler/src/monomorphize/analyzer.rs`
  - Simple: `src/compiler/monomorphize/analyzer.spl`
- ✅ `compiler/monomorphize/rewriter` → `rust/compiler/src/monomorphize/rewriter.rs`
  - Simple: `src/compiler/monomorphize/rewriter.spl`
- ✅ `compiler/monomorphize/engine` → `rust/compiler/src/monomorphize/engine.rs`
  - Simple: `src/compiler/monomorphize/engine.spl`
- ❌ `compiler/pipeline/codegen` → `rust/compiler/src/pipeline/codegen.rs`
- ❌ `compiler/pipeline/core` → `rust/compiler/src/pipeline/core.rs`
- ❌ `compiler/pipeline/execution` → `rust/compiler/src/pipeline/execution.rs`
- ❌ `compiler/pipeline/parsing` → `rust/compiler/src/pipeline/parsing.rs`
- ❌ `compiler/pipeline/script_detection` → `rust/compiler/src/pipeline/script_detection.rs`
- ❌ `compiler/pipeline/lowering` → `rust/compiler/src/pipeline/lowering.rs`
- ❌ `compiler/pipeline/module_loader` → `rust/compiler/src/pipeline/module_loader.rs`
- ❌ `compiler/pipeline/mod` → `rust/compiler/src/pipeline/mod.rs`
- ❌ `compiler/runtime_profile/config` → `rust/compiler/src/runtime_profile/config.rs`
- ❌ `compiler/runtime_profile/diagram` → `rust/compiler/src/runtime_profile/diagram.rs`
- ❌ `compiler/runtime_profile/feedback` → `rust/compiler/src/runtime_profile/feedback.rs`
- ❌ `compiler/runtime_profile/mod` → `rust/compiler/src/runtime_profile/mod.rs`
- ❌ `compiler/runtime_profile/profiler` → `rust/compiler/src/runtime_profile/profiler.rs`
- ❌ `compiler/runtime_profile/stats` → `rust/compiler/src/runtime_profile/stats.rs`
- ❌ `compiler/semantics/binary_ops` → `rust/compiler/src/semantics/binary_ops.rs`
- ❌ `compiler/semantics/cast_rules` → `rust/compiler/src/semantics/cast_rules.rs`
- ❌ `compiler/semantics/mod` → `rust/compiler/src/semantics/mod.rs`
- ❌ `compiler/semantics/truthiness` → `rust/compiler/src/semantics/truthiness.rs`
- ❌ `compiler/semantics/type_coercion` → `rust/compiler/src/semantics/type_coercion.rs`
- ❌ `compiler/type_check/mod` → `rust/compiler/src/type_check/mod.rs`
- ❌ `compiler/weaving/diagnostics` → `rust/compiler/src/weaving/diagnostics.rs`
- ❌ `compiler/weaving/matcher` → `rust/compiler/src/weaving/matcher.rs`
- ❌ `compiler/weaving/mod` → `rust/compiler/src/weaving/mod.rs`
- ❌ `compiler/weaving/types` → `rust/compiler/src/weaving/types.rs`
- ❌ `compiler/weaving/weaver` → `rust/compiler/src/weaving/weaver.rs`
- ❌ `dependency_tracker/graph` → `rust/dependency_tracker/src/graph.rs`
- ❌ `dependency_tracker/macro_import` → `rust/dependency_tracker/src/macro_import.rs`
- ❌ `dependency_tracker/resolution` → `rust/dependency_tracker/src/resolution.rs`
- ❌ `dependency_tracker/symbol` → `rust/dependency_tracker/src/symbol.rs`
- ❌ `dependency_tracker/visibility` → `rust/dependency_tracker/src/visibility.rs`
- ❌ `gpu/device` → `rust/gpu/src/device.rs`
- ❌ `gpu/buffer` → `rust/gpu/src/buffer.rs`
- ❌ `gpu/context` → `rust/gpu/src/context.rs`
- ❌ `gpu/error` → `rust/gpu/src/error.rs`
- ❌ `gpu/intrinsics` → `rust/gpu/src/intrinsics.rs`
- ❌ `gpu/kernel` → `rust/gpu/src/kernel.rs`
- ❌ `gpu/optimize` → `rust/gpu/src/optimize.rs`
- ✅ `gpu/parallel` → `rust/gpu/src/parallel.rs`
  - Simple: `src/compiler/parallel.spl`
- ❌ `gpu/backend/mod` → `rust/gpu/src/backend/mod.rs`
- ❌ `gpu/backend/cuda` → `rust/gpu/src/backend/cuda.rs`
- ❌ `gpu/backend/rocm` → `rust/gpu/src/backend/rocm.rs`
- ❌ `gpu/backend/software` → `rust/gpu/src/backend/software.rs`
- ✅ `lib/build` → `rust/lib/build.rs`
  - Simple: `src/build.spl`
- ✅ `lib/io/mod` → `rust/lib/src/io/mod.rs`
  - Simple: `src/app/io/mod.spl`
- ❌ `lib/io/term/mod` → `rust/lib/src/io/term/mod.rs`
- ❌ `loader/module` → `rust/loader/src/module.rs`
- ❌ `loader/arch_validate` → `rust/loader/src/arch_validate.rs`
- ❌ `loader/registry` → `rust/loader/src/registry.rs`
- ❌ `loader/startup` → `rust/loader/src/startup.rs`
- ❌ `loader/loader` → `rust/loader/src/loader.rs`
- ❌ `loader/smf/reloc` → `rust/loader/src/smf/reloc.rs`
- ❌ `loader/smf/section` → `rust/loader/src/smf/section.rs`
- ❌ `loader/smf/symbol` → `rust/loader/src/smf/symbol.rs`
- ❌ `loader/smf/header` → `rust/loader/src/smf/header.rs`
- ❌ `loader/smf/settlement` → `rust/loader/src/smf/settlement.rs`
- ❌ `loader/smf/note_loader` → `rust/loader/src/smf/note_loader.rs`
- ❌ `loader/smf/bytecode_writer` → `rust/loader/src/smf/bytecode_writer.rs`
- ❌ `loader/smf/bytecode_loader` → `rust/loader/src/smf/bytecode_loader.rs`
- ❌ `loader/smf/compression` → `rust/loader/src/smf/compression.rs`
- ❌ `loader/smf/mod` → `rust/loader/src/smf/mod.rs`
- ❌ `loader/smf/jit_instantiator` → `rust/loader/src/smf/jit_instantiator.rs`
- ❌ `loader/memory/common` → `rust/loader/src/memory/common.rs`
- ❌ `loader/memory/mod` → `rust/loader/src/memory/mod.rs`
- ❌ `loader/memory/posix` → `rust/loader/src/memory/posix.rs`
- ❌ `loader/memory/windows` → `rust/loader/src/memory/windows.rs`
- ❌ `loader/settlement/mod` → `rust/loader/src/settlement/mod.rs`
- ❌ `loader/settlement/container` → `rust/loader/src/settlement/container.rs`
- ❌ `loader/settlement/container_impl` → `rust/loader/src/settlement/container_impl.rs`
- ❌ `loader/settlement/linker` → `rust/loader/src/settlement/linker.rs`
- ❌ `loader/settlement/slots` → `rust/loader/src/settlement/slots.rs`
- ❌ `loader/settlement/tables` → `rust/loader/src/settlement/tables.rs`
- ❌ `loader/settlement/builder` → `rust/loader/src/settlement/builder.rs`
- ❌ `loader/package/mod` → `rust/loader/src/package/mod.rs`
- ❌ `loader/package/format` → `rust/loader/src/package/format.rs`
- ❌ `loader/package/reader` → `rust/loader/src/package/reader.rs`
- ❌ `loader/package/writer` → `rust/loader/src/package/writer.rs`
- ❌ `log/parse/mod` → `rust/log/src/parse/mod.rs`
- ❌ `log/run_time/mod` → `rust/log/src/run_time/mod.rs`
- ❌ `native_loader/registry` → `rust/native_loader/src/registry.rs`
- ❌ `native_loader/chained_provider` → `rust/native_loader/src/chained_provider.rs`
- ❌ `native_loader/dynamic_provider` → `rust/native_loader/src/dynamic_provider.rs`
- ❌ `native_loader/loader` → `rust/native_loader/src/loader.rs`
- ❌ `native_loader/module` → `rust/native_loader/src/module.rs`
- ❌ `native_loader/provider` → `rust/native_loader/src/provider.rs`
- ❌ `native_loader/static_provider` → `rust/native_loader/src/static_provider.rs`
- ❌ `parser/diagnostic` → `rust/parser/src/diagnostic.rs`
- ❌ `parser/doc_gen` → `rust/parser/src/doc_gen.rs`
- ❌ `parser/error` → `rust/parser/src/error.rs`
- ❌ `parser/error_recovery` → `rust/parser/src/error_recovery.rs`
- ❌ `parser/interner` → `rust/parser/src/interner.rs`
- ❌ `parser/macro_registry` → `rust/parser/src/macro_registry.rs`
- ✅ `parser/parser_types` → `rust/parser/src/parser_types.rs`
  - Simple: `src/compiler/parser_types.spl`
- ❌ `parser/sui_parser` → `rust/parser/src/sui_parser.rs`
- ❌ `parser/token` → `rust/parser/src/token.rs`
- ❌ `parser/parser_patterns` → `rust/parser/src/parser_patterns.rs`
- ❌ `parser/parser_helpers` → `rust/parser/src/parser_helpers.rs`
- ❌ `parser/effect_inference` → `rust/parser/src/effect_inference.rs`
- ❌ `parser/aop/mod` → `rust/parser/src/aop/mod.rs`
- ❌ `parser/expressions/core` → `rust/parser/src/expressions/core.rs`
- ❌ `parser/expressions/mod` → `rust/parser/src/expressions/mod.rs`
- ❌ `parser/expressions/placeholder` → `rust/parser/src/expressions/placeholder.rs`
- ❌ `parser/expressions/postfix` → `rust/parser/src/expressions/postfix.rs`
- ❌ `parser/expressions/helpers` → `rust/parser/src/expressions/helpers.rs`
- ❌ `parser/expressions/binary` → `rust/parser/src/expressions/binary.rs`
- ❌ `parser/expressions/no_paren` → `rust/parser/src/expressions/no_paren.rs`
- ❌ `parser/expressions/primary/collections` → `rust/parser/src/expressions/primary/collections.rs`
- ❌ `parser/expressions/primary/control` → `rust/parser/src/expressions/primary/control.rs`
- ❌ `parser/expressions/primary/i18n` → `rust/parser/src/expressions/primary/i18n.rs`
- ❌ `parser/expressions/primary/identifiers` → `rust/parser/src/expressions/primary/identifiers.rs`
- ❌ `parser/expressions/primary/lambdas` → `rust/parser/src/expressions/primary/lambdas.rs`
- ❌ `parser/expressions/primary/literals` → `rust/parser/src/expressions/primary/literals.rs`
- ❌ `parser/expressions/primary/math` → `rust/parser/src/expressions/primary/math.rs`
- ❌ `parser/expressions/primary/mod` → `rust/parser/src/expressions/primary/mod.rs`
- ❌ `parser/parser_impl/attributes` → `rust/parser/src/parser_impl/attributes.rs`
- ❌ `parser/parser_impl/definitions` → `rust/parser/src/parser_impl/definitions.rs`
- ❌ `parser/parser_impl/doc_comments` → `rust/parser/src/parser_impl/doc_comments.rs`
- ❌ `parser/parser_impl/mod` → `rust/parser/src/parser_impl/mod.rs`
- ❌ `parser/parser_impl/items` → `rust/parser/src/parser_impl/items.rs`
- ❌ `parser/parser_impl/functions` → `rust/parser/src/parser_impl/functions.rs`
- ❌ `parser/parser_impl/core` → `rust/parser/src/parser_impl/core.rs`
- ❌ `parser/stmt_parsing/aop` → `rust/parser/src/stmt_parsing/aop.rs`
- ❌ `parser/stmt_parsing/assert` → `rust/parser/src/stmt_parsing/assert.rs`
- ❌ `parser/stmt_parsing/bounds` → `rust/parser/src/stmt_parsing/bounds.rs`
- ❌ `parser/stmt_parsing/contract` → `rust/parser/src/stmt_parsing/contract.rs`
- ❌ `parser/stmt_parsing/gherkin` → `rust/parser/src/stmt_parsing/gherkin.rs`
- ❌ `parser/stmt_parsing/jump` → `rust/parser/src/stmt_parsing/jump.rs`
- ❌ `parser/stmt_parsing/macro_parsing` → `rust/parser/src/stmt_parsing/macro_parsing.rs`
- ❌ `parser/stmt_parsing/mod` → `rust/parser/src/stmt_parsing/mod.rs`
- ❌ `parser/stmt_parsing/unit_parsing` → `rust/parser/src/stmt_parsing/unit_parsing.rs`
- ❌ `parser/stmt_parsing/module_system` → `rust/parser/src/stmt_parsing/module_system.rs`
- ❌ `parser/stmt_parsing/lean` → `rust/parser/src/stmt_parsing/lean.rs`
- ❌ `parser/stmt_parsing/var_decl` → `rust/parser/src/stmt_parsing/var_decl.rs`
- ❌ `parser/stmt_parsing/control_flow` → `rust/parser/src/stmt_parsing/control_flow.rs`
- ❌ `parser/types_def/enum_parsing` → `rust/parser/src/types_def/enum_parsing.rs`
- ❌ `parser/types_def/mod` → `rust/parser/src/types_def/mod.rs`
- ❌ `parser/types_def/trait_impl_parsing` → `rust/parser/src/types_def/trait_impl_parsing.rs`
- ✅ `runtime/coverage` → `rust/runtime/src/coverage.rs`
  - Simple: `src/compiler/coverage.spl`
- ❌ `runtime/cuda_runtime` → `rust/runtime/src/cuda_runtime.rs`
- ❌ `runtime/monoio_tcp_v2` → `rust/runtime/src/monoio_tcp_v2.rs`
- ❌ `runtime/monoio_buffer` → `rust/runtime/src/monoio_buffer.rs`
- ❌ `runtime/monoio_udp_v2` → `rust/runtime/src/monoio_udp_v2.rs`
- ❌ `runtime/monoio_waker` → `rust/runtime/src/monoio_waker.rs`
- ✅ `runtime/aop` → `rust/runtime/src/aop.rs`
  - Simple: `src/compiler/aop.spl`
- ❌ `runtime/monoio_tcp` → `rust/runtime/src/monoio_tcp.rs`
- ❌ `runtime/monoio_udp` → `rust/runtime/src/monoio_udp.rs`
- ❌ `runtime/monoio_runtime` → `rust/runtime/src/monoio_runtime.rs`
- ❌ `runtime/executor` → `rust/runtime/src/executor.rs`
- ❌ `runtime/async_runtime` → `rust/runtime/src/async_runtime.rs`
- ❌ `runtime/debug` → `rust/runtime/src/debug.rs`
- ❌ `runtime/hir_core` → `rust/runtime/src/hir_core.rs`
- ✅ `runtime/parallel` → `rust/runtime/src/parallel.rs`
  - Simple: `src/compiler/parallel.spl`
- ❌ `runtime/concurrency/mod` → `rust/runtime/src/concurrency/mod.rs`
- ❌ `runtime/memory/no_gc` → `rust/runtime/src/memory/no_gc.rs`
- ❌ `runtime/memory/gcless` → `rust/runtime/src/memory/gcless.rs`
- ❌ `runtime/memory/mod` → `rust/runtime/src/memory/mod.rs`
- ❌ `runtime/memory/gc` → `rust/runtime/src/memory/gc.rs`
- ❌ `runtime/value/net_http` → `rust/runtime/src/value/net_http.rs`
- ❌ `runtime/value/sync_barrier` → `rust/runtime/src/value/sync_barrier.rs`
- ❌ `runtime/value/sync_rwlock` → `rust/runtime/src/value/sync_rwlock.rs`
- ❌ `runtime/value/channels` → `rust/runtime/src/value/channels.rs`
- ❌ `runtime/value/sync_semaphore` → `rust/runtime/src/value/sync_semaphore.rs`
- ❌ `runtime/value/args` → `rust/runtime/src/value/args.rs`
- ❌ `runtime/value/async_gen` → `rust/runtime/src/value/async_gen.rs`
- ❌ `runtime/value/gpu` → `rust/runtime/src/value/gpu.rs`
- ❌ `runtime/value/gpu_backend` → `rust/runtime/src/value/gpu_backend.rs`
- ❌ `runtime/value/sync` → `rust/runtime/src/value/sync.rs`
- ❌ `runtime/value/monoio_future` → `rust/runtime/src/value/monoio_future.rs`
- ❌ `runtime/value/process` → `rust/runtime/src/value/process.rs`
- ❌ `runtime/value/net_tcp` → `rust/runtime/src/value/net_tcp.rs`
- ❌ `runtime/value/net_udp` → `rust/runtime/src/value/net_udp.rs`
- ❌ `runtime/value/contracts` → `rust/runtime/src/value/contracts.rs`
- ❌ `runtime/value/net` → `rust/runtime/src/value/net.rs`
- ❌ `runtime/value/actors` → `rust/runtime/src/value/actors.rs`
- ❌ `runtime/value/simd` → `rust/runtime/src/value/simd.rs`
- ❌ `runtime/value/dict` → `rust/runtime/src/value/dict.rs`
- ❌ `runtime/value/collections` → `rust/runtime/src/value/collections.rs`
- ❌ `runtime/value/objects` → `rust/runtime/src/value/objects.rs`
- ❌ `runtime/value/tags` → `rust/runtime/src/value/tags.rs`
- ❌ `runtime/value/core` → `rust/runtime/src/value/core.rs`
- ❌ `runtime/value/heap` → `rust/runtime/src/value/heap.rs`
- ❌ `runtime/value/ratatui_tui` → `rust/runtime/src/value/ratatui_tui.rs`
- ❌ `runtime/value/mod` → `rust/runtime/src/value/mod.rs`
- ❌ `runtime/value/pty` → `rust/runtime/src/value/pty.rs`
- ❌ `runtime/value/file_io/fadvise` → `rust/runtime/src/value/file_io/fadvise.rs`
- ❌ `runtime/value/file_io/process` → `rust/runtime/src/value/file_io/process.rs`
- ❌ `runtime/value/file_io/mmap` → `rust/runtime/src/value/file_io/mmap.rs`
- ❌ `runtime/value/file_io/async_file` → `rust/runtime/src/value/file_io/async_file.rs`
- ❌ `runtime/value/file_io/common` → `rust/runtime/src/value/file_io/common.rs`
- ❌ `runtime/value/file_io/file_ops` → `rust/runtime/src/value/file_io/file_ops.rs`
- ❌ `runtime/value/file_io/syscalls` → `rust/runtime/src/value/file_io/syscalls.rs`
- ❌ `runtime/value/file_io/zerocopy` → `rust/runtime/src/value/file_io/zerocopy.rs`
- ❌ `runtime/value/file_io/mod` → `rust/runtime/src/value/file_io/mod.rs`
- ❌ `runtime/value/torch/error` → `rust/runtime/src/value/torch/error.rs`
- ❌ `runtime/value/torch/metadata` → `rust/runtime/src/value/torch/metadata.rs`
- ❌ `runtime/value/torch/mod` → `rust/runtime/src/value/torch/mod.rs`
- ❌ `runtime/value/torch/registry` → `rust/runtime/src/value/torch/registry.rs`
- ❌ `runtime/value/torch/autograd` → `rust/runtime/src/value/torch/autograd.rs`
- ❌ `runtime/value/torch/data_access` → `rust/runtime/src/value/torch/data_access.rs`
- ❌ `runtime/value/torch/device` → `rust/runtime/src/value/torch/device.rs`
- ❌ `runtime/value/torch/nn_activations` → `rust/runtime/src/value/torch/nn_activations.rs`
- ❌ `runtime/value/torch/nn_initialization` → `rust/runtime/src/value/torch/nn_initialization.rs`
- ❌ `runtime/value/torch/nn_loss` → `rust/runtime/src/value/torch/nn_loss.rs`
- ❌ `runtime/value/torch/nn_normalization` → `rust/runtime/src/value/torch/nn_normalization.rs`
- ❌ `runtime/value/torch/ops_comparison` → `rust/runtime/src/value/torch/ops_comparison.rs`
- ❌ `runtime/value/torch/ops_matrix` → `rust/runtime/src/value/torch/ops_matrix.rs`
- ❌ `runtime/value/torch/ops_shape` → `rust/runtime/src/value/torch/ops_shape.rs`
- ❌ `runtime/value/torch/optimizer` → `rust/runtime/src/value/torch/optimizer.rs`
- ❌ `runtime/value/torch/linalg` → `rust/runtime/src/value/torch/linalg.rs`
- ❌ `runtime/value/torch/fft` → `rust/runtime/src/value/torch/fft.rs`
- ❌ `runtime/value/torch/scheduler` → `rust/runtime/src/value/torch/scheduler.rs`
- ❌ `runtime/value/torch/ops_reduction` → `rust/runtime/src/value/torch/ops_reduction.rs`
- ❌ `runtime/value/torch/creation` → `rust/runtime/src/value/torch/creation.rs`
- ❌ `runtime/value/torch/ops_elementwise` → `rust/runtime/src/value/torch/ops_elementwise.rs`
- ❌ `runtime/value/torch/data/dataset` → `rust/runtime/src/value/torch/data/dataset.rs`
- ❌ `runtime/value/torch/data/mod` → `rust/runtime/src/value/torch/data/mod.rs`
- ❌ `runtime/value/torch/data/dataloader` → `rust/runtime/src/value/torch/data/dataloader.rs`
- ❌ `runtime/value/torch/modules/batchnorm` → `rust/runtime/src/value/torch/modules/batchnorm.rs`
- ❌ `runtime/value/torch/modules/conv` → `rust/runtime/src/value/torch/modules/conv.rs`
- ❌ `runtime/value/torch/modules/dropout` → `rust/runtime/src/value/torch/modules/dropout.rs`
- ❌ `runtime/value/torch/modules/embedding` → `rust/runtime/src/value/torch/modules/embedding.rs`
- ❌ `runtime/value/torch/modules/layernorm` → `rust/runtime/src/value/torch/modules/layernorm.rs`
- ❌ `runtime/value/torch/modules/linear` → `rust/runtime/src/value/torch/modules/linear.rs`
- ❌ `runtime/value/torch/modules/rnn` → `rust/runtime/src/value/torch/modules/rnn.rs`
- ❌ `runtime/value/torch/modules/mod` → `rust/runtime/src/value/torch/modules/mod.rs`
- ❌ `runtime/value/gpu_vulkan/mod` → `rust/runtime/src/value/gpu_vulkan/mod.rs`
- ❌ `runtime/value/hpcollections/mod` → `rust/runtime/src/value/hpcollections/mod.rs`
- ❌ `runtime/value/hpcollections/hashmap` → `rust/runtime/src/value/hpcollections/hashmap.rs`
- ❌ `runtime/value/hpcollections/hashset` → `rust/runtime/src/value/hpcollections/hashset.rs`
- ❌ `runtime/value/hpcollections/btreemap` → `rust/runtime/src/value/hpcollections/btreemap.rs`
- ❌ `runtime/value/hpcollections/btreeset` → `rust/runtime/src/value/hpcollections/btreeset.rs`
- ❌ `runtime/concurrent/map` → `rust/runtime/src/concurrent/map.rs`
- ❌ `runtime/concurrent/mod` → `rust/runtime/src/concurrent/mod.rs`
- ❌ `runtime/concurrent/queue` → `rust/runtime/src/concurrent/queue.rs`
- ❌ `runtime/concurrent/stack` → `rust/runtime/src/concurrent/stack.rs`
- ❌ `runtime/concurrent/gc_barrier` → `rust/runtime/src/concurrent/gc_barrier.rs`
- ❌ `runtime/sandbox/windows` → `rust/runtime/src/sandbox/windows.rs`
- ❌ `runtime/sandbox/limits` → `rust/runtime/src/sandbox/limits.rs`
- ❌ `runtime/sandbox/mod` → `rust/runtime/src/sandbox/mod.rs`
- ❌ `runtime/sandbox/linux` → `rust/runtime/src/sandbox/linux.rs`
- ❌ `runtime/sandbox/macos` → `rust/runtime/src/sandbox/macos.rs`
- ❌ `runtime/vulkan/buffer` → `rust/runtime/src/vulkan/buffer.rs`
- ❌ `runtime/vulkan/instance` → `rust/runtime/src/vulkan/instance.rs`
- ❌ `runtime/vulkan/pipeline` → `rust/runtime/src/vulkan/pipeline.rs`
- ❌ `runtime/vulkan/surface` → `rust/runtime/src/vulkan/surface.rs`
- ❌ `runtime/vulkan/swapchain` → `rust/runtime/src/vulkan/swapchain.rs`
- ❌ `runtime/vulkan/device` → `rust/runtime/src/vulkan/device.rs`
- ❌ `runtime/vulkan/sync` → `rust/runtime/src/vulkan/sync.rs`
- ❌ `runtime/vulkan/render_pass` → `rust/runtime/src/vulkan/render_pass.rs`
- ❌ `runtime/vulkan/graphics_pipeline` → `rust/runtime/src/vulkan/graphics_pipeline.rs`
- ❌ `runtime/vulkan/framebuffer` → `rust/runtime/src/vulkan/framebuffer.rs`
- ❌ `runtime/vulkan/descriptor` → `rust/runtime/src/vulkan/descriptor.rs`
- ❌ `runtime/vulkan/window` → `rust/runtime/src/vulkan/window.rs`
- ❌ `runtime/vulkan/image` → `rust/runtime/src/vulkan/image.rs`
- ❌ `runtime/vulkan/error` → `rust/runtime/src/vulkan/error.rs`
- ❌ `runtime/vulkan/mod` → `rust/runtime/src/vulkan/mod.rs`
- ❌ `runtime/monoio_direct/init` → `rust/runtime/src/monoio_direct/init.rs`
- ❌ `runtime/monoio_direct/tcp` → `rust/runtime/src/monoio_direct/tcp.rs`
- ❌ `runtime/monoio_direct/tcp_options` → `rust/runtime/src/monoio_direct/tcp_options.rs`
- ❌ `runtime/monoio_direct/udp` → `rust/runtime/src/monoio_direct/udp.rs`
- ❌ `runtime/monoio_direct/udp_options` → `rust/runtime/src/monoio_direct/udp_options.rs`
- ❌ `runtime/monoio_direct/future` → `rust/runtime/src/monoio_direct/future.rs`
- ❌ `runtime/monoio_direct/stats` → `rust/runtime/src/monoio_direct/stats.rs`
- ❌ `runtime/monoio_direct/mod` → `rust/runtime/src/monoio_direct/mod.rs`
- ❌ `runtime/monoio_executor/types` → `rust/runtime/src/monoio_executor/types.rs`
- ❌ `runtime/monoio_executor/pending_op` → `rust/runtime/src/monoio_executor/pending_op.rs`
- ❌ `runtime/monoio_executor/handle_store` → `rust/runtime/src/monoio_executor/handle_store.rs`
- ❌ `runtime/monoio_executor/tcp_ops` → `rust/runtime/src/monoio_executor/tcp_ops.rs`
- ❌ `runtime/monoio_executor/udp_ops` → `rust/runtime/src/monoio_executor/udp_ops.rs`
- ❌ `runtime/monoio_executor/runtime` → `rust/runtime/src/monoio_executor/runtime.rs`
- ❌ `runtime/monoio_executor/mod` → `rust/runtime/src/monoio_executor/mod.rs`
- ❌ `runtime/monoio_executor/executor` → `rust/runtime/src/monoio_executor/executor.rs`
- ❌ `runtime/monoio_thread/macros` → `rust/runtime/src/monoio_thread/macros.rs`
- ❌ `runtime/monoio_thread/types` → `rust/runtime/src/monoio_thread/types.rs`
- ❌ `runtime/monoio_thread/registry` → `rust/runtime/src/monoio_thread/registry.rs`
- ❌ `runtime/monoio_thread/tcp_handlers` → `rust/runtime/src/monoio_thread/tcp_handlers.rs`
- ❌ `runtime/monoio_thread/udp_handlers` → `rust/runtime/src/monoio_thread/udp_handlers.rs`
- ❌ `runtime/monoio_thread/request_builder` → `rust/runtime/src/monoio_thread/request_builder.rs`
- ❌ `runtime/monoio_thread/dispatcher` → `rust/runtime/src/monoio_thread/dispatcher.rs`
- ❌ `runtime/monoio_thread/runtime` → `rust/runtime/src/monoio_thread/runtime.rs`
- ❌ `runtime/monoio_thread/mod` → `rust/runtime/src/monoio_thread/mod.rs`
- ❌ `runtime/bytecode/opcodes` → `rust/runtime/src/bytecode/opcodes.rs`
- ❌ `runtime/bytecode/vm` → `rust/runtime/src/bytecode/vm.rs`
- ❌ `runtime/bytecode/disassembler` → `rust/runtime/src/bytecode/disassembler.rs`
- ❌ `runtime/bytecode/mod` → `rust/runtime/src/bytecode/mod.rs`
- ❌ `runtime/loader/arch_validate` → `rust/runtime/src/loader/arch_validate.rs`
- ❌ `runtime/loader/loader` → `rust/runtime/src/loader/loader.rs`
- ✅ `runtime/loader/mod` → `rust/runtime/src/loader/mod.rs`
  - Simple: `src/compiler/loader/mod.spl`
- ❌ `runtime/loader/module` → `rust/runtime/src/loader/module.rs`
- ❌ `runtime/loader/registry` → `rust/runtime/src/loader/registry.rs`
- ❌ `runtime/loader/startup` → `rust/runtime/src/loader/startup.rs`
- ❌ `runtime/loader/memory/common` → `rust/runtime/src/loader/memory/common.rs`
- ❌ `runtime/loader/memory/mod` → `rust/runtime/src/loader/memory/mod.rs`
- ❌ `runtime/loader/memory/posix` → `rust/runtime/src/loader/memory/posix.rs`
- ❌ `runtime/loader/memory/windows` → `rust/runtime/src/loader/memory/windows.rs`
- ❌ `runtime/loader/package/format` → `rust/runtime/src/loader/package/format.rs`
- ❌ `runtime/loader/package/mod` → `rust/runtime/src/loader/package/mod.rs`
- ❌ `runtime/loader/package/reader` → `rust/runtime/src/loader/package/reader.rs`
- ❌ `runtime/loader/package/writer` → `rust/runtime/src/loader/package/writer.rs`
- ❌ `runtime/loader/settlement/builder` → `rust/runtime/src/loader/settlement/builder.rs`
- ❌ `runtime/loader/settlement/container` → `rust/runtime/src/loader/settlement/container.rs`
- ❌ `runtime/loader/settlement/container_impl` → `rust/runtime/src/loader/settlement/container_impl.rs`
- ❌ `runtime/loader/settlement/linker` → `rust/runtime/src/loader/settlement/linker.rs`
- ❌ `runtime/loader/settlement/mod` → `rust/runtime/src/loader/settlement/mod.rs`
- ❌ `runtime/loader/settlement/slots` → `rust/runtime/src/loader/settlement/slots.rs`
- ❌ `runtime/loader/settlement/tables` → `rust/runtime/src/loader/settlement/tables.rs`
- ❌ `runtime/loader/smf/bytecode_writer` → `rust/runtime/src/loader/smf/bytecode_writer.rs`
- ❌ `runtime/loader/smf/compression` → `rust/runtime/src/loader/smf/compression.rs`
- ❌ `runtime/loader/smf/header` → `rust/runtime/src/loader/smf/header.rs`
- ❌ `runtime/loader/smf/jit_instantiator` → `rust/runtime/src/loader/smf/jit_instantiator.rs`
- ❌ `runtime/loader/smf/mod` → `rust/runtime/src/loader/smf/mod.rs`
- ❌ `runtime/loader/smf/note_loader` → `rust/runtime/src/loader/smf/note_loader.rs`
- ❌ `runtime/loader/smf/reloc` → `rust/runtime/src/loader/smf/reloc.rs`
- ❌ `runtime/loader/smf/section` → `rust/runtime/src/loader/smf/section.rs`
- ❌ `runtime/loader/smf/settlement` → `rust/runtime/src/loader/smf/settlement.rs`
- ❌ `runtime/loader/smf/symbol` → `rust/runtime/src/loader/smf/symbol.rs`
- ❌ `runtime/loader/smf/bytecode_loader` → `rust/runtime/src/loader/smf/bytecode_loader.rs`
- ❌ `runtime/compress/upx_download` → `rust/runtime/src/compress/upx_download.rs`
- ❌ `runtime/compress/upx` → `rust/runtime/src/compress/upx.rs`
- ❌ `runtime/compress/self_extract` → `rust/runtime/src/compress/self_extract.rs`
- ❌ `runtime/compress/mod` → `rust/runtime/src/compress/mod.rs`
- ❌ `runtime/compress/lzma_stub` → `rust/runtime/src/compress/lzma_stub.rs`
- ❌ `simd/detection` → `rust/simd/src/detection.rs`
- ❌ `simd/types_core` → `rust/simd/src/types_core.rs`
- ❌ `simd/types_f32` → `rust/simd/src/types_f32.rs`
- ❌ `simd/types` → `rust/simd/src/types.rs`
- ❌ `simd/ops` → `rust/simd/src/ops.rs`
- ❌ `simd/types_int` → `rust/simd/src/types_int.rs`
- ❌ `simd/intrinsics` → `rust/simd/src/intrinsics.rs`
- ❌ `test/diagnostics_i18n_integration` → `rust/test/diagnostics_i18n_integration.rs`
- ❌ `test/common` → `rust/test/contract/common.rs`
- ❌ `test/contract_modes` → `rust/test/contract/contract_modes.rs`
- ❌ `test/common_integration` → `rust/test/integration/common_integration.rs`
- ❌ `test/compiler_integration` → `rust/test/integration/compiler_integration.rs`
- ❌ `test/compiler_integration2` → `rust/test/integration/compiler_integration2.rs`
- ❌ `test/driver_integration` → `rust/test/integration/driver_integration.rs`
- ❌ `test/driver_integration2` → `rust/test/integration/driver_integration2.rs`
- ❌ `test/loader_integration` → `rust/test/integration/loader_integration.rs`
- ❌ `test/pkg_integration` → `rust/test/integration/pkg_integration.rs`
- ❌ `test/runtime_integration` → `rust/test/integration/runtime_integration.rs`
- ❌ `test/type_integration` → `rust/test/integration/type_integration.rs`
- ❌ `test/vulkan_integration` → `rust/test/integration/vulkan_integration.rs`
- ❌ `test/parser_integration` → `rust/test/integration/parser_integration.rs`
- ❌ `test/simple_cli_e2e` → `rust/test/system/simple_cli_e2e.rs`
- ❌ `test/simple_cli_shared` → `rust/test/system/simple_cli_shared.rs`
- ✅ `test/mod` → `rust/test/system/simple_basic/mod.rs`
  - Simple: `src/compiler/mod.spl`
- ✅ `test/mod` → `rust/test/system/simple_basic/compiler/mod.rs`
  - Simple: `src/compiler/mod.spl`
- ✅ `test/mod` → `rust/test/system/simple_basic/interpreter/mod.rs`
  - Simple: `src/compiler/mod.spl`
- ❌ `type/bitfield` → `rust/type/src/bitfield.rs`
- ❌ `type/checker_builtins` → `rust/type/src/checker_builtins.rs`
- ❌ `type/checker_unify` → `rust/type/src/checker_unify.rs`
- ❌ `type/dispatch_checker` → `rust/type/src/dispatch_checker.rs`
- ❌ `type/http_status` → `rust/type/src/http_status.rs`
- ❌ `type/macro_checker` → `rust/type/src/macro_checker.rs`
- ❌ `type/mixin_checker` → `rust/type/src/mixin_checker.rs`
- ❌ `type/response_builder` → `rust/type/src/response_builder.rs`
- ❌ `type/route_params` → `rust/type/src/route_params.rs`
- ❌ `type/tagged_union` → `rust/type/src/tagged_union.rs`
- ❌ `type/checker_infer` → `rust/type/src/checker_infer.rs`
- ❌ `type/checker_check` → `rust/type/src/checker_check.rs`
- ✅ `type/effects` → `rust/type/src/effects.rs`
  - Simple: `src/compiler/effects.spl`
- ❌ `util/api_scanner` → `rust/util/simple_mock_helper/src/api_scanner.rs`
- ✅ `util/coverage` → `rust/util/simple_mock_helper/src/coverage.rs`
  - Simple: `src/compiler/coverage.spl`
- ❌ `util/fluent` → `rust/util/simple_mock_helper/src/fluent.rs`
- ❌ `util/mock_policy` → `rust/util/simple_mock_helper/src/mock_policy.rs`
- ❌ `util/bin/coverage_gen` → `rust/util/simple_mock_helper/src/bin/coverage_gen.rs`
- ❌ `util/bin/smh_coverage` → `rust/util/simple_mock_helper/src/bin/smh_coverage.rs`
- ❌ `util/coverage_extended/metrics` → `rust/util/simple_mock_helper/src/coverage_extended/metrics.rs`
- ❌ `util/coverage_extended/types` → `rust/util/simple_mock_helper/src/coverage_extended/types.rs`
- ❌ `util/coverage_extended/utils` → `rust/util/simple_mock_helper/src/coverage_extended/utils.rs`
- ❌ `util/coverage_extended/analyzer` → `rust/util/simple_mock_helper/src/coverage_extended/analyzer.rs`
- ❌ `util/coverage_extended/display` → `rust/util/simple_mock_helper/src/coverage_extended/display.rs`
- ❌ `util/coverage_extended/mod` → `rust/util/simple_mock_helper/src/coverage_extended/mod.rs`
- ❌ `util/coverage_extended/report` → `rust/util/simple_mock_helper/src/coverage_extended/report.rs`
- ❌ `util/fluent_integration` → `rust/util/simple_mock_helper/examples/fluent_integration.rs`
- ❌ `util/error` → `rust/util/arch_test/src/error.rs`
- ❌ `util/analyzer` → `rust/util/arch_test/src/analyzer.rs`
- ❌ `util/layer` → `rust/util/arch_test/src/layer.rs`
- ❌ `util/rules` → `rust/util/arch_test/src/rules.rs`
- ❌ `util/visualize` → `rust/util/arch_test/src/visualize.rs`
- ❌ `wasm-runtime/bridge` → `rust/wasm-runtime/src/bridge.rs`
- ❌ `wasm-runtime/browser_mock` → `rust/wasm-runtime/src/browser_mock.rs`
- ❌ `wasm-runtime/cache` → `rust/wasm-runtime/src/cache.rs`
- ❌ `wasm-runtime/error` → `rust/wasm-runtime/src/error.rs`
- ❌ `wasm-runtime/runner` → `rust/wasm-runtime/src/runner.rs`
- ❌ `wasm-runtime/wasi_env` → `rust/wasm-runtime/src/wasi_env.rs`
