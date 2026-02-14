# Compiler vs Compiler_Core Compatibility Report

## Type System Comparison

### BackendKind Enum

**compiler/backend_types.spl:**
- Interpreter ✓
- Compiler
- Sdn
- CraneliftJit
- LlvmJit
- AutoJit
- Custom(name: text)

**compiler_core/backend_types.spl:**
- Cranelift
- Llvm
- Native
- Wasm
- Lean
- Interpreter ✓
- Cuda
- Vulkan

**Overlap:** Only `Interpreter` is common
**Compatibility:** ❌ INCOMPATIBLE

---

### CodegenTarget Enum

**compiler/backend/backend_types.spl:**
- X86_64 ✓
- AArch64 ✓
- Riscv64 ✓
- X86
- Arm
- Riscv32
- Wasm32
- Wasm64
- CudaPtx(compute_cap)
- VulkanSpirv(version)
- Host ✓

**compiler_core/backend/backend_types.spl:**
- X86_64 ✓
- AArch64 ✓
- Riscv64 ✓
- Native
- Host ✓

**Overlap:** X86_64, AArch64, Riscv64, Host
**Compatibility:** ⚠️ PARTIAL (64-bit targets compatible)

---

## Architecture Comparison

### compiler/ (Production)
- **Focus:** JIT compilation, runtime execution
- **Backends:** Multiple JIT backends (Cranelift, LLVM)
- **Targets:** All architectures (32/64-bit, Wasm, GPU)
- **Use case:** Full-featured compiler with runtime

### compiler_core/ (Bootstrap)
- **Focus:** AOT compilation, bootstrapping
- **Backends:** AOT backends (Cranelift, LLVM, Native)
- **Targets:** Simplified (64-bit only, seed.cpp compatible)
- **Use case:** Self-hosting bootstrap compiler

---

## Can They Interoperate?

### ❌ Direct Type Sharing: NO
The enum types are fundamentally incompatible. You cannot pass a `compiler::BackendKind` to code expecting `compiler_core::BackendKind`.

### ✓ Code Reuse: YES (with adaptation)
Individual algorithms and utilities could be shared if they don't depend on the specific backend enums.

### ⚠️ Conversion Layer: POSSIBLE
Could create a translation layer:
```simple
fn compiler_to_core(kind: compiler.BackendKind) -> compiler_core.BackendKind?:
    match kind:
        case Interpreter: Some(compiler_core.BackendKind.Interpreter)
        case CraneliftJit: Some(compiler_core.BackendKind.Cranelift)
        case LlvmJit: Some(compiler_core.BackendKind.Llvm)
        case _: nil  # No equivalent
```

---

## Recommendations

### Option 1: Keep Separate (Recommended)
- Maintain both as independent implementations
- compiler/ = production runtime compiler
- compiler_core/ = bootstrap/AOT compiler
- No mixing of types between them

### Option 2: Unify Types
- Merge enum definitions
- Make compiler_core a subset of compiler
- Requires significant refactoring
- **Effort:** High

### Option 3: Adapter Pattern
- Create translation layer between the two
- Allow selective interop where needed
- **Effort:** Medium

---

## Test Results

✅ Both modules can be imported simultaneously (no namespace collision)
✅ lexer.spl parse error fixed - compiler/ now loads
❌ Types cannot be mixed directly
⚠️ Partial overlap on 64-bit targets only

---

## Conclusion

**Status: INCOMPATIBLE but COEXISTABLE**

The two implementations serve different purposes:
- **compiler/**: Full-featured production compiler
- **compiler_core/**: Simplified bootstrap compiler

They cannot share backend types but can exist in the same codebase for different use cases.
