# Compiler vs Compiler_Core Compatibility Analysis

## Summary

**Finding**: `src/compiler/` and `src/compiler_core_legacy/` are **NOT compatible** - they have completely different backend type definitions and appear to be separate implementations.

## Key Differences

### BackendKind Enum

**src/compiler/backend_types.spl**:
```simple
enum BackendKind:
    Interpreter
    Compiler
    Sdn
    CraneliftJit
    LlvmJit
    AutoJit
    Custom(name: text)
```

**src/compiler_core_legacy/backend_types.spl**:
```simple
enum BackendKind:
    Cranelift
    Llvm
    Native
    Wasm
    Lean
    Interpreter
    Cuda
    Vulkan
```

### CodegenTarget Enum

**src/compiler/backend/backend_types.spl**:
```simple
enum CodegenTarget:
    X86_64
    AArch64
    Riscv64
    X86
    Arm
    Riscv32
    Wasm32
    Wasm64
    CudaPtx(compute_cap: (i64, i64))
    VulkanSpirv(version: (i64, i64))
    Host
```

**src/compiler_core_legacy/backend/backend_types.spl**:
```simple
enum CodegenTarget:
    X86_64
    AArch64
    Riscv64
    Native
    Host
```
(Note: compiler_core_legacy already has simplified enums for seed.cpp compatibility)

## File Counts

- `src/compiler/`: 415 .spl files
- `src/compiler_core_legacy/`: 441 .spl files

## Parse Error Issue

**Error**: `error: compile failed: parse: in "/home/ormastes/dev/pub/simple/src/compiler/lexer.spl": Unexpected token: expected expression, found Indent`

This prevents using `bin/release/simple` to compile `src/compiler/main.spl`.

## Architecture Analysis

These appear to be **two different compiler implementations**:

1. **src/compiler/** - Full-featured compiler with:
   - JIT backends (CraneliftJit, LlvmJit, AutoJit)
   - Custom backend support
   - SDN backend
   - All target architectures (32-bit, 64-bit, WebAssembly, GPU)

2. **src/compiler_core_legacy/** - Core compiler with:
   - AOT backends (Cranelift, Llvm, Native)
   - Lean verification export
   - Simplified targets (64-bit only, Native, Host)
   - Already aligned with seed.cpp limitations

## Compatibility Status

❌ **NOT Compatible** - Cannot mix types between the two implementations

The two compilers have:
- Different backend architectures
- Different enum definitions
- Different file structures
- Different capabilities

## Recommendations

### Option 1: Use compiler_core_legacy (Recommended)
- Already has seed.cpp-compatible types
- Successfully transpiles (375 files → 20,005 C++ lines)
- Only blocked by seed_cpp transpiler bugs
- Clean architecture

### Option 2: Use compiler (Current Production)
- Full-featured with all backends
- But has parse error preventing compilation
- Would need to fix src/compiler/lexer.spl parse error
- Not aligned with seed.cpp (has GPU targets, 32-bit, etc.)

### Option 3: Merge/Align
- Align src/compiler/ enums with src/compiler_core_legacy/
- Fix parse error in src/compiler/lexer.spl
- Significant refactoring required

## Next Steps

1. **Fix parse error** in src/compiler/lexer.spl
2. **Choose** which compiler to use as the canonical version
3. **Decide** whether to merge or maintain separately

## Current Working Status

- ✅ bin/release/simple - Works for basic code
- ❌ bin/release/simple src/compiler/main.spl - Parse error
- ✅ bin/release/simple -c "print('test')" - Works
- ✅ compiler_core_legacy transpilation - Works (seed_cpp bugs only)
- ❌ compiler compilation - Blocked by parse error
