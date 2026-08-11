# Rust to Simple Migration Status Summary - 2026-02-03

## Executive Summary

Analyzed the codebase to determine which Rust modules should be migrated to Simple for self-hosting. The compiler is **partially self-hosted** - high-level logic is in Simple, performance-critical implementations remain in Rust.

## Architecture Pattern

The codebase follows a **hybrid architecture**:

```
┌─────────────────────────────────────┐
│  Simple (Self-Hosted Layer)        │
│  - Compiler orchestration           │
│  - Type system logic                │
│  - HIR/MIR definitions              │
│  - High-level codegen               │
└──────────────┬──────────────────────┘
               │ FFI calls
┌──────────────▼──────────────────────┐
│  Rust (Performance Layer)           │
│  - Cranelift backend                │
│  - LLVM backend                     │
│  - Runtime (GC, memory, FFI)        │
│  - Low-level codegen                │
└─────────────────────────────────────┘
```

## Module Counts

| Category | Count | Status |
|----------|-------|--------|
| **Total Rust modules** | 1,233 | Analyzed |
| **Infrastructure (Rust-only)** | 125 | ✅ Should stay |
| **Runtime (Rust-only)** | 3 | ✅ Should stay |
| **FFI/Native (Rust-only)** | 103 | ✅ Should stay |
| **Tests (Rust-only)** | 119 | ✅ Should stay |
| **Compiler frontend** | 207 | ⚠️ Partial migration |
| **Needs review** | 676 | 🔍 TBD |

## Detailed Breakdown

### 1. Should Stay in Rust (350 modules) ✅

These are infrastructure, runtime, and performance-critical components:

#### Infrastructure (125 modules)
- Driver binary and startup
- Build tooling
- Database management
- GPU initialization
- Test infrastructure

#### Runtime (3 modules)
- Garbage collector
- Fault detection
- Arena allocator

#### FFI/Native (103 modules)
- FFI bridge implementations
- Native I/O helpers
- Concurrent providers
- External interface implementations

#### Tests/Benchmarks (119 modules)
- Rust unit tests
- Performance benchmarks
- Integration tests

### 2. Compiler Frontend (207 modules) ⚠️

**Status:** Partially migrated with hybrid approach

The compiler is split into:

#### In Simple (src/compiler/)
**High-level orchestration and definitions:**
- `codegen.spl` - Codegen orchestrator
- `hir/` - HIR definitions
- `mir/` - MIR definitions
- `backend.spl` - Backend interface
- `type_infer/` - Type inference
- `resolve/` - Name resolution

**Total Simple files:** ~100+ compiler-related .spl files

#### In Rust (rust/compiler/src/)
**Performance-critical implementations:**

**Codegen backends (81 modules):**
- Cranelift backend (23 modules)
- LLVM backend (12 modules)
- Lean verification backend (10 modules)
- Bytecode compiler (3 modules)
- Instruction implementations (33 modules)

**AST/Parser (29 modules):**
- AST node definitions
- Lexer implementations
- Parser helpers
- AOP integration
- Contract parsing

**MIR Lowering (22 modules):**
- Expression lowering
- Statement lowering
- Type lowering
- GPU lowering
- Optimization passes

**HIR (15 modules):**
- HIR transformations
- Type checking
- Lifetime analysis
- Borrow checking

**Lexer (8 modules):**
- Comment handling
- String escaping
- Number parsing
- Identifier recognition
- Indentation handling

### 3. Needs Review (676 modules) 🔍

These modules need case-by-case evaluation:

**Categories:**
- Common utilities (diagnostics, file reading, safety checks)
- Compiler utilities (API scanning, dependency tracking)
- Interpreter components (evaluation, FFI integration)
- Module system (loading, resolution, exports)

**Already Migrated Examples:**
- ✅ `compiler/api_surface` → `src/compiler/api_surface.spl`
- ✅ `compiler/arch_rules` → `src/compiler/arch_rules.spl`
- ✅ `compiler/build_log` → `src/compiler/build_log.spl`
- ✅ `compiler/build_mode` → `src/compiler/build_mode.spl`

## Migration Philosophy

### What Should Be in Simple

1. **Compiler Orchestration**
   - High-level compilation pipeline
   - Type system definitions
   - IR (HIR/MIR) data structures
   - Module resolution logic

2. **Self-Hosting Benefits**
   - Easy to modify and extend
   - Dogfooding the language
   - Better documentation (code is spec)
   - Faster iteration on language features

3. **Non-Performance-Critical**
   - Configuration management
   - API surface analysis
   - Diagnostic formatting
   - Code navigation tools

### What Should Stay in Rust

1. **Performance-Critical**
   - Code generation (Cranelift/LLVM)
   - Runtime system (GC, memory)
   - Low-level optimization passes

2. **External Dependencies**
   - LLVM bindings
   - Cranelift integration
   - GPU backends (CUDA, Vulkan)

3. **Safety-Critical**
   - Memory management
   - Concurrent primitives
   - FFI boundary handling

## Specific Examples

### Lexer/Parser

**Current Status:** Mostly in Rust

```
rust/parser/src/
├── lexer/           # 8 modules - Low-level tokenization
├── parser/          # Parser combinators and error recovery
└── ast/             # 29 modules - AST node definitions
```

**Recommendation:** Keep in Rust (performance-critical, mature implementation)

**Alternative:** Use tree-sitter integration from Simple (already exists)

### Codegen

**Current Status:** Hybrid

```
src/compiler/
└── codegen.spl      # High-level orchestrator

rust/compiler/src/codegen/
├── cranelift/       # 23 modules - JIT backend
├── llvm/            # 12 modules - AOT backend
├── lean/            # 10 modules - Verification backend
└── instr/           # 33 modules - Instruction implementations
```

**Status:** ✅ Correct architecture - Simple orchestrates, Rust implements

### HIR/MIR

**Current Status:** Hybrid

```
src/compiler/
├── hir/             # HIR definitions and high-level operations
└── mir/             # MIR definitions and high-level operations

rust/compiler/src/
├── hir/             # 15 modules - Type checking, analysis
└── mir/             # 22 modules - Lowering, optimization
```

**Status:** ✅ Correct architecture - Definitions in Simple, heavy lifting in Rust

## Recommendations

### Short Term

1. ✅ **Keep current hybrid architecture** - It's working well
2. ✅ **Don't force migration** - Rust implementations are mature and fast
3. ⚠️ **Document boundaries** - Clarify which modules are Simple vs Rust

### Long Term

1. **Gradual migration** of non-performance-critical modules:
   - Diagnostic formatting
   - API surface analysis
   - Build configuration
   - Module resolution (partially done)

2. **Maintain Rust for**:
   - All code generation backends
   - Runtime system
   - Parser/lexer (or use tree-sitter)
   - Low-level optimizations

3. **Focus Simple development on**:
   - Type system evolution
   - Language feature design
   - Compiler pipeline orchestration
   - Developer tooling

## Statistics Summary

```
Total Codebase:
  Rust files: 1,272
  Rust modules: 1,233
  Rust structs: 1,459
  Rust impl blocks: 1,643
  Rust functions: 8,816

Should Stay in Rust:
  Infrastructure: 125 modules
  Runtime: 3 modules
  FFI: 103 modules
  Tests: 119 modules
  Total: 350 modules (28%)

Compiler Components:
  Codegen backends: 81 modules (stay Rust)
  AST/Parser: 29 modules (stay Rust)
  MIR lowering: 22 modules (stay Rust)
  HIR: 15 modules (partially migrated)
  Lexer: 8 modules (stay Rust)

Migration Target:
  High-priority: ~50 modules (orchestration, config, tools)
  Low-priority: ~150 modules (can stay Rust)
  Not migrating: ~207 modules (performance-critical)
```

## Conclusion

✅ **Current architecture is sound** - Hybrid approach works well

✅ **No urgent migration needed** - Performance-critical code should stay in Rust

⚠️ **Gradual improvement** - Migrate non-critical components over time

🎯 **Focus on value** - Migrate modules that benefit from Simple's flexibility

The "207 unmigrated modules" finding is **not a problem** - most of those modules (codegen backends, low-level implementations) should remain in Rust for performance. The compiler is already successfully self-hosting at the orchestration level.

## Related Reports

- `doc/09_report/ffi_wrapper_audit_2026-02-03.md` - FFI wrapper status
- `doc/09_report/rust_to_simple_migration.md` - Detailed module list
- `doc/09_report/ffi_direct_calls.md` - Direct FFI usage audit
