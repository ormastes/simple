# Unified Compiler Architecture — Design Document

## Status: Unified (Phases 0-7 Complete)

## 1. Architecture Overview

The Simple compiler is now a **single unified compiler** in `src/compiler/`. The old 4-tier
bootstrap (`compiler_seed/ → compiler_core/ → compiler_shared/ → compiler/`) has been
replaced with a C/C++ backend for bootstrap.

**New bootstrap approach** (like Go/Zig):
```
compiler --backend=c → generates C++20 → committed to src/compiler_cpp/
                                          → CMake + Ninja + Clang builds it
```

Anyone can bootstrap from scratch with just CMake + Clang.

## 2. Current Architecture

```
+===================================================================+
|              src/compiler/ (Unified Compiler)                       |
|                                                                    |
|  core/        (lexer, parser, AST, tokens, types, AOP, interpreter)|
|  backend/     (C/C++, LLVM, Cranelift, Native, Wasm, CUDA, Vulkan) |
|  blocks/      (block definition system)                            |
|  interpreter/ (shared interpreter code)                            |
|  mir_data     (MIR types)                                          |
|  hir          (HIR types + lowering)                               |
|  type_infer   (bidirectional, constraints)                         |
|  monomorphize (generic specialization)                             |
|  borrow_check / traits / effects                                   |
|  mir_opt      (const_fold, dce, inline, cse...)                    |
|  linker/      (ELF, Mach-O, WASM linking)                         |
|  loader/      (module loading, JIT)                                |
|  mdsoc/       (Multi-Dimensional Separation of Concerns)           |
|  driver       (full pipeline orchestration)                        |
+===================================================================+

src/compiler_cpp/   → Generated C++20 output (CMakeLists.txt + *.cpp files)
src/compiler_core/  → Build infra only (CMakeLists.txt, legacy)
src/compiler_seed/  → C runtime only (runtime.c, runtime.h, platform/)
```

## 3. C Backend Bootstrap

The C backend (`src/compiler/backend/c_backend.spl`) translates MIR to C++20:
- `CTypeMapper`: Maps MIR types → C++ types (int64_t, double, void*, etc.)
- `CIRBuilder`: Builds C++ source strings with indentation
- `MirToC`: Main translator handling all MIR instructions and terminators
- `CCodegenBackend`: Backend interface used by `BackendFactory`

The MIR-based C backend is fully wired into the compiler pipeline:
- `CompilerDriver.aot_compile()` detects `--backend=c` and routes to `compile_to_c()`
- `compile_to_c()` translates all MIR modules via `compile_module_with_backend("c", ...)`
- Output is written directly to the specified file via `rt_file_write_text()`

Bootstrap workflow:
1. `bin/simple compile --backend=c -o src/compiler_cpp/ src/app/cli/main.spl` → generates C++20
2. Output committed to `src/compiler_cpp/`
3. `cmake -B build -G Ninja -DCMAKE_CXX_COMPILER=clang++ -DCMAKE_C_COMPILER=clang -S src/compiler_cpp`
4. `ninja -C build` → `build/simple`
5. `mkdir -p bin/bootstrap/cpp && cp build/simple bin/bootstrap/cpp/simple`
6. `bin/bootstrap/cpp/simple build` → self-host verification

Build generated C++ (single-file):
```bash
clang++ -std=c++20 -O2 output.cpp src/compiler_seed/runtime.c -I src/compiler_seed -o output
```

Build generated C++ (multi-file via CMake):
```bash
cmake -B build -G Ninja -DCMAKE_CXX_COMPILER=clang++ -DCMAKE_C_COMPILER=clang -S src/compiler_cpp
ninja -C build
```

## 4. Import Paths

After unification:
- `use compiler.X` — compiler modules (backends, HIR, MIR, linker, etc.)
- `use compiler.core.X` — core types (tokens, lexer, parser, AST, types)
- `use compiler_shared.X` — removed (merged into `compiler.X`)
- `use compiler_core.X` — removed (merged into `compiler.core.X`)

## 4. Core Compilation Paths

### Path A: AST-Direct (--emit-c)
```
source.spl --> lexer --> parser --> AST --> c_codegen --> output.cpp
```
Simple, fast. No optimizations. Good for bootstrapping.

### Path B: HIR/MIR Pipeline (--backend=c)
```
source.spl --> lexer --> parser --> AST --> hir_lower --> HIR
    --> monomorphize --> mir_lower --> MIR --> optimize --> MirToC --> output.cpp
```
Full pipeline with MIR optimizations. Wired end-to-end via `CompilerDriver.compile_to_c()`.
Usage: `bin/simple compile --backend=c -o output.cpp source.spl`

### Path C: Interpreter (--interpret)
```
source.spl --> lexer --> parser --> AST --> eval (tree-walk + JIT)
```
Existing path. Already working (604/604 tests passing).

## 5. WFFI Architecture

### Core WFFI (runtime dlopen)
```simple
extern fn rt_dlopen(path: text) -> i64
extern fn rt_dlsym(handle: i64, name: text) -> i64
extern fn rt_dlclose(handle: i64) -> bool
extern fn rt_wffi_call(fn_ptr: i64, arg_types: [i64], args: [i64]) -> i64
```

Simple API: `wffi_load`, `wffi_get`, `wffi_call_i64`, `wffi_call_text`, `wffi_free`

### Full WFFI Extensions
- `header_parser`: Parse C `.h` files, extract fn signatures + structs
- `binding_gen`: Auto-generate typed Simple wrappers from headers
- `struct_layout`: Compute sizeof, field offsets, alignment
- `callback_bridge`: Wrap Simple fn as C function pointer
- `lib_manager`: Lazy loading, ref counting, search paths, hot reload

## 6. Implementation Phases

| Phase | Description | Status |
|-------|-------------|--------|
| 1 | Design doc (this file) | DONE |
| 2 | Core C codegen (AST -> C) | DONE |
| 3 | Core HIR lowering (AST -> HIR) | DONE |
| 4 | Core MIR lowering (HIR -> MIR) | DONE |
| 5 | Core MIR codegen (MIR -> C) | DONE |
| 6 | Core WFFI (dlopen/dlsym) | DONE |
| 7 | Core driver integration (compile_to_c, aot_compile routing, CCodegenBackend) | DONE |
| 8 | Migrate full lexer/parser to use core | PLANNED |
| 9 | Full WFFI extensions | PLANNED |
| 10 | SFFI gen + shell library | PLANNED |
| 11 | Fix skipped FFI tests | PLANNED |

## 7. Phase 8 Migration Plan — Full Imports Core

### Goal
Eliminate duplication by having `src/compiler/` import and extend `src/compiler_core/` modules
instead of maintaining parallel implementations.

### File-by-File Migration

| Core File | Full File | Migration Strategy |
|-----------|-----------|-------------------|
| `compiler_core/tokens.spl` | `compiler/tokens.spl` | Full imports core tokens, adds block/GPU/math tokens via extension constants |
| `compiler_core/lexer_struct.spl` (719 lines) | `compiler/lexer.spl` (~2K lines) | Full lexer imports core lexer, extends with block tokens, math mode, unified registry |
| `compiler_core/parser.spl` (1,188 lines) | `compiler/parser.spl` (~1.8K lines) | Full parser imports core parser, extends with generics `<>`, traits, async, macros |
| `compiler_core/ast.spl` + `ast_types.spl` (~940 lines) | `compiler/ast.spl` (~1.5K lines) | Full AST extends core AST with generic types, trait bounds, effects, custom blocks |
| `compiler_core/types.spl` (367 lines) | `compiler/types/` (~2K lines) | Full types import core type IDs, add inference engine + bidirectional checking |

### LLVM Shared Infrastructure

~1,300 lines of LLVM code duplicated between core and full (37% overlap per `LLVM_BACKEND_ARCHITECTURE.md`).
Move shared LLVM infra to `src/compiler_shared/llvm/`:

| Shared Module | Content |
|--------------|---------|
| `llvm/types.spl` | LLVM type mappings (i64->i64, f64->double, text->i8*) |
| `llvm/builder.spl` | Basic block + instruction builder wrappers |
| `llvm/module.spl` | Module creation, function declarations |
| `llvm/codegen_helpers.spl` | Common patterns (alloca+store, GEP, casts) |

### Migration Order

1. **Tokens first** — lowest dependency, highest reuse
2. **AST types** — core AST structs become base, full extends
3. **Lexer** — full lexer wraps core lexer, adds state for blocks/math
4. **Parser** — full parser calls core parser for base syntax, adds extension rules
5. **Types** — full type system imports core type IDs
6. **LLVM shared** — extract common LLVM patterns to compiler_shared

### Constraints

- Core must remain seed-compilable (no generics, no closures)
- Full can freely use the full language
- Import direction: full → core only (never core → full)
- compiler_shared may depend on core but not on full

## 8. Verification Strategy

1. **Seed builds core:** All core files compile through seed_cpp
2. **Core compiles itself:** core_compiler can compile core .spl files
3. **Full test suite passes:** 604+ tests passing after each phase
4. **WFFI works:** Load .so, call foreign function, get correct result

## 9. Key Files

- `src/compiler/backend/c_backend.spl` — MIR-to-C++20 translator (MirToC, CCodegenBackend)
- `src/compiler/backend/c_type_mapper.spl` — MIR type → C++ type mapping
- `src/compiler/backend/c_ir_builder.spl` — C++ source string builder
- `src/compiler/backend/backend_helpers.spl` — compile_module_with_backend() routing
- `src/compiler/backend/backend_factory.spl` — BackendFactory (CCodegen case)
- `src/compiler/driver.spl` — CompilerDriver (compile_to_c, aot_compile C routing)
- `src/app/compile/c_mir_backend.spl` — CLI entry script for MIR C backend
- `src/app/compile/c_codegen.spl` — AST-direct C codegen (Path A, legacy)
- `src/compiler_seed/runtime.c` — C runtime (linked with generated C++)
