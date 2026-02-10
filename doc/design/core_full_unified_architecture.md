# Core/Full Unified Architecture — Design Document

## Status: Implementation In Progress (Phase 7 Complete)

## 1. Problem Statement

Currently, Core Simple (`src/core/`, ~8.8K lines) and Full Simple (`src/compiler/`, ~123K lines)
are completely separate implementations with duplicated lexer, parser, AST, HIR types, and MIR types.
Core has no codegen. Full cannot reuse core.

**Duplication map:**
- Lexer: `src/core/lexer_struct.spl` (719 lines) vs `src/compiler/lexer.spl` (~2K lines)
- Parser: `src/core/parser.spl` (1,188 lines) vs `src/compiler/parser.spl` (~1.8K lines)
- AST: `src/core/ast.spl` + `ast_types.spl` (~940 lines) vs `src/compiler/ast.spl` (~1.5K lines)
- Types: `src/core/types.spl` (367 lines) vs `src/compiler/types/` (~2K lines)

## 2. Target Architecture

```
 SEED (C++)                          core is deployable alone
      | builds                       |
      v                              v
+===================================================================+
|                    src/core/ (Seed-Compilable)                     |
|                                                                   |
|  tokens --> lexer --> parser --> ast (struct pools, int tags)      |
|                                  |                                |
|           +----------+-----------+-----------+----------+         |
|           v          v           v           v          v         |
|    interpreter   c_codegen   hir_lower   mir_lower    wffi       |
|    (eval+JIT)    (AST->C)   (AST->HIR)  (HIR->MIR) (dlopen)     |
|                                              |                    |
|                                         mir_codegen               |
|                                         (MIR->C)                  |
|                                                                   |
|  types  error  driver (orchestrates all)                          |
+===================================================================+
                         |
               Full IMPORTS and EXTENDS
                         |
+===================================================================+
|              src/compiler/ (Compiled-Only Extensions)              |
|                                                                   |
|  lexer_ext    (blocks, math mode, unified registry)               |
|  parser_ext   (generics <>, traits, async, macros)                |
|  hir_ext      (generic types, trait bounds, effects)              |
|  type_infer   (bidirectional, constraints)                        |
|  monomorphize (generic specialization)                            |
|  borrow_check / traits / effects                                  |
|  mir_ext + mir_opt (const_fold, dce, inline, cse...)              |
|  wffi_ext     (header_parser, binding_gen, struct_layout,         |
|                callback_bridge, lib_manager)                      |
|  backend/     (cranelift, llvm, native ELF, wasm, cuda)           |
|  driver       (full pipeline orchestration)                       |
+===================================================================+
```

## 3. Module Boundaries

### Core (Seed-Compilable)
Everything in `src/core/` must compile through `seed_cpp`. Constraints:
- No generics (`<T>` syntax)
- No closures/lambdas
- No traits or impl blocks with dynamic dispatch
- No exception handling (try/catch/throw)
- No multi-line boolean expressions
- All types are concrete: i64, f64, text, bool, [i64], [text], named structs
- Integer tags for enums/variants (no enum payloads)
- Struct pools instead of generic containers
- `var`/`val` for all variables

### Full (Compiled-Only)
Everything in `src/compiler/` may use the full language. It:
- Imports from core and extends it
- Adds generics, traits, async, macros
- Has multiple backends (cranelift, llvm, native, wasm, cuda)
- Full type inference with bidirectional checking

## 4. Core Compilation Paths

### Path A: AST-Direct (--emit-c)
```
source.spl --> lexer --> parser --> AST --> c_codegen --> output.cpp
```
Simple, fast. No optimizations. Good for bootstrapping.

### Path B: HIR/MIR Pipeline (--emit-c-mir)
```
source.spl --> lexer --> parser --> AST --> hir_lower --> HIR
    --> mir_lower --> MIR --> mir_codegen --> output.cpp
```
Enables future optimizations at MIR level.

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
| 7 | Core driver integration | DONE |
| 8 | Migrate full lexer/parser to use core | PLANNED |
| 9 | Full WFFI extensions | PLANNED |
| 10 | SFFI gen + shell library | PLANNED |
| 11 | Fix skipped FFI tests | PLANNED |

## 7. Verification Strategy

1. **Seed builds core:** All core files compile through seed_cpp
2. **Core compiles itself:** core_compiler can compile core .spl files
3. **Full test suite passes:** 604+ tests passing after each phase
4. **WFFI works:** Load .so, call foreign function, get correct result

## 8. Key Files

- `src/core/compiler/c_codegen.spl` — AST-direct C codegen (Phase 2)
- `src/core/compiler/driver.spl` — Compiler driver
- `src/core/hir/lowering.spl` — HIR lowering (Phase 3)
- `src/core/mir/lowering.spl` — MIR lowering (Phase 4)
- `src/core/compiler/mir_codegen.spl` — MIR-to-C codegen (Phase 5)
- `src/core/wffi/mod.spl` — WFFI module (Phase 6)
