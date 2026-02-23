# Architecture Skill - Simple Compiler

## Compilation Pipeline

Unified compiler with numbered layers in `src/compiler/`. The layer prefix (NN.name/) is stripped for imports.

### Default Runtime (Core Interpreter)

Used by `bin/simple file.spl`, `bin/simple test`. The pre-built runtime (`bin/release/simple`) invokes this via FFI.

Frontend: `compiler/10.frontend/core/` (no treesitter, no block resolution)

```
Source (.spl)
    │
    ▼
┌──────────────────┐
│ Source Desugar    │  app/desugar/ — 7 text-level passes
│ (static methods, │  (traits, enums, forwarding, context params)
│  enums, traits)  │
└──────────────────┘
    │
    ▼
┌──────────────────┐
│ Lexer            │  compiler/10.frontend/core/lexer.spl
│                  │  → Token stream (INDENT/DEDENT, keywords, operators)
└──────────────────┘
    │
    ▼
┌──────────────────┐
│ Parser           │  compiler/10.frontend/core/ — recursive descent + Pratt
│                  │  → AST (arena: exprs, stmts, decls)
└──────────────────┘
    │
    ▼
┌──────────────────────────────────────────────┐
│ Core Interpreter  compiler/95.interp/        │
│                                              │
│  resolve_module_locals() → eval_module()     │
│       │                                      │
│       ├─ Cold: eval_expr/eval_stmt           │
│       │  (direct AST tree-walk)              │
│       │                                      │
│       └─ Hot (JIT): AST→HIR→MIR→native      │
│          (threshold-based, adaptive)         │
│          Cranelift/LLVM via SFFI             │
│                                              │
│  Hybrid: InterpCall/InterpEval MIR insts     │
│  bridge compiled ↔ interpreted functions     │
└──────────────────────────────────────────────┘
```

### Full Compilation Pipeline

Used by `bin/simple build`, `CompilerDriver.compile()`.

Frontend: `compiler/10.frontend/` (with treesitter outline + block resolution)

```
Source (.spl)
    │
    ▼
┌──────────────────┐
│ Source Desugar    │  app/desugar/ — 7 text-level passes
│ (static methods, │  (traits, enums, forwarding, context params)
│  enums, traits)  │
└──────────────────┘
    │
    ▼
┌──────────────────┐
│ Preprocessor     │  preprocess_conditionals() — @when/@cfg
└──────────────────┘
    │
    ▼
┌──────────────────┐
│ Lexer            │  compiler/10.frontend/core/lexer.spl
│                  │  → Token stream
└──────────────────┘
    │
    ▼
┌──────────────────┐
│ TreeSitter       │  compiler/10.frontend/treesitter/ — Pure Simple outline parser
│ (outline)        │  Walks tokens, extracts module structure, skips bodies,
│                  │  captures DSL block payloads (m{}, sh{}, sql{})
│                  │  → OutlineModule
└──────────────────┘
    │
    ▼
┌──────────────────┐
│ Block Resolver   │  compiler/15.blocks/ — resolves captured DSL blocks
│                  │  Calls each block's parse_full() handler
│                  │  3-phase: sub-lex → treesitter outline → full parse
└──────────────────┘
    │
    ▼
┌──────────────────┐
│ Parser           │  compiler/10.frontend/core/ — full AST parse
│                  │  with pre-resolved blocks
│                  │  → AST (arena: exprs, stmts, decls)
└──────────────────┘
    │
    ▼
┌──────────────────┐
│ AST Desugar      │  compiler/ — async/generator/spawn transforms
│ (async, gen)     │
└──────────────────┘
    │
    ▼
┌──────────────────┐
│ Type Checking    │  compiler/30.types/ — inference + checking
│ + Inference      │
└──────────────────┘
    │
    ▼
┌──────────────────┐
│ Monomorphization │  compiler/40.mono/ — generic specialization
└──────────────────┘
    │
    ▼
┌──────────────────┐
│ HIR Lowering     │  compiler/20.hir/ — name resolution + type annotation
│                  │  → HIR (structured control flow)
└──────────────────┘
    │
    ▼
┌──────────────────┐
│ AOP Weaving      │  compiler/90.tools/ — HIR join-point detection
│ [STUBBED]        │  Currently no-op — see TODO below
└──────────────────┘
    │
    ▼
┌──────────────────┐
│ MIR Lowering     │  compiler/50.mir/ — HIR → flat basic blocks
│                  │  → MIR (50+ instructions, effect tags)
└──────────────────┘
    │
    ▼
┌──────────────────┐
│ MIR Optimization │  compiler/60.mir_opt/ — copy propagation, etc.
└──────────────────┘
    │
    ▼
┌───────────────────────────────────────────────────┐
│                  Backend Selection                  │
│                                                     │
│  Debug ──→ Cranelift  (fast compile)               │
│  Release → LLVM       (optimized)                  │
│                                                     │
│  Also: C, Native (x86/ARM/RISC-V), WASM, CUDA,   │
│        Vulkan/SPIR-V, VHDL, Lean                   │
└───────────────────────────────────────────────────┘
    │
    ▼
┌──────────────────┐
│ Linker           │  compiler/70.backend/linker/ — SMF binary format
│                  │  Backends: mold (Linux), MSVC (Windows)
└──────────────────┘
    │
    ▼
┌──────────────────┐
│ Loader           │  compiler/99.loader/ — mmap-based SMF loading
└──────────────────┘
    │
    ▼
  Execution
```

### TODO: Wire AOP weaving at HIR level

**Current state:** AOP is stubbed — `AopWeaver.weave()` is a no-op. `detect_join_points()` operates on `MirBlockInfo`.

**Planned change:** Move AOP weaving to HIR level (after HIR lowering, before MIR lowering).

**Work needed:**
- Rewrite `detect_join_points()` to work on HIR nodes instead of `MirBlockInfo`
- Wire `AopWeaver.weave()` into full pipeline after HIR lowering
- Update pipeline order to: `monomorphize → HIR → AOP weave → MIR → optimize → codegen`

## Full Pipeline — MDSOC Feature Stages

Each stage is a `feature/` module with typed port contracts. Stage boundaries enforced by entity-view adapters.

```
┌─────────────────────────────────────────────────────────────────┐
│                     MDSOC Pipeline Stages                       │
│                                                                 │
│  module_loading ─→ LoadedModuleView ─→ lexing                  │
│       │                                    │                    │
│       │                              TokenStreamView            │
│       │                                    │                    │
│       │                                 parsing                 │
│       │                                    │                    │
│       │                               AstView                   │
│       │                                    │                    │
│       │                              desugaring                 │
│       │                                    │                    │
│       │                             DesugarView                 │
│       │                                    │                    │
│       │                            type_checking                │
│       │                                    │                    │
│       │                           TypedAstContext               │
│       │                                    │                    │
│       │                            hir_lowering                 │
│       │                                    │                    │
│       │                             CfgContext                  │
│       │                           (structured→flat)             │
│       │                                    │                    │
│       │                            mir_lowering                 │
│       │                                    │                    │
│       │                             MirOptView                  │
│       │                                    │                    │
│       │                           optimization                  │
│       │                                    │                    │
│       │         ┌──── monomorphization ────┤                    │
│       │         │                          │                    │
│       │         │                     MirProgram                │
│       │         │                          │                    │
│       │         │                       codegen                 │
│       │         │                          │                    │
│       │         │                   ObjectFileView              │
│       │         │                          │                    │
│       │         │                       linking                 │
│       │         │                          │                    │
│       │         └──── events (diagnostics, progress) ──→        │
│                                                                 │
└─────────────────────────────────────────────────────────────────┘
```

### Stage Port Contracts (MDSOC)

| Stage | Input Port | Output Port |
|-------|-----------|-------------|
| Lexing | `source_text` | `token_tags[], token_texts[], token_lines[], token_cols[], token_count` |
| Parsing | token arrays | `expr_count, stmt_count, decl_count, root_decls[], errors[]` |
| Desugaring | `source_text, module_name` | `desugared_source, injected_fn_names[], pass_count` |
| Type Checking | typed decls | `symbol_count, inferred_type_count` |
| HIR Lowering | `module_name, typed_decl_count` | `functions: [HirFunction], struct_count, error_count` |
| MIR Lowering | `module_name, function_count` | `function_count, extern_fn_names[], string_literal_count` |
| Codegen | `function_count, extern_fn_count` | `object_byte_count, symbol_count, target_triple, success` |

### Transform Entity Views

| Boundary | View | Key fields |
|----------|------|------------|
| lexing → parsing | `TokenStreamView` | Adapts LexerOutputPort arrays for parser |
| parsing → desugaring | `AstView` / `AstDesugarView` | `source_text, root_decl_count, module_name` |
| desugaring → typing | `DesugarView` | Desugared source for type checker |
| typing → hir | `TypedAstContext` | `ast_decl_count, symbol_count, inferred_type_count` |
| hir → mir | `CfgContext` | `current_fn_name, loop_depth, break/continue stacks` |
| mir → optimizer | `MirOptView` | Copy-prop and other optimization inputs |
| mir → backend | `MirProgram` | `function_count, extern_fn_names, target_triple` |
| backend → linker | `ObjectFileView` | Object file for linking |
| loading → parsing | `LoadedModuleView` | Loaded module for re-parse |

---

## Module Dependency Graph

```
cli (CLI entry) ──────────────────────────────┐
    │                                         │
    ├── compiler (numbered layers) ────────────┤
    │       │                                 │
    │       └── std (Standard library) ───────┤
    │                                         │
    ├── app (Applications) ───────────────────┤
    │   ├── build (Build system)              │
    │   ├── desugar (Source-level desugar)     │
    │   ├── mcp (MCP server)                  │
    │   ├── io (SFFI I/O)                     │
    │   └── test_runner (Test framework)      │
    │                                         │
    └── lib (Libraries) ──────────────────────┘
        └── database (SDN tables, atomic ops)
```

## Key Directories

### Source Code (`src/`)
```
src/
├── app/              # Applications (100% Simple)
│   ├── build/        # Self-hosting build system
│   ├── cli/          # CLI entry point
│   ├── mcp/          # MCP server
│   ├── desugar/      # Source-level desugaring (7 passes)
│   ├── fix/          # EasyFix auto-corrections
│   ├── lint/         # Linter
│   ├── io/           # I/O module (SFFI)
│   └── test_runner_new/ # Test runner + SDoctest
├── lib/              # Libraries
│   └── database/     # Database library (SDN tables, atomic ops)
├── std/              # Standard library (symlink to lib/)
│   ├── spec.spl      # SSpec BDD framework
│   ├── text.spl, array.spl, math.spl, path.spl
│   └── platform/     # Cross-platform support
├── compiler_cpp/     # Generated C code + runtime (bootstrap via CMake+Ninja)
│   ├── CMakeLists.txt
│   ├── *.cpp, *.c    # Generated C code
│   └── runtime/      # C runtime (runtime.c/runtime.h)
└── compiler/         # Unified compiler — numbered layers
    ├── 00.common/    # Error types, config, effects, visibility, diagnostics, registry
    ├── 10.frontend/  # Lexer, parser, AST, treesitter, desugar, parser types
    │   └── core/     # Core frontend (lexer.spl, parser.spl, ast.spl, tokens.spl)
    ├── 15.blocks/    # Block definition system (22 files)
    ├── 20.hir/       # HIR types, definitions, lowering, inference
    ├── 25.traits/    # Trait def, impl, solver, coherence, validation
    ├── 30.types/     # Type inference, type system, dimension constraints
    ├── 35.semantics/ # Semantic analysis, lint, macro check, resolve, const eval
    ├── 40.mono/      # Monomorphization (18 files), instantiation
    ├── 50.mir/       # MIR types, data, instructions, lowering, serialization
    ├── 55.borrow/    # Borrow checking, GC analysis
    ├── 60.mir_opt/   # MIR optimization passes (17 files)
    ├── 70.backend/   # Backends (C, LLVM, Cranelift, WASM, CUDA, Vulkan, Native, Lean)
    │   ├── backend/  # Backend implementations
    │   └── linker/   # SMF format, mold/MSVC linker wrappers
    ├── 80.driver/    # Driver, pipeline, project, build mode, incremental
    ├── 85.mdsoc/     # MDSOC (virtual capsules, feature, transform, weaving)
    ├── 90.tools/     # API surface, coverage, query, symbol analyzer, AOP
    ├── 95.interp/    # Interpreter, MIR interpreter, execution
    └── 99.loader/    # Module resolver, loader
```

## Source-Level Desugaring Passes

Runs **before** lexing, rewrites source text (`app/desugar/mod.spl`):

| Pass | Module | Transformation |
|------|--------|----------------|
| -2 | `context_params.spl` | `context val name: Type` → module var + with_context wrapper |
| -1 | `trait_desugar.spl` | `trait Repo: fn find()` → struct with fn fields |
| 0 | `forwarding.spl` | `alias fn push = inner.push` → delegation method |
| 1 | `static_constants.spl` | `impl T: static val X = v` → `val T__X = v` |
| 2 | `static_methods.spl` | `impl T: static fn f()` → `fn T__f()` |
| 3 | `enum_constructors.spl` | Enum variant factory functions |
| 4 | `rewriter.spl` | `T.method()` → `T__method()` call-site rewrite |

## Block Parser System

Custom DSL blocks use a **3-phase parsing** architecture (`compiler/15.blocks/`):

| Phase | Method | Purpose |
|-------|--------|---------|
| 1 | `lex(payload, pre_lex, ctx)` | Fast sub-lexer (brace tracking) |
| 2 | `treesitter_outline(payload, pre_lex)` | IDE structural extraction |
| 3 | `parse_full(payload, pre_lex, ctx)` | Full block parse → AST nodes |

Builtin blocks: `m{ x^2 }` (math), `sh{...}` (shell), `sql{...}`, data blocks, loss blocks (ML).

Block registry: `register_block(name, definition)`, `is_block(name)`, `with_block(name, fn)`.

## AOP (Aspect-Oriented Programming)

MIR-level weaving at `compiler/90.tools/`:

- **Pointcuts**: `NamePattern` (glob), `Annotation` (`@tag`), `Module` (path), `All`
- **Advice**: `Before`, `AfterSuccess`, `AfterError`, `Around`
- **Join points**: `Execution` (fn entry), `Decision` (branch/pattern), `Condition` (comparison), `Error` (try_unwrap)
- **Pipeline**: `detect_join_points()` → `match_advice_for_join_point()` → `weave_function()`
- Config via SDN and `pc{...}` predicate islands

## Backend Details

| Backend | Mode | File(s) |
|---------|------|---------|
| **C** | Bootstrap | `c_backend.spl`, `c_ir_builder.spl`, `c_type_mapper.spl` |
| **Cranelift** | Debug/JIT | `compiler.spl`, `cranelift_type_mapper.spl` |
| **LLVM** | Release | `llvm_backend.spl`, `llvm_ir_builder.spl`, `llvm_target.spl` |
| **Native** | Bare-metal | `native/isel_x86_64.spl`, `isel_aarch64.spl`, `isel_riscv{32,64}.spl`, `regalloc.spl`, `elf_writer.spl`, `macho_writer.spl` |
| **WASM** | Web | `wasm_backend.spl`, `wasm/wat_codegen.spl` |
| **CUDA** | GPU | `cuda_backend.spl`, `cuda/ptx_builder.spl` |
| **Vulkan** | GPU | `vulkan_backend.spl`, `vulkan/spirv_builder.spl` |
| **VHDL** | FPGA | `vhdl_backend.spl`, `vhdl/vhdl_builder.spl` |
| **Interpreter** | Test | Wraps tree-walker as `BackendPort` |
| **Lean** | Verify | `lean_backend.spl`, `lean_borrow.spl` |

Selection: `select_backend_with_mode(target, mode, nil)` in `backend_selector.spl`.

## MIR Instruction Categories

| Category | Count | Examples |
|----------|-------|----------|
| Core | 6 | ConstInt, ConstFloat, BinOp, UnaryOp, Copy |
| Memory | 6 | Load, Store, LocalAddr, GetElementPtr, GcAlloc |
| Collections | 7 | ArrayLit, TupleLit, DictLit, IndexGet, IndexSet, Spread |
| Strings | 3 | ConstString, ConstSymbol, FStringFormat |
| Closures | 2 | ClosureCreate, IndirectCall |
| Objects | 3 | StructInit, FieldGet, FieldSet |
| Methods | 3 | MethodCallStatic, MethodCallVirtual, BuiltinMethod |
| Patterns | 4 | PatternTest, PatternBind, EnumDiscriminant, EnumPayload |
| Enums | 2 | EnumUnit, EnumWith |
| Async | 5 | FutureCreate, Await, ActorSpawn, ActorSend, ActorRecv |
| Generators | 3 | GeneratorCreate, Yield, GeneratorNext |
| Errors | 5 | TryUnwrap, OptionSome, OptionNone, ResultOk, ResultErr |
| Fallback | 2 | InterpCall, InterpEval |
| Contracts | 2 | ContractCheck, ContractOldCapture |

Each instruction has an effect tag: `Compute`, `Io`, `Wait`, `GcAlloc`.

## Bootstrap Chain (C Backend)

```
Phase 0: C/C++ compiler (clang/gcc/MSVC)
Phase 1: bin/simple compile --backend=c  →  generates C code into src/compiler_cpp/
Phase 2: cmake + ninja  →  builds C code + runtime.c  →  bootstrap binary
```

Commands:
```bash
bin/simple compile --backend=c -o src/compiler_cpp/ src/app/cli/main.spl
cmake -B build -G Ninja -DCMAKE_CXX_COMPILER=clang++ -DCMAKE_C_COMPILER=clang -S src/compiler_cpp
ninja -C build
mkdir -p bin/bootstrap/cpp && cp build/simple bin/bootstrap/cpp/simple
```

## Stdlib Variant System

### Memory Model Matrix

| Directory | GC | Mutable |
|-----------|-----|---------|
| `gc_sync_mut/` | Yes | Yes |
| `gc_sync_immut/` | Yes | No |
| `nogc_sync_mut/` | No | Yes |
| `nogc_sync_immut/` | No | No |
| `gc_async_mut/` | Yes | Yes + Async |
| `nogc_async_mut/` | No | Yes + Async |

## Adding New Features

1. **Lexer/Parser**: `src/compiler/10.frontend/core/lexer.spl`, `parser.spl`
2. **Source desugar**: `src/app/desugar/` (if new syntax sugar)
3. **Block parsers**: `src/compiler/15.blocks/` (if new DSL block)
4. **Type system**: `src/compiler/30.types/`
5. **HIR lowering**: `src/compiler/20.hir/`
6. **AOP rules**: `src/compiler/90.tools/` (if new join-point kind)
7. **MIR lowering**: `src/compiler/50.mir/`
8. **Backend**: `src/compiler/70.backend/` (if new instruction)
9. **Standard library**: `src/lib/`
10. **Tests**: `test/`

## Architecture Rules

- `src/compiler/` uses numbered layers — lower numbers cannot depend on higher numbers
- `src/lib/` is the standard library (imports use `std.X` which resolves to `lib`)
- `src/app/cli/` is the only CLI entry point
- No circular dependencies between modules
- MDSOC `arch {}` blocks enforce stage isolation

### Module Dependency Rules

| Layer | May Access | May Not Access |
|-------|------------|----------------|
| `src/app/cli/` | all | - |
| `src/compiler/` | lib, std | app |
| `src/lib/` | (no deps on compiler) | compiler, app |

---

## Lean 4 Verification

### Verification Projects

```
verification/
├── type_inference_compile/    # Type inference soundness
├── memory_capabilities/       # Reference capabilities (mut T, iso T)
├── memory_model_drf/          # SC-DRF memory model
├── manual_pointer_borrow/     # Borrow checker model
├── gc_manual_borrow/          # GC safety proofs
├── async_compile/             # Effect tracking
├── nogc_compile/              # NoGC instruction safety
├── module_resolution/         # Module path resolution
├── visibility_export/         # Export visibility rules
└── macro_auto_import/         # Macro import safety
```

### Lean Generation Commands

```bash
simple gen-lean generate                    # All projects
simple gen-lean generate --project memory   # Specific project
simple gen-lean compare                     # Show status
simple gen-lean compare --diff              # Show differences
simple gen-lean write --force               # Regenerate all
```

### When Modifying Type Inference

1. Update `src/compiler/30.types/`
2. Update Lean theorems in `verification/type_inference_compile/`
3. Run `lake build` in verification project
4. Run `simple gen-lean compare` to verify alignment

---

## Design Checklist

### Before Implementing

- [ ] Read relevant feature spec (`doc/feature/`)
- [ ] Identify affected pipeline stages
- [ ] Draw dependency impact diagram

### After Implementing

- [ ] Run `bin/simple test` - all tests pass
- [ ] Run `simple gen-lean compare` - if verification affected
- [ ] Update Lean proofs if needed (`lake build`)

## See Also

- **`doc/guide/architecture_writing.md`** - Architecture writing guide
- `doc/architecture/README.md` - Full architecture docs
- `doc/architecture/file_class_structure.md` - Codebase inventory
- `doc/codegen_technical.md` - Codegen details
- `doc/codegen/status.md` - MIR coverage
- `doc/formal_verification.md` - Lean verification docs
- `CLAUDE.md` - Project structure
