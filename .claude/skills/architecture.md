# Architecture Skill - Simple Compiler

## Compilation Pipeline

Two frontends exist. Both share `compiler_core/lexer.spl` for tokenization.

### Default Runtime (Core Interpreter)

Used by `bin/simple file.spl`, `bin/simple test`. The Rust runtime (`bin/release/simple`) invokes this via FFI.

Frontend: `compiler_core/frontend.spl` (no treesitter, no block resolution)

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
│ Lexer            │  compiler_core/lexer.spl
│                  │  → Token stream (INDENT/DEDENT, keywords, operators)
└──────────────────┘
    │
    ▼
┌──────────────────┐
│ Parser           │  compiler_core/parser.spl — recursive descent + Pratt
│                  │  → AST (arena: exprs, stmts, decls)
└──────────────────┘
    │
    ▼
┌──────────────────────────────────────────────┐
│ Core Interpreter  compiler_core/interpreter/ │
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

Frontend: `compiler/frontend.spl` (with treesitter outline + block resolution)

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
│ Lexer            │  compiler_core/lexer.spl
│                  │  → Token stream
└──────────────────┘
    │
    ▼
┌──────────────────┐
│ TreeSitter       │  compiler_shared/treesitter.spl — Pure Simple outline parser
│ (outline)        │  Walks tokens, extracts module structure, skips bodies,
│                  │  captures DSL block payloads (m{}, sh{}, sql{})
│                  │  → OutlineModule
└──────────────────┘
    │
    ▼
┌──────────────────┐
│ Block Resolver   │  compiler/blocks/ — resolves captured DSL blocks
│                  │  Calls each block's parse_full() handler
│                  │  3-tier: sub-lex → treesitter outline → full parse
└──────────────────┘
    │
    ▼
┌──────────────────┐
│ Parser           │  compiler_core/parser.spl — full AST parse
│                  │  with pre-resolved blocks
│                  │  → AST (arena: exprs, stmts, decls)
└──────────────────┘
    │
    ▼
┌──────────────────┐
│ AST Desugar      │  compiler/desugar/ — async/generator/spawn transforms
│ (async, gen)     │
└──────────────────┘
    │
    ▼
┌──────────────────┐
│ Type Checking    │  compiler_shared/type_system/ — inference + checking
│ + Inference      │  compiler/inference/ — unify, constraints, deferred
└──────────────────┘
    │
    ▼
┌──────────────────┐
│ Monomorphization │  compiler/monomorphize/ — generic specialization
└──────────────────┘
    │
    ▼
┌──────────────────┐
│ HIR Lowering     │  compiler/hir_lowering/ — name resolution + type annotation
│                  │  → HIR (structured control flow)
└──────────────────┘
    │
    ▼
┌──────────────────┐
│ AOP Weaving      │  compiler_core/aop.spl — HIR join-point detection
│ [STUBBED]        │  ⚠ Currently no-op — see TODO below
└──────────────────┘
    │
    ▼
┌──────────────────┐
│ MIR Lowering     │  compiler/mir/ — HIR → flat basic blocks
│                  │  → MIR (50+ instructions, effect tags)
└──────────────────┘
    │
    ▼
┌──────────────────┐
│ MIR Optimization │  compiler/mir_opt/ — copy propagation, etc.
└──────────────────┘
    │
    ▼
┌───────────────────────────────────────────────────┐
│                  Backend Selection                  │
│                                                     │
│  Debug ──→ Cranelift  (fast compile)               │
│  Release → LLVM       (optimized)                  │
│                                                     │
│  Also: Native (x86/ARM/RISC-V), WASM, CUDA,       │
│        Vulkan/SPIR-V, VHDL, Lean                   │
└───────────────────────────────────────────────────┘
    │
    ▼
┌──────────────────┐
│ Linker           │  compiler/linker/ — SMF binary format
│                  │  Backends: mold (Linux), MSVC (Windows)
└──────────────────┘
    │
    ▼
┌──────────────────┐
│ Loader           │  compiler/loader/ — mmap-based SMF loading
└──────────────────┘
    │
    ▼
  Execution
```

### Two Frontends Compared

| | Core Frontend | Full Frontend |
|---|---|---|
| **File** | `compiler_core/frontend.spl` | `compiler/frontend.spl` |
| **Used by** | Core interpreter (default runtime) | `bin/simple build`, CompilerDriver |
| **Preprocessor** | No | Yes (`@when`/`@cfg`) |
| **TreeSitter** | No | Yes (outline + block capture) |
| **Block resolution** | No | Yes (DSL blocks: m{}, sh{}, sql{}) |
| **Seed-compilable** | Yes | No |

### Deprecated: Interpreter-as-Backend

`compiler/backend/interpreter.spl` wraps a HIR-level tree-walker as a `BackendPort`. File header marks it **DEPRECATED** — use `compiler_core.interpreter` instead. Only used in compiler driver tests.

### TODO: Wire AOP weaving at HIR level

**Current state:** AOP is stubbed — `AopWeaver.weave()` is a no-op, call in `pipeline_fn.spl` is commented out. `detect_join_points()` operates on `MirBlockInfo`.

**Planned change:** Move AOP weaving to HIR level (after HIR lowering, before MIR lowering).

**Why:** HIR is the last common representation before backends diverge. Weaving at HIR means:
- All compiled backends get AOP automatically
- Core interpreter's JIT hot-path (AST→HIR→MIR→native) would get AOP if wired through the full frontend
- Structured control flow makes join-point matching more natural than flat MIR blocks

**Work needed:**
- Rewrite `detect_join_points()` to work on HIR nodes instead of `MirBlockInfo`
- Wire `AopWeaver.weave()` into full pipeline after HIR lowering
- Update `pipeline_fn.spl` order to: `monomorphize → HIR → AOP weave → MIR → optimize → codegen`
- Remove MIR-level weaving stubs

## Full Pipeline — MDSOC Feature Stages

Each stage is a `feature/` module with typed port contracts. Stage boundaries enforced by `transform/feature/` entity-view adapters.

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
    ├── compiler (HIR, MIR, Codegen) ─────────┤
    │       │                                 │
    │       ├── compiler_shared ──────────────┤  (shared between core + full)
    │       │       │                         │
    │       │       └── compiler_core ────────┤  (Lexer, Parser, AST, AOP)
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
├── std/              # Standard library
│   ├── spec.spl      # SSpec BDD framework
│   ├── text.spl, array.spl, math.spl, path.spl
│   └── platform/     # Cross-platform support
├── compiler_core/    # Core (seed-compilable, no generics, no deps)
│   ├── lexer.spl     # Stateful tokenizer (module globals)
│   ├── parser.spl    # Recursive descent + Pratt
│   ├── frontend.spl  # Shared parse entry points
│   ├── ast.spl       # AST arena (parallel arrays)
│   ├── tokens.spl    # Token kinds + keyword lookup
│   ├── types.spl     # Type representations
│   ├── aop.spl       # AOP weaving engine
│   ├── hir_types.spl, mir_types.spl, backend_types.spl
│   ├── interpreter/  # Tree-walking eval + adaptive JIT
│   ├── compiler/     # C++ codegen (bootstrap)
│   └── entity/       # Typed entities: ast/, hir/, mir/, token/, span/
├── compiler_shared/  # Shared between core + full compiler
│   ├── treesitter/   # TreeSitter integration (IDE, outline)
│   ├── blocks/       # Block definition trait, registry, modes
│   ├── aop.spl       # Shared AOP (richer features)
│   ├── hir.spl, mir.spl, mir_opt/
│   ├── backend/      # Backend API, selector, helpers
│   ├── pipeline/     # CompilerCompilationContext
│   └── type_system/  # Type checking + inference
└── compiler/         # Full self-hosting compiler
    ├── backend/      # All backends (Cranelift, LLVM, Native, WASM, CUDA, Vulkan, VHDL, Lean)
    ├── blocks/       # Custom block parsers (math, shell, data, SQL)
    ├── hir_lowering/ # AST → HIR
    ├── mir/          # HIR → MIR
    ├── mir_opt/      # MIR optimization
    ├── monomorphize/ # Generic specialization
    ├── inference/    # Type inference (unify, constraints)
    ├── linker/       # SMF format, mold/MSVC linker wrappers
    ├── loader/       # mmap-based SMF loading, JIT context
    ├── dependency/   # Module resolution, visibility
    ├── semantics/    # Binary ops, casts, coercion
    ├── feature/      # MDSOC pipeline stages (ports)
    ├── transform/    # MDSOC stage boundary adapters (entity views)
    ├── mdsoc/        # Virtual capsule types, config, layer checker
    ├── adapters/     # Hexagonal: in/ (lang server) out/ (file/mem storage)
    └── desugar/      # AST-level desugar (async/generator/spawn)
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

Custom DSL blocks use a **3-tier parsing** architecture (`compiler/blocks/`):

| Tier | Method | Purpose |
|------|--------|---------|
| 1 | `lex(payload, pre_lex, ctx)` | Fast sub-lexer (brace tracking) |
| 2 | `treesitter_outline(payload, pre_lex)` | IDE structural extraction |
| 3 | `parse_full(payload, pre_lex, ctx)` | Full block parse → AST nodes |

Builtin blocks: `m{ x^2 }` (math), `sh{...}` (shell), `sql{...}`, data blocks, loss blocks (ML).

Block registry: `register_block(name, definition)`, `is_block(name)`, `with_block(name, fn)`.

## AOP (Aspect-Oriented Programming)

MIR-level weaving at `compiler_core/aop.spl`:

- **Pointcuts**: `NamePattern` (glob), `Annotation` (`@tag`), `Module` (path), `All`
- **Advice**: `Before`, `AfterSuccess`, `AfterError`, `Around`
- **Join points**: `Execution` (fn entry), `Decision` (branch/pattern), `Condition` (comparison), `Error` (try_unwrap)
- **Pipeline**: `detect_join_points()` → `match_advice_for_join_point()` → `weave_function()`
- Config via SDN and `pc{...}` predicate islands

## Backend Details

| Backend | Mode | File(s) |
|---------|------|---------|
| **Cranelift** | Debug/JIT | `compiler.spl`, `cranelift_type_mapper.spl` |
| **LLVM** | Release | `llvm_backend.spl`, `llvm_ir_builder.spl`, `llvm_target.spl` |
| **Native** | Bootstrap | `native/isel_x86_64.spl`, `isel_aarch64.spl`, `isel_riscv{32,64}.spl`, `regalloc.spl`, `elf_writer.spl`, `macho_writer.spl` |
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

## Bootstrap Chain

```
Phase 0: C/C++ compiler (clang/gcc/MSVC)
Phase 1: src/compiler_seed/seed.cpp  →  seed binary (C++ transpiler)
Phase 2: seed transpiles compiler_core/*.spl  →  C++ code
Phase 3: C++ code + runtime.c  →  core_compiler binary
Phase 4: core_compiler compiles compiler/*.spl  →  Full Simple compiler
```

## Stdlib Variant System

### Memory Model Matrix

| Directory | GC | Mutable |
|-----------|-----|---------|
| `core/` | Yes | Yes |
| `core_immut/` | Yes | No |
| `core_nogc/` | No | Yes |
| `core_nogc_immut/` | No | No |

### Host Variants (Default: `async_nogc_mut`)
```
host/
├── async_gc_mut/
├── async_gc_immut/
├── async_nogc_mut/   # DEFAULT
├── sync_nogc_mut/
└── common/
```

## Adding New Features

1. **Lexer/Parser**: `src/compiler_core/lexer.spl`, `parser.spl`
2. **Source desugar**: `src/app/desugar/` (if new syntax sugar)
3. **Block parsers**: `src/compiler/blocks/` (if new DSL block)
4. **Type system**: `src/compiler_core/types.spl`, `src/compiler/inference/`
5. **HIR lowering**: `src/compiler/hir_lowering/`
6. **AOP rules**: `src/compiler_core/aop.spl` (if new join-point kind)
7. **MIR lowering**: `src/compiler/mir/`, `src/compiler_core/mir.spl`
8. **Backend**: `src/compiler/backend/` (if new instruction)
9. **Standard library**: `src/std/`
10. **Tests**: `test/`

## Architecture Rules

- `src/compiler_core/` has no dependencies on other Simple modules
- `src/compiler_shared/` depends only on `compiler_core`
- `src/std/` depends only on `src/compiler_core/`
- `src/compiler/` depends on `compiler_core`, `compiler_shared`, `std`
- `src/lib/` depends on `src/std/` and `src/compiler_core/`
- `src/app/cli/` is the only CLI entry point
- No circular dependencies between modules
- MDSOC `arch {}` blocks enforce stage isolation in `feature/__init__.spl`

### Module Dependency Rules

| Layer | May Access | May Not Access |
|-------|------------|----------------|
| `src/app/cli/` | all | - |
| `src/compiler/` | compiler_core, compiler_shared, std | app |
| `src/compiler_shared/` | compiler_core | compiler, app |
| `src/compiler_core/` | (no deps) | compiler, compiler_shared, app |
| `src/std/` | compiler_core | compiler, app |
| `src/lib/` | std, compiler_core | compiler |

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

1. Update `src/compiler_core/types.spl`
2. Update Lean theorems in `verification/type_inference_compile/`
3. Run `lake build` in verification project
4. Run `simple gen-lean compare` to verify alignment

---

## Design Checklist

### Before Implementing

- [ ] Read relevant feature spec (`doc/feature/`)
- [ ] Identify affected pipeline stages (feature/ + transform/)
- [ ] Draw dependency impact diagram

### After Implementing

- [ ] Run `bin/simple test` - all tests pass
- [ ] Run `simple gen-lean compare` - if verification affected
- [ ] Update Lean proofs if needed (`lake build`)

## See Also

- **`doc/guide/architecture_writing.md`** - Architecture writing guide
- `doc/architecture/README.md` - Full architecture docs
- `doc/architecture/file_class_structure.md` - Codebase inventory (2,649 files, 623K lines)
- `doc/codegen_technical.md` - Codegen details
- `doc/codegen/status.md` - MIR coverage
- `doc/formal_verification.md` - Lean verification docs
- `CLAUDE.md` - Project structure
