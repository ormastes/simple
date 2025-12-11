# Architecture Overview

## Project Structure

```
simple/
├── CLAUDE.md                # Development guide
├── Cargo.toml               # Workspace definition (12 crates)
├── Makefile                 # Build automation
│
├── doc/                     # Documentation
│   ├── architecture.md      # This file
│   ├── feature.md           # Feature list with ratings
│   ├── formal_verification.md # Lean 4 proofs documentation
│   ├── test.md              # Test policy
│   ├── spec/                # Language specifications
│   │   ├── language.md
│   │   └── lexer_parser.md
│   ├── design/              # Design documents
│   ├── status/              # Feature status tracking
│   ├── plans/               # Implementation plans
│   └── research/            # Research notes
│
├── verification/            # Lean 4 formal verification
│   ├── manual_pointer_borrow/   # Borrow checker proofs
│   ├── gc_manual_borrow/        # GC safety proofs
│   ├── async_compile/           # Async safety proofs (non-blocking verification)
│   ├── nogc_compile/            # NoGC instruction proofs
│   └── type_inference_compile/  # Type inference proofs
│
├── src/                     # Source code (12 crates - see below)
└── tests/                   # Integration tests
```

## Execution Modes

Simple supports two execution modes with different type requirements:

| Mode | Type Annotations | Execution | Use Case |
|------|-----------------|-----------|----------|
| **Compiler** | Required (like Rust) | Native codegen via Cranelift | Production, performance |
| **Interpreter** | Optional | Tree-walking interpreter | Prototyping, scripting |

**Key principle**: Code with explicit types runs in BOTH modes. Code without types runs ONLY in interpreter mode.

```
┌─────────────────────────────────────────────────────┐
│                  Source Code                        │
├─────────────────────────────────────────────────────┤
│  With types:     fn add(a: i64, b: i64) -> i64:    │  ──► Both modes
│  Without types:  fn add(a, b):                      │  ──► Interpreter only
└─────────────────────────────────────────────────────┘
```

The `driver` module provides `RunningType` enum:
- `Interpreter` - Run via tree-walking interpreter (supports untyped code)
- `Compiler` - Compile to native via HIR→MIR→Cranelift (requires types)
- `Both` - Run both paths and verify parity (for testing)

---

## Goals (grounded in feature list & language spec)
- Feature work should stay locally scoped: each feature touches parser → compiler → runtime via narrow contracts in `src/common/`.
- Minimize dependency fan-out: no "reach across" into unrelated modules to add a feature from `doc/feature.md`.
- Standardise interfaces (GC, ABI, loader) in `src/common/` so new features don't create ad-hoc couplings.
- Provide clear contracts for runtime/GC so memory management stays behind a stable boundary while implementing GC-managed default from the spec/feature list.
- Keep watch/build/run predictable and isolated to driver+compiler+loader; adding a language feature should not require touching them.
- Logging should be structured, low-overhead, and opt-in: prefer `tracing` spans/fields over ad-hoc prints. Use `#[tracing::instrument]` on hot paths when diagnostics are needed; avoid pervasive logging in perf-sensitive code paths by default.
- **Prevent Duplication**: Each concern belongs to exactly ONE module. If logic is needed in multiple places, define a shared abstraction in `common/` or create helper modules.
- **Formal Verification**: Key invariants (borrow safety, GC safety, effects) are modeled in Lean 4 and implemented exactly in Rust.
- **Type Requirements**: Compiler mode requires explicit type annotations on function parameters (like Rust). Interpreter mode supports dynamic typing.

---

## Module Dependency Diagram

```
                    ┌─────────────┐
                    │   common    │  ← Zero dependencies, defines all contracts
                    └─────┬───────┘
                          │
        ┌─────────────────┼─────────────────────────┐
        │                 │                         │
        ▼                 ▼                         ▼
  ┌──────────┐      ┌──────────┐             ┌──────────┐
  │  parser  │      │  loader  │             │  runtime │
  └────┬─────┘      └──────────┘             └──────────┘
       │                                           │
       ▼                                           │
  ┌──────────┐                                     │
  │   type   │                                     │
  └────┬─────┘                                     │
       │                                           │
       ▼                                           │
  ┌──────────────────────────────┐                 │
  │          compiler            │                 │
  │  (depends: parser, type,     │                 │
  │   loader/smf, common)        │                 │
  │  NOTE: does NOT depend on    │                 │
  │  runtime - uses trait only   │                 │
  └───────────────┬──────────────┘                 │
                  │                                │
       ┌──────────┼──────────────┬─────────────────┘
       │          │              │
       ▼          ▼              ▼
  ┌────────┐  ┌────────────┐  ┌──────────────┐
  │ loader │  │native_loader│ │   runtime    │
  └────────┘  └────────────┘  └──────────────┘
       │          │              │
       └──────────┴──────┬───────┘
                         │
                         ▼
                   ┌──────────┐
                   │   pkg    │  ← Package manager (UV-style)
                   └────┬─────┘
                        │
                        ▼
                   ┌──────────┐
                   │  driver  │  ← Orchestrates everything
                   │  (also   │
                   │  lib/log)│
                   └──────────┘
```

**Key Dependency Notes:**
- `parser` has NO internal dependencies (pure syntax)
- `type` depends only on `parser`
- `loader` depends only on `common`
- `runtime` depends only on `common`
- `compiler` depends on parser, type, loader/smf, common (NOT runtime - uses ActorSpawner trait)
- `pkg` (package manager) depends on common, may use loader for imports
- `driver` depends on ALL modules and orchestrates execution

---

## Project Layout (detailed)

```
src/
├── common/              # Shared contracts (ZERO dependencies)
│   ├── lib.rs           # DynModule, DynLoader, ModuleCache, ModuleRegistry
│   ├── gc.rs            # GcAllocator trait, GcHandle marker
│   ├── config_env.rs    # ConfigEnv - unified config/env/args interface
│   ├── actor.rs         # ActorHandle, ActorSpawner, Message, ThreadSpawner
│   └── manual.rs        # Manual memory: Unique, Shared, Weak, Handle, HandlePool
│
├── parser/              # Pure syntax (depends: common only for ConfigEnv)
│   ├── lib.rs           # Re-exports
│   ├── token.rs         # Token enum and TokenKind
│   ├── lexer.rs         # Tokenization with INDENT/DEDENT
│   ├── ast.rs           # AST node definitions
│   ├── parser.rs        # Main parser entry point
│   ├── error.rs         # Parse error types (ParseError enum)
│   ├── expressions/     # Expression parsing (split for maintainability)
│   │   └── mod.rs       # Pratt parser with binary operator macros
│   ├── statements/      # Statement parsing
│   │   └── mod.rs       # Variable decls, control flow, jump statements
│   └── types_def/       # Type parsing
│       └── mod.rs       # Type syntax parsing
│
├── type/                # Type checking/inference
│   └── lib.rs           # TypeChecker, Substitution, Type enum, unify()
│                        # LeanTy/LeanExpr for formal verification
│
├── compiler/            # Compilation pipeline
│   ├── lib.rs           # Re-exports CompilerPipeline, Value, CompileError
│   ├── error.rs         # CompileError enum
│   ├── pipeline.rs      # CompilerPipeline - orchestrates compilation
│   ├── project.rs       # ProjectContext - project detection, simple.toml parsing
│   ├── module_resolver.rs # ModuleResolver - path→file resolution, __init__.spl
│   ├── value.rs         # Value enum, Env, pointer wrappers
│   ├── value_tests.rs   # Comprehensive value operation tests
│   ├── effects.rs       # Effect checking (async safety, blocking detection)
│   ├── interpreter.rs   # Tree-walking interpreter entry (includes 8 modules)
│   ├── interpreter_call.rs    # Function call handling
│   ├── interpreter_control.rs # Control flow handling (if/match/loop/break/return)
│   ├── interpreter_helpers.rs # Common patterns extracted from expression eval
│   ├── interpreter_method.rs  # Method dispatch handling
│   ├── interpreter_macro.rs   # Macro expansion handling
│   ├── interpreter_extern.rs  # External function handling
│   ├── interpreter_context.rs # Context statement handling
│   ├── interpreter_ffi.rs     # FFI bridge for compiled code (thread-local state)
│   ├── value_bridge.rs        # FFI value marshalling (BridgeValue)
│   ├── compilability.rs       # Compilability analysis (20+ fallback reasons)
│   ├── hir/             # High-level IR
│   │   ├── mod.rs
│   │   ├── types.rs     # HIR type representations
│   │   └── lower.rs     # AST → HIR lowering
│   ├── mir/             # Mid-level IR
│   │   ├── mod.rs       # Re-exports
│   │   ├── types.rs     # MIR types, effects, patterns
│   │   ├── instructions.rs  # 50+ MIR instruction variants
│   │   ├── blocks.rs    # Basic block management
│   │   ├── function.rs  # Function-level MIR
│   │   ├── effects.rs   # Effect tracking and analysis
│   │   ├── generator.rs # Generator state machine lowering
│   │   └── lower.rs     # HIR → MIR lowering
│   ├── codegen/         # Code generation
│   │   ├── mod.rs
│   │   ├── cranelift.rs # AOT Cranelift backend
│   │   ├── jit.rs       # JIT Cranelift backend
│   │   ├── runtime_ffi.rs   # Shared FFI function specs (50+ functions)
│   │   └── types_util.rs    # Type conversion utilities (TypeId → Cranelift)
│   └── linker/          # SMF emission
│       ├── mod.rs
│       └── smf_writer.rs
│
├── loader/              # SMF binary loading
│   ├── lib.rs           # Re-exports ModuleLoader, LoadedModule, ModuleRegistry
│   ├── loader.rs        # ModuleLoader (DynLoader impl)
│   ├── module.rs        # LoadedModule (DynModule impl)
│   ├── registry.rs      # ModuleRegistry with symbol resolution
│   ├── smf/             # SMF format definitions
│   │   ├── mod.rs       # Re-exports, SMF_MAGIC constant
│   │   ├── header.rs    # SmfHeader, Platform, Arch
│   │   ├── section.rs   # SmfSection, SectionType
│   │   ├── symbol.rs    # SmfSymbol, SymbolType, SymbolBinding, SymbolTable
│   │   └── reloc.rs     # SmfRelocation, RelocationType
│   └── memory/          # Memory mapping
│       ├── mod.rs       # PlatformAllocator, Protection, ExecutableMemory, MemoryAllocator trait
│       ├── common.rs    # Shared memory abstractions
│       ├── posix.rs     # PosixAllocator (mmap implementation)
│       └── windows.rs   # WindowsAllocator (VirtualAlloc implementation)
│
├── native_loader/       # OS dylib loading
│   ├── lib.rs           # Re-exports
│   ├── loader.rs        # ModuleLoader (DynLoader impl for .so/.dll)
│   ├── module.rs        # LoadedModule (DynModule impl)
│   └── registry.rs      # Type alias for common::ModuleRegistry
│
├── runtime/             # GC, concurrency, and runtime values
│   ├── lib.rs           # Re-exports memory::gc, NoGcAllocator, RuntimeValue types
│   ├── value/           # Runtime value system (9 modules)
│   │   ├── mod.rs       # Re-exports all value types and FFI functions
│   │   ├── core.rs      # RuntimeValue - 64-bit tagged pointer
│   │   ├── tags.rs      # Tag constants and definitions
│   │   ├── heap.rs      # HeapHeader, HeapObjectType
│   │   ├── collections.rs # RuntimeArray, RuntimeTuple, RuntimeDict, RuntimeString + FFI
│   │   ├── objects.rs   # RuntimeObject, RuntimeClosure, RuntimeEnum + FFI
│   │   ├── ffi.rs       # Value conversion and core FFI operations
│   │   ├── actors.rs    # RuntimeActor + FFI (spawn/send/recv)
│   │   └── async_gen.rs # RuntimeFuture, RuntimeGenerator + FFI (state machine)
│   ├── memory/
│   │   ├── mod.rs
│   │   ├── gc.rs        # GcRuntime (Abfall wrapper, logging)
│   │   └── no_gc.rs     # NoGcAllocator (GC-off profile)
│   └── concurrency/
│       └── mod.rs       # Scheduler, ScheduledSpawner, spawn_actor, send_to, join_actor
│
├── pkg/                 # Package manager (UV-style)
│   ├── lib.rs           # Package manager entry
│   ├── manifest.rs      # simple.toml manifest parsing
│   ├── lock.rs          # simple.lock lock file format
│   ├── cache.rs         # Global cache with hard links
│   ├── version.rs       # Version and VersionReq types
│   ├── error.rs         # PkgError, PkgResult types
│   ├── linker.rs        # Dependency linking
│   ├── resolver/        # Dependency resolution
│   │   ├── mod.rs
│   │   └── graph.rs     # Topological ordering
│   └── commands/        # CLI subcommands
│       ├── mod.rs
│       ├── init.rs      # simple init
│       ├── install.rs   # simple install
│       ├── add.rs       # simple add <pkg>
│       ├── update.rs    # simple update
│       ├── list.rs      # simple list
│       └── cache_cmd.rs # simple cache
│
├── driver/              # CLI and orchestration
│   ├── lib.rs           # Re-exports Runner, Interpreter, watch, run_code
│   ├── main.rs          # CLI entry point
│   ├── runner.rs        # Runner - compile & run files
│   ├── exec_core.rs     # ExecCore - shared compile/load/run logic
│   ├── interpreter.rs   # Interpreter, RunResult, RunConfig, run_code()
│   ├── dependency_cache.rs # DepInfo, BuildCache - import/macro tracking
│   └── watcher/
│       └── mod.rs       # File watching for hot reload
│
├── lib/                 # Native stdlib
│   └── src/
│       ├── lib.rs       # Re-exports io module
│       └── io/
│           ├── mod.rs   # I/O module entry
│           └── term/
│               └── mod.rs  # Terminal I/O bindings
│
└── util/
    └── simple_mock_helper/  # Test utilities
        └── src/
            ├── lib.rs           # Re-exports all public items
            ├── api_scanner.rs   # ScannedApi, ScannedType, scan_directory, generate_yaml
            ├── coverage.rs      # ClassCoverage, MethodCoverage, CoverageSummary, PublicApiSpec
            ├── mock_policy.rs   # MockCheckResult, init_mocks_for_*, check_mock_use_from
            ├── test_check.rs    # TestLevel, TestCheckResult, validate_test_config
            └── bin/
                └── smh_coverage.rs  # Coverage CLI tool
```

---

## File-Based Type/Struct/Enum Listing

### common/src/

**`lib.rs`** - Core module traits and caching
- `trait DynModule` - Runtime module interface (`get_fn`, `entry_fn`)
- `trait DynLoader` - Module loader interface (`load`, `load_with_resolver`)
- `struct ModuleCache<M,E>` - Generic thread-safe caching (`get`, `insert`, `remove`, `modules`)
- `struct ModuleRegistry<L>` - Loader + cache combination (`load`, `unload`, `reload`)

**`gc.rs`** - GC contract
- `trait GcAllocator` - Memory allocation contract (`alloc_bytes`, `collect`)
- `trait GcHandle` - Marker trait for GC-managed references

**`config_env.rs`** - Configuration
- `struct ConfigEnv` - Dict-like config/env/args access

**`actor.rs`** - Actor system
- `enum Message` - Actor message types (`Value(String)`, `Bytes(Vec<u8>)`)
- `enum ActorLifecycle` - Actor state machine (`Running`, `Joined`)
- `struct ActorHandle` - Communication handle (`id`, `send`, `recv`, `join`, `is_running`)
- `trait ActorSpawner` - Spawning interface (`spawn`)
- `struct ThreadSpawner` - Thread-based spawner implementation

**`manual.rs`** - Manual memory management (matches Lean formal verification)
- `struct Nat` - Natural number newtype (matches Lean's Nat, saturating pred)
- `struct BorrowState` - Borrow tracking (`exclusive: bool`, `shared: Nat`)
- `enum ValidBorrowState` - Type-safe borrow states (`Unborrowed`, `Exclusive`, `Shared(NonZeroUsize)`)
- `struct BorrowTracker` - Thread-safe runtime borrow checker
- `struct ValidBorrowTracker` - Type-safe borrow tracker
- `struct GcState` - GC state tracking (HashSet-based, `allocate`, `borrow`, `release`, `collect_safe`)
- `struct GcStateVerify` - Vec-based GC state for Lean correspondence
- `struct GcStateTracker` - Thread-safe GC tracker
- `struct ManualGc` - Manual memory arena (`alloc`, `alloc_shared`, `alloc_handle`, `live`, `collect`)
- `struct Unique<T>` - Unique ownership pointer (`new`, `is_valid`, `into_inner`)
- `struct Shared<T>` - Reference-counted pointer (`new`, `downgrade`)
- `struct WeakPtr<T>` - Weak reference (`upgrade`)
- `struct HandlePool<T>` - Handle allocation pool (`alloc`, `resolve`, `release`)
- `struct Handle<T>` - Pool-managed handle (`resolve`)
- Pure functions: `borrow_state_valid`, `gc_state_safe`, `take_exclusive`, `take_shared`, `release_exclusive`, `release_shared`, `gc_allocate`, `gc_borrow`, `gc_release`, `gc_collect_safe`

---

### parser/src/

**`lexer.rs`** - Tokenization
- `struct Lexer<'a>` - Source → Token stream

**`token.rs`** - Token types
- `struct Span` - Source location range
- `enum FStringToken` - F-string parts
- `enum TokenKind` - Token type enum
  - **Module system tokens**: `Mod`, `Use`, `Export`, `Common`, `Auto`, `Crate`
- `struct Token` - Token with position

**`parser.rs`** - Main parser entry point
- `struct Parser<'a>` - Token stream → AST
- Delegates to submodules for parsing

**`error.rs`** - Errors
- `enum ParseError` - Parse error types

**`expressions/mod.rs`** - Expression parsing (private module)
- Pratt parser with binary operator macros (`parse_binary_single!`, `parse_binary_multi!`)
- `parse_expression()`, `parse_expression_or_assignment()`
- Expression precedence climbing implementation

**`statements/mod.rs`** - Statement parsing (private module)
- Variable declarations: `parse_let()`, `parse_mut_let()`, `parse_const()`, `parse_static()`
- Control flow: `parse_if()`, `parse_for()`, `parse_while()`, `parse_loop()`, `parse_match()`
- Jump statements: `parse_return()`, `parse_break()`, `parse_continue()`
- Module system: `parse_use()`, `parse_mod()`, `parse_common_use()`, `parse_export_use()`, `parse_auto_import()`, `parse_module_path()`, `parse_import_target()`
- Special: `parse_context()`, `parse_with()`

**`types_def/mod.rs`** - Type parsing (private module)
- `parse_type()` and related type syntax

**`ast.rs`** - AST nodes
- `enum Visibility` - Pub/private
- `enum Mutability` - Mut/immut
- `enum RangeBound` - Range bounds
- `enum SelfMode` - Self parameter modes
- `enum Node` - Top-level AST node
- **Module system**: `struct ModulePath`, `enum ImportTarget`, `struct ModDecl`, `struct UseStmt`, `struct CommonUseStmt`, `struct ExportUseStmt`, `struct AutoImportStmt`
- `struct FunctionDef`, `Parameter`, `Block`
- `struct StructDef`, `ClassDef`, `Field`
- `struct EnumDef`, `EnumVariant`
- `struct TraitDef`, `ImplBlock`, `ActorDef`
- `struct TypeAliasDef`, `ExternDef`
- `struct MacroDef`, `MacroPattern`, `MacroInvocation`
- `enum MacroParam`, `MacroBody`, `MacroToken`, `MacroArg`
- `struct LetStmt`, `ConstStmt`, `StaticStmt`
- `struct AssignmentStmt`, `enum AssignOp`
- `struct ReturnStmt`, `IfStmt`, `MatchStmt`, `MatchArm`
- `struct ForStmt`, `WhileStmt`, `LoopStmt`
- `struct BreakStmt`, `ContinueStmt`, `ContextStmt`
- `enum Type`, `PointerKind`, `Effect`
- `enum Expr`, `struct Argument`, `enum FStringPart`
- `struct LambdaParam`
- `enum BinOp`, `UnaryOp` ⚠️ *Also in hir/types.rs*
- `enum Pattern`
- `struct Module`

---

### type/src/

**`lib.rs`** - Type system
- `enum LeanTy` - Types for formal verification
- `enum LeanExpr` - Exprs for formal verification
- `enum SimpleTy` - Extended simple types
- `enum SimpleExpr` - Extended simple exprs
- `enum Type` - Full type representation
- `struct Substitution` - Type variable mapping
- `enum TypeError` - Type errors
- `struct TypeChecker` - Inference engine

---

### compiler/src/

**`error.rs`** - Errors
- `enum CompileError` - Compilation errors

**`pipeline.rs`** - Pipeline
- `struct CompilerPipeline` - Orchestration
- `with_project()`, `with_gc_and_project()` - Constructor with project context
- `compile_with_project_detection()` - Auto-detect project from file path

**`project.rs`** - Project detection and configuration
- `struct ProjectContext` - Project-level configuration holder
  - `root`, `source_root`, `name`, `resolver`, `features`, `profiles`
- `fn new(root)` - Create from project root directory
- `fn detect(file_path)` - Auto-detect project by searching for `simple.toml`
- `fn single_file(path)` - Create context for single-file mode
- `fn parse_manifest(content)` - Parse `simple.toml` content

**`module_resolver.rs`** - Module path resolution
- `struct ModuleResolver` - Resolves module paths to filesystem paths
  - `project_root`, `source_root`, `manifests`, `features`, `profiles`
- `fn resolve(path, from_file)` - Resolve module path to `ResolvedModule`
- `fn load_manifest(dir_path)` - Load and parse `__init__.spl` directory manifest
- `struct DirectoryManifest` - Parsed `__init__.spl` contents
  - `name`, `attributes`, `child_modules`, `common_uses`, `exports`, `auto_imports`
- `struct ChildModule` - Child module declaration (name, visibility, attributes)
- `struct ResolvedModule` - Resolution result (path, module_path, is_directory, manifest)

**`value.rs`** - Runtime values
- `type Env` - Variable environment
- `struct ClassName`, `EnumTypeName`, `VariantName` - Newtypes
- `enum Value` - Runtime value representation
- `struct FutureValue` - Async result
- `enum GeneratorState` - Generator lifecycle
- `struct GeneratorValue` - Coroutine state
- `struct ManualUniqueValue` - Unique wrapper
- `struct ManualSharedValue` - Shared wrapper
- `struct ManualWeakValue` - Weak wrapper
- `struct ManualHandleValue` - Handle wrapper
- `struct BorrowValue`, `BorrowMutValue` - Borrow wrappers

**`interpreter.rs`** - Interpreter entry (1364 lines)
- `enum Control` - Control flow states
- Thread-local state: ACTOR_SPAWNER, ACTOR_INBOX/OUTBOX, CONST_NAMES, etc.
- Type definitions: Enums, ImplMethods, ExternFunctions, Macros, Units
- Includes 8 modules via `include!`

**`interpreter_call.rs`** - Function call handling (532 lines)
- Call expression evaluation
- Argument evaluation and function dispatch

**`interpreter_control.rs`** - Control flow handling (522 lines)
- Block execution, if/match/loop statement execution
- Break/continue/return handling

**`interpreter_helpers.rs`** - Helper functions (559 lines)
- Common patterns extracted from expression evaluation
- Reduces duplication across interpreter modules

**`interpreter_method.rs`** - Method dispatch (357 lines)
- Built-in method handling for arrays, dicts, strings, etc.
- Method call resolution

**`interpreter_macro.rs`** - Macro expansion (315 lines)
- Macro pattern matching
- User-defined macro expansion

**`interpreter_extern.rs`** - External function handling (110 lines)
- FFI function calls

**`interpreter_context.rs`** - Context statement handling (51 lines)
- DSL support via context blocks

**`hir/types.rs`** - HIR types
- `enum Signedness` - Signed/unsigned
- `struct TypeId` - Type identifier
- `enum HirType` - HIR type representation
- `enum PointerKind` ⚠️ *Also in ast.rs*
- `struct TypeIdAllocator`, `TypeRegistry`
- `struct HirExpr`, `enum HirExprKind`
- `enum BinOp`, `UnaryOp` ⚠️ *Also in ast.rs*
- `enum HirStmt`
- `struct LocalVar`, `HirFunction`, `HirModule`

**`hir/lower.rs`** - AST→HIR
- `enum LowerError`
- `type LowerResult<T>`
- `struct Lowerer`

**`mir/types.rs`** - MIR types
- `enum LocalKind`
- `enum AsyncEffect` - Async safety effects (Compute, Io, Wait) - matches Lean `async_compile` model
- `fn is_async(e)` - Check if effect is non-blocking (Lean: `is_async`)
- `fn pipeline_safe(es)` - Check if all effects are async-safe (Lean: `pipelineSafe`)
- `enum NogcInstr` - NoGC instructions (Const, Add, GcAlloc) - matches Lean model
- `fn nogc(p)` - Check if no GC allocations
- `enum Effect` - Combined effects for production use ⚠️ *Also in ast.rs (different purpose)*
- `struct EffectSet` - Set of effects with `is_pipeline_safe()` for async safety
- `trait HasEffects` - Trait for types that report their effects
- `enum BuiltinFunc`, `CallTarget` - Known functions with effect annotations
- **Closure support**: `struct CapturedVar`, `enum CaptureMode` (ByValue, ByRef, ByMutRef)
- **Pattern matching**: `enum MirPattern`, `enum MirLiteral`, `struct PatternBinding`, `enum BindingStep`
- **F-strings**: `enum FStringPart` (Literal, Expr)

**`mir/instructions.rs`** - MIR instruction definitions
- `struct BlockId`, `VReg`
- `enum MirInst` - 50+ instruction variants (see MIR Instruction Summary below)
- `enum Terminator` - Block terminators (Return, Jump, Branch, Unreachable)

**`mir/blocks.rs`** - Basic block management
- `enum BlockBuildState`, `BlockBuildError`
- `struct BlockBuilder`, `MirBlock`

**`mir/function.rs`** - Function-level MIR
- `struct MirLocal`, `MirFunction`, `MirModule`

**`mir/effects.rs`** - Effect tracking and analysis
- Effect analysis utilities
- `CallTarget` effect annotations

**`mir/generator.rs`** - Generator state machine lowering
- `struct GeneratorState` - Per-yield state metadata
- `struct GeneratorLowering` - Lowering result
- `fn lower_generator(func, body_block)` - Rewrite generator bodies into state-machine-friendly shape

**`mir/lower.rs`** - HIR→MIR
- `struct LoopContext`
- `enum LowererState`, `BlockState`
- `enum MirLowerError`
- `type MirLowerResult<T>`
- `struct MirLowerer`

**`codegen/cranelift.rs`** - AOT code generation
- `enum CodegenError`
- `type CodegenResult<T>`
- `struct Codegen`
- Supports 50+ MIR instructions with trap fallbacks for unimplemented ops

**`codegen/jit.rs`** - JIT code generation
- JIT variant of Codegen for interactive execution
- Same instruction set as cranelift.rs
- Memory-based module loading

**`codegen/runtime_ffi.rs`** - Shared FFI function specifications
- `struct RuntimeFuncSpec` - FFI function specification (name, params, returns)
- `static RUNTIME_FUNCS: &[RuntimeFuncSpec]` - 50+ runtime function specs
- Defines all runtime function signatures (arrays, tuples, dicts, strings, values, objects, actors, generators, futures)
- Supports both AOT and JIT backends through shared spec

**`codegen/types_util.rs`** - Type conversion utilities
- `fn type_id_to_cranelift(type_id: TypeId) -> types::Type` - Map Simple types to Cranelift
- `fn type_id_size(type_id: TypeId) -> u32` - Get type size in bytes
- `fn type_to_cranelift(ty: TypeId) -> types::Type` - Alternative mapping
- Zero-cost codegen without RuntimeValue boxing

**`value_bridge.rs`** - FFI value marshalling
- `struct BridgeValue` - FFI-safe value representation (64-bit tagged)
- 23 tag constants for all value types
- Conversions: `Value ↔ BridgeValue ↔ RuntimeValue`

**`interpreter_ffi.rs`** - FFI bridge for compiled code (511 lines)
- Thread-local interpreter state (environment, functions, classes)
- `struct CompiledFnSignature` and `struct CompiledFn`
- Registry: `register_compiled_fn()`, `unregister_compiled_fn()`
- Entry points: `interp_eval_ffi()`, `interp_call_ffi()`
- `simple_interp_init(module)` - Initialize interpreter context
- `simple_interp_call(func_name, argc, argv)` - Call interpreter function
- `simple_interp_eval_expr(expr_index)` - Evaluate expression via interpreter

**`compilability.rs`** - Compilability analysis
- `enum FallbackReason` - 20+ reasons for interpreter fallback
- `enum CompilabilityStatus` - Compilable vs RequiresInterpreter
- `analyze_module()`, `analyze_function()` - Determine what can be compiled

**`linker/smf_writer.rs`** - SMF writing
- `enum DataSectionKind` - Mutable/readonly
- `enum SmfWriteError`
- `type SmfWriteResult<T>`
- `struct SmfSymbol` - Local writing struct
- `struct SmfRelocation` - Local writing struct
- `struct SmfSection` - Local writing struct
- `struct SmfWriter`
- Re-exports from `loader/smf/`: `SectionType`, `SymbolBinding`, `SymbolType`, `RelocationType`

---

### loader/src/

**`loader.rs`** - SMF loading
- `struct ModuleLoader`
  - `load(path)` - Load SMF from file
  - `load_with_resolver(path, F)` - Load with custom symbol resolver
  - `load_from_memory(bytes)` - Load SMF from memory buffer (TODO)
  - `load_from_memory_with_resolver(bytes, F)` - Load from memory with resolver (TODO)
- `enum LoadError`

**`module.rs`** - Loaded module
- `struct LoadedModule`

**`registry.rs`** - Module registry
- `type ModuleRegistryBase`
- `struct ModuleRegistry`

**`smf/header.rs`** - SMF header (CANONICAL)
- `struct SmfHeader`
- `enum Platform`, `Arch`

**`smf/section.rs`** - Sections (CANONICAL)
- `struct SmfSection`
- `enum SectionType`

**`smf/symbol.rs`** - Symbols (CANONICAL)
- `struct SmfSymbol`
- `enum SymbolType`, `SymbolBinding`
- `struct SymbolTable`

**`smf/reloc.rs`** - Relocations (CANONICAL)
- `struct SmfRelocation`
- `enum RelocationType`

**`memory/mod.rs`** - Memory abstraction
- `type PlatformAllocator`
- `enum Protection`
- `struct ExecutableMemory`
- `trait MemoryAllocator`

**`memory/posix.rs`** - POSIX impl
- `struct PosixAllocator`

**`memory/windows.rs`** - Windows impl
- `struct WindowsAllocator`

---

### native_loader/src/

**`loader.rs`** - Native loading
- `struct ModuleLoader`
- `enum LoadError`

**`module.rs`** - Loaded module
- `struct LoadedModule`

**`registry.rs`** - Registry
- `type ModuleRegistry`

---

### runtime/src/

**`lib.rs`** - Re-exports
- Re-exports `memory::gc`, `NoGcAllocator`
- Re-exports `RuntimeValue` types and 50+ FFI functions

**`value/mod.rs`** - Runtime value system (9 modules)
- Aggregates all value types and FFI functions
- Comprehensive re-export lists

**`value/core.rs`** - Core RuntimeValue
- `struct RuntimeValue(u64)` - 64-bit tagged pointer
- Methods: `is_int()`, `as_int()`, `from_int()`, etc.

**`value/tags.rs`** - Tag constants
- `TAG_INT`, `TAG_HEAP`, `TAG_FLOAT`, `TAG_SPECIAL`

**`value/heap.rs`** - Heap header management
- `struct HeapHeader` - Common header for heap objects
- `enum HeapObjectType` - String, Array, Dict, Tuple, Object, Closure, Enum, Future, Generator, Actor, Unique, Shared, Borrow

**`value/collections.rs`** - Collection types + FFI
- `struct RuntimeArray`, `RuntimeTuple`, `RuntimeDict`, `RuntimeString`
- **FFI functions**:
  - Array ops: `rt_array_new`, `rt_array_push`, `rt_array_get`, `rt_array_set`, `rt_array_pop`, `rt_array_clear`
  - Tuple ops: `rt_tuple_new`, `rt_tuple_set`, `rt_tuple_get`, `rt_tuple_len`
  - Dict ops: `rt_dict_new`, `rt_dict_set`, `rt_dict_get`, `rt_dict_len`, `rt_dict_clear`, `rt_dict_keys`, `rt_dict_values`
  - String ops: `rt_string_new`, `rt_string_concat`, `rt_string_data`, `rt_string_len`

**`value/objects.rs`** - Object/Closure/Enum types + FFI
- `struct RuntimeObject` - Class/struct instance
- `struct RuntimeClosure` - Closure with captured values
- `struct RuntimeEnum` - Enum variant with payload
- **FFI functions**:
  - Object ops: `rt_object_new`, `rt_object_field_get`, `rt_object_field_set`, `rt_object_class_id`, `rt_object_field_count`
  - Closure ops: `rt_closure_new`, `rt_closure_set_capture`, `rt_closure_get_capture`, `rt_closure_func_ptr`
  - Enum ops: `rt_enum_new`, `rt_enum_discriminant`, `rt_enum_payload`

**`value/ffi.rs`** - Value conversion and core FFI
- Memory: `rt_alloc`, `rt_free`, `rt_ptr_to_value`
- Values: `rt_value_int`, `rt_value_float`, `rt_value_bool`, `rt_value_nil`
- Extraction: `rt_value_as_int`, `rt_value_as_float`, `rt_value_as_bool`
- Checking: `rt_value_eq`, `rt_value_truthy`
- Fallback: `rt_interp_call`, `rt_interp_eval`

**`value/actors.rs`** - Actor FFI
- `struct RuntimeActor`
- **FFI functions**: `rt_actor_spawn`, `rt_actor_send`, `rt_actor_recv`
- Thread-local actor mailbox state

**`value/async_gen.rs`** - Future and Generator FFI
- `struct RuntimeFuture`, `struct RuntimeGenerator`
- **FFI functions**:
  - Future: `rt_future_new`, `rt_future_await`
  - Generator: `rt_generator_new`, `rt_generator_next`, `rt_generator_get_state`, `rt_generator_set_state`
  - Frame save/restore: `rt_generator_load_slot`, `rt_generator_store_slot`, `rt_generator_mark_done`, `rt_generator_get_ctx`

**`memory/gc.rs`** - GC runtime
- `enum GcLogEventKind`
- `struct GcLogEvent`
- `struct GcRuntime` - Abfall-backed GC wrapper with logging

**`memory/no_gc.rs`** - No-GC allocator
- `struct NoGcAllocator` - GC-off profile implementation

**`concurrency/mod.rs`** - Actor scheduler
- `struct Scheduler` (private) - Global actor registry with mailboxes and join handles
- `struct ScheduledSpawner` - Actor spawner that registers with global scheduler
- `fn spawn_actor<F>` - Spawn a new actor thread with mailbox setup
- `fn send_to(id, msg)` - Send message to actor by ID (scheduler dispatch)
- `fn join_actor(id)` - Join an actor by ID (scheduler join table)

---

### pkg/src/ (Package Manager)

**`lib.rs`** - Package manager entry
- Re-exports all public types and commands

**`manifest.rs`** - Manifest parsing
- `struct Manifest` - simple.toml representation
- `struct Dependency` - Dependency specification (path, git, version)

**`lock.rs`** - Lock file format
- `struct LockFile` - simple.lock representation
- `struct LockedDependency` - Resolved dependency with exact version

**`cache.rs`** - Global cache
- `struct Cache` - Global package cache with hard links
- Methods: `get()`, `put()`, `list()`, `clean()`

**`version.rs`** - Version handling
- `struct Version` - Semantic version
- `struct VersionReq` - Version requirement/constraint

**`error.rs`** - Error types
- `enum PkgError` - Package manager errors
- `type PkgResult<T>` - Result alias

**`linker.rs`** - Dependency linking
- `struct Linker` - Links dependencies into project

**`resolver/mod.rs`** - Dependency resolution
- `struct Resolver` - Dependency resolver

**`resolver/graph.rs`** - Dependency graph
- `struct DepGraph` - Dependency graph with topological ordering
- `fn topological_sort()` - Build order computation

**`commands/mod.rs`** - CLI command entry
- Re-exports all command handlers

**`commands/init.rs`** - Project initialization
- `fn init()` - Create new simple.toml

**`commands/install.rs`** - Dependency installation
- `fn install()` - Install all dependencies from lock file

**`commands/add.rs`** - Add dependency
- `fn add(name, version)` - Add dependency to manifest

**`commands/update.rs`** - Update dependencies
- `fn update()` - Update dependencies to latest compatible versions

**`commands/list.rs`** - List dependencies
- `fn list()` - Show dependency tree

**`commands/cache_cmd.rs`** - Cache management
- `fn cache_list()`, `fn cache_clean()` - Cache operations

---

### util/simple_mock_helper/src/

**`lib.rs`** - Re-exports all public items

**`api_scanner.rs`** - Public API scanning
- `struct ScannedApi` - Scanned API data
- `struct ScannedType` - Scanned type information
- `fn scan_directory` - Scan directory for public APIs
- `fn generate_yaml` - Generate YAML from scanned APIs
- `fn write_yaml` - Write YAML to file
- `fn merge_with_existing` - Merge with existing API spec

**`coverage.rs`** - Coverage analysis
- `struct ClassCoverage` - Class-level coverage data
- `struct MethodCoverage` - Method-level coverage data
- `struct CoverageSummary` - Overall coverage summary
- `struct PublicApiSpec` - Public API specification
- `struct LlvmCovExport` - LLVM coverage export data
- `fn compute_class_coverage` - Compute class coverage from llvm-cov
- `fn load_llvm_cov_export` - Load llvm-cov export file
- `fn load_public_api_spec` - Load public API spec from YAML
- `fn print_class_coverage_table` - Print coverage table

**`mock_policy.rs`** - Mock control for tests
- `enum MockCheckResult` - Result of mock permission check
- `const DEFAULT_HAL_PATTERNS` - Default HAL mock patterns
- `const DEFAULT_ENV_PATTERNS` - Default environment mock patterns
- `fn are_mocks_enabled` - Check if mocks are enabled
- `fn check_mock_use_from` - Check if mock use is allowed
- `fn try_check_mock_use_from` - Try to check mock permission
- `fn get_allowed_patterns` - Get allowed mock patterns
- `fn init_mocks_for_only` - Initialize mocks for specific patterns
- `fn init_mocks_for_only_default` - Initialize with default patterns
- `fn init_mocks_for_system` - Initialize for system tests (no mocks)
- `fn is_policy_initialized` - Check if policy is initialized

**`test_check.rs`** - Test level management
- `enum TestLevel` - Test level (`Unit`, `Integration`, `System`, `Environment`)
- `struct TestCheckResult` - Result of test check
- `fn get_test_level` - Get current test level
- `fn get_test_level_name` - Get test level name
- `fn try_get_test_level` - Try to get test level
- `fn init_test_level` - Initialize test level
- `fn init_test_level_named` - Initialize test level with name
- `fn assert_test_level` - Assert expected test level
- `fn assert_mocks_allowed` - Assert mocks are allowed
- `fn assert_mocks_forbidden` - Assert mocks are forbidden
- `fn validate_test_config` - Validate test configuration

---

### driver/src/

**`lib.rs`** - Re-exports
- Re-exports `Runner`, `watch`, `run_code`, `Interpreter`, `RunResult`, `RunConfig`

**`exec_core.rs`** - Low-level execution engine (shared logic)
- `struct ExecCore`
  - `loader: SmfLoader` - SMF module loader
  - `gc_alloc: Arc<dyn GcAllocator>` - GC allocator trait object
  - `gc_runtime: Option<Arc<GcRuntime>>` - Optional GC runtime for logging
  - `new()`, `new_no_gc()` - Create with/without GC
  - `compile_source(source, out)` - Compile source to SMF file
  - `compile_file(path, out)` - Compile file to SMF
  - `compile_to_memory(source)` - Compile to bytes, no disk I/O
  - `compile_to_memory_native(source)` - Compile to native code in memory
  - `load_module(path)` - Load SMF from file
  - `load_module_from_memory(bytes)` - Load SMF from memory
  - `run_smf(path)` - Run pre-compiled SMF file
  - `run_smf_from_memory(bytes)` - Run SMF from memory
  - `run_source(source)` - Compile and run (uses temp file)
  - `run_source_in_memory(source)` - Compile and run, no disk I/O
  - `run_file(path)` - Auto-detect .spl/.smf and run
  - `execute()` - Execute loaded module
  - `collect_gc()` - Trigger GC collection

**`runner.rs`** - Mid-level public API
- `struct Runner`
  - `new()`, `new_no_gc()` - Create with/without GC
  - `run_source(source)` - Compile and run source string
  - `run_source_in_memory(source)` - Compile and run without disk I/O
  - `run_file(path)` - Run .spl or .smf file (auto-detect)
  - `run_smf(path)` - Run pre-compiled SMF directly
  - `compile_to_smf(source, out)` - Compile source to SMF file
  - `gc_runtime()` - Access underlying GC runtime

**`interpreter.rs`** - High-level API with I/O capture
- `struct Interpreter`
  - `new()`, `new_no_gc()` - Create with/without GC
  - Uses `Runner` internally (delegates execution)
  - `run(code, config)` - Run with configuration
  - `run_with_stdin(code, stdin)` - Run with stdin input
  - `run_simple(code)` - Run without config
  - `run_in_memory(code)` - Run without disk I/O
  - `runner()` - Access underlying Runner
  - `gc()` - Access underlying GC runtime
- `struct RunResult` - `exit_code`, `stdout`, `stderr`
- `struct RunConfig` - `args`, `stdin`, `timeout_ms`, `in_memory`
- `fn run_code(code, args, stdin)` - Convenience function for running code

**`dependency_cache.rs`** - Import/macro dependency tracking
- `struct DepInfo` - Dependency information
- `struct BuildCache` - Build cache for incremental compilation

**`watcher/mod.rs`** - File watching
- `fn watch(path, callback)` - Watch file for changes and trigger rebuild

---

## Potential Duplications (⚠️ Review Required)

| Type Name | Location 1 | Location 2 | Resolution |
|-----------|------------|------------|------------|
| `BinOp` | `parser/ast.rs` | `compiler/hir/types.rs` | OK: AST vs HIR representation |
| `UnaryOp` | `parser/ast.rs` | `compiler/hir/types.rs` | OK: AST vs HIR representation |
| `PointerKind` | `parser/ast.rs` | `compiler/hir/types.rs` | OK: AST vs HIR representation |
| `Effect` | `parser/ast.rs` | `compiler/mir/types.rs` | OK: AST annotation vs MIR effect |
| `Type` | `parser/ast.rs` | `type/lib.rs` | OK: AST syntax vs type system |
| `ModuleLoader` | `loader/` | `native_loader/` | OK: Different loaders |
| `LoadedModule` | `loader/` | `native_loader/` | OK: Different module types |
| `LoadError` | `loader/` | `native_loader/` | OK: Different error types |
| `ModuleRegistry` | `loader/` | `native_loader/` | OK: SMF extends, native aliases |

**All duplications are intentional** - they represent the same concept at different abstraction levels (AST→HIR→MIR) or for different module types (SMF vs native).

---

## Dependency Discipline (by feature area)

### common (ZERO dependencies)
- **Only place** for cross-cutting contracts
- Everything else may depend on it
- Never import from parser/compiler/runtime/loader

### parser (ZERO internal dependencies)
- Pure syntax; no semantic analysis
- Adding new syntax: ONLY modify parser/
- No interpretation, no type checking
- External deps: only `thiserror`

### type (depends: parser)
- Type inference and checking
- No runtime values, no interpretation
- Does NOT depend on common (standalone type system)

### loader (depends: common)
- SMF binary loading
- DynLoader/DynModule implementations
- Memory mapping abstractions
- No parser/compiler/runtime dependencies

### native_loader (depends: common)
- OS dylib loading (.so/.dll)
- DynLoader/DynModule implementations
- No parser/compiler/runtime dependencies

### runtime (depends: common)
- GcAllocator implementation (Abfall wrapper)
- Actor scheduler (ScheduledSpawner)
- Runtime value FFI (50+ functions)
- No compiler/parser dependencies

### compiler (depends: parser, type, loader/smf, common)
- Interpretation lives HERE (not in driver)
- Value types live HERE (not in common)
- Uses loader/smf only for format structs
- **Does NOT depend on runtime** - uses `common::ActorSpawner` trait instead
- This allows compiler to be runtime-agnostic

### pkg (depends: common)
- UV-style package manager
- Manifest and lock file handling
- Dependency resolution with topological ordering
- Global cache with hard links
- No parser/compiler/runtime dependencies

### driver (depends: all modules)
- Uses loader, native_loader, compiler, runtime, common, lib (term-io), log, pkg
- Orchestration only; no business logic
- Wires up GcRuntime and provides it to compiler via trait

---

## Duplication Prevention Rules

### Where Logic MUST Live (Single Source of Truth)

| Concern | Canonical Location | NOT Allowed In |
|---------|-------------------|----------------|
| Token types | `parser/token.rs` | anywhere else |
| AST nodes | `parser/ast.rs` | anywhere else |
| Type inference | `type/lib.rs` | compiler/interpreter |
| Value representation | `compiler/value.rs` | common/, driver/ |
| Interpretation | `compiler/interpreter*.rs` | driver/ |
| Module caching | `common/lib.rs` | loader/, native_loader/ |
| GC trait | `common/gc.rs` | runtime/ (impl only) |
| Actor spawning | `common/actor.rs` | compiler/, driver/ |
| Manual memory | `common/manual.rs` | compiler/ (wrappers only) |
| SMF types (canonical) | `loader/smf/` | anywhere else (import only) |
| SMF writing logic | `compiler/linker/smf_writer.rs` | loader/ |
| Memory mapping | `loader/memory/` | anywhere else |

### Anti-Patterns to Avoid

❌ **Don't duplicate ModuleRegistry logic**
```rust
// BAD: Each loader implements its own cache
impl ModuleLoader {
    fn load_cached(&self, ...) { ... }  // Duplicated!
}

// GOOD: Use common::ModuleRegistry<L>
pub type Registry = common::ModuleRegistry<MyLoader>;
```

❌ **Don't put Value types in common/**
```rust
// BAD: common/ has runtime-specific types
// common/lib.rs
pub enum Value { Int(i64), ... }  // NO!

// GOOD: Value lives in compiler/value.rs
// compiler/value.rs
pub enum Value { Int(i64), ... }
```

❌ **Don't interpret in driver/**
```rust
// BAD: driver/ contains evaluation logic
// driver/runner.rs
fn evaluate(&self, expr: &Expr) -> Value { ... }  // NO!

// GOOD: driver/ calls compiler/interpreter
// driver/exec_core.rs
fn run_source(&self) -> Result<i32, String> {
    // ...
    compiler::evaluate_module(&ast)?  // Delegate to compiler
}
```

❌ **Don't duplicate helper functions across interpreter modules**
```rust
// BAD: Same pattern in multiple interpreter_*.rs files
// interpreter_method.rs
fn eval_arg_int(...) { ... }
// interpreter_call.rs
fn eval_arg_int(...) { ... }  // Duplicated!

// GOOD: Define once in interpreter.rs, use in all includes
// interpreter.rs
fn eval_arg_int(...) { ... }  // Shared helper
include!("interpreter_call.rs");
include!("interpreter_method.rs");
```

### Shared Abstraction Patterns

**Pattern 1: Generic + Type Alias**
```rust
// common/lib.rs - Generic implementation
pub struct ModuleRegistry<L: DynLoader> { ... }

// loader/registry.rs - Type alias with extensions
pub type Base = common::ModuleRegistry<ModuleLoader>;
pub struct ModuleRegistry { inner: Base }
impl ModuleRegistry {
    // SMF-specific: cross-module symbol resolution
    pub fn resolve_symbol(&self, name: &str) -> Option<usize> { ... }
}

// native_loader/registry.rs - Simple type alias
pub type ModuleRegistry = common::ModuleRegistry<ModuleLoader>;
```

**Pattern 2: Trait in common/, Impl in crate**
```rust
// common/gc.rs - Contract
pub trait GcAllocator {
    fn alloc_bytes(&self, bytes: &[u8]) -> usize;
    fn collect(&self);
}

// runtime/memory/gc.rs - Implementation
impl GcAllocator for GcRuntime { ... }

// runtime/memory/no_gc.rs - Alternative implementation
impl GcAllocator for NoGcAllocator { ... }
```

**Pattern 3: Wrappers for Type-Specific Behavior**
```rust
// common/manual.rs - Generic pointer types
pub struct Unique<T> { ... }

// compiler/value.rs - Value-specific wrappers
pub struct ManualUniqueValue {
    ptr: ManualUnique<Value>,  // Uses generic from common
}
impl ManualUniqueValue {
    // Value-specific behavior
    pub fn inner(&self) -> &Value { ... }
}
```

---

## Data Flow Diagrams

### Compilation Pipeline

```
Source Code (.spl)
       │
       ▼
┌──────────────────────────────────────────────────────────────┐
│  parser/                                                      │
│  ┌────────┐    ┌────────┐    ┌─────────┐                     │
│  │ Lexer  │ →  │ Parser │ →  │   AST   │                     │
│  └────────┘    └────────┘    └────┬────┘                     │
└───────────────────────────────────┼──────────────────────────┘
                                    │
                                    ▼
┌──────────────────────────────────────────────────────────────┐
│  type/                                                        │
│  ┌─────────────┐    ┌──────────────┐                         │
│  │ TypeChecker │ →  │ Type-checked │  (optional errors)      │
│  └─────────────┘    └──────┬───────┘                         │
└────────────────────────────┼─────────────────────────────────┘
                             │
                             ▼
┌──────────────────────────────────────────────────────────────┐
│  compiler/                                                    │
│  ┌────────────────┐    ┌───────┐    ┌─────────────────┐      │
│  │ evaluate_module│ →  │ Value │ →  │ write_smf_with_ │      │
│  │ (interpreter)  │    │ (i32) │    │ return_value()  │      │
│  └────────────────┘    └───────┘    └────────┬────────┘      │
└───────────────────────────────────────────────┼──────────────┘
                                                │
                                                ▼
                                           SMF Binary
```

### Runtime Execution

```
SMF Binary (file or memory)
     │
     ▼
┌──────────────────────────────────────────────────────────────┐
│  loader/                                                      │
│  ┌──────────────────────────────────────────────────────┐    │
│  │              ModuleLoader                             │    │
│  │  ┌─────────────────┐    ┌─────────────────────────┐  │    │
│  │  │ load(path)      │    │ load_from_memory(bytes) │  │    │
│  │  │ (from file)     │    │ (from memory) [TODO]    │  │    │
│  │  └────────┬────────┘    └───────────┬─────────────┘  │    │
│  │           └──────────┬──────────────┘                │    │
│  │                      ▼                               │    │
│  │           ┌─────────────────────┐                    │    │
│  │           │   LoadedModule      │                    │    │
│  │           └──────────┬──────────┘                    │    │
│  └──────────────────────┼───────────────────────────────┘    │
└─────────────────────────┼────────────────────────────────────┘
                          │
                          ▼
┌──────────────────────────────────────────────────────────────┐
│  driver/                                                      │
│  ┌──────────┐    ┌────────────┐                              │
│  │ ExecCore │ →  │ run_main() │ → Exit Code (i32)            │
│  └──────────┘    └────────────┘                              │
└──────────────────────────────────────────────────────────────┘
```

### Driver Component Hierarchy

```
┌─────────────────────────────────────────────────────────────────┐
│                         driver/                                  │
│                                                                  │
│  ┌─────────────────┐                                            │
│  │   Interpreter   │  High-level: I/O capture, config           │
│  │  (uses Runner)  │                                            │
│  └────────┬────────┘                                            │
│           │ delegates to                                        │
│           ▼                                                     │
│  ┌─────────────────┐                                            │
│  │     Runner      │  Mid-level: public compile/run API         │
│  │ (uses ExecCore) │                                            │
│  └────────┬────────┘                                            │
│           │ delegates to                                        │
│           ▼                                                     │
│  ┌─────────────────┐                                            │
│  │    ExecCore     │  Low-level: shared compile/load/run logic  │
│  └────────┬────────┘                                            │
│           │                                                     │
│     ┌─────┴─────┐                                               │
│     │           │                                               │
│     ▼           ▼                                               │
│  ┌──────┐  ┌────────┐                                           │
│  │Compiler│  │ Loader │                                          │
│  │Pipeline│  │        │                                          │
│  └──────┘  └────────┘                                           │
└─────────────────────────────────────────────────────────────────┘
```

### Execution Modes

**Mode 1: File-based (current)**
```
Source → compile_source() → temp.smf (disk) → load() → LoadedModule → run_main()
```

**Mode 2: In-memory (TODO)**
```
Source → compile_to_memory() → Vec<u8> → load_from_memory() → LoadedModule → run_main()
```

### Module Loading & Caching

```
                    ┌─────────────────────┐
                    │   common/lib.rs     │
                    │  ModuleRegistry<L>  │
                    │  ModuleCache<M,E>   │
                    └─────────┬───────────┘
                              │
              ┌───────────────┼───────────────┐
              │               │               │
              ▼               │               ▼
    ┌─────────────────┐       │     ┌─────────────────┐
    │ loader/         │       │     │ native_loader/  │
    │ ModuleRegistry  │       │     │ ModuleRegistry  │
    │ (extends base)  │       │     │ (type alias)    │
    │ +resolve_symbol │       │     └─────────────────┘
    └─────────────────┘       │
                              │
                              ▼
                    ┌─────────────────────┐
                    │     driver/         │
                    │     ExecCore        │
                    │  (uses both types)  │
                    └─────────────────────┘
```

---

## Hybrid Execution Architecture (Codegen + Interpreter)

The Simple compiler supports a hybrid execution model where compilable features are compiled to native code via Cranelift, while unsupported features fall back to the tree-walking interpreter.

### Architecture Overview

```
Source Code
    │
    ▼
┌─────────────────────────┐
│  Compilability Analysis │  ← Determine what can be compiled
│  (compilability.rs)     │
└───────────┬─────────────┘
            │
    ┌───────┴───────┐
    ▼               ▼
┌────────┐    ┌──────────────┐
│Compiled│    │ Interpreter  │
│  Path  │◄──►│   Fallback   │  ← Bidirectional calls
│(codegen)│   │(interpreter) │
└────────┘    └──────────────┘
    │               │
    └───────┬───────┘
            ▼
┌─────────────────────────┐
│    Runtime Bridge       │  ← Value conversion (BridgeValue)
│  (value_bridge.rs)      │
└─────────────────────────┘
```

### MIR Instruction Summary

The MIR (Mid-level IR) defines 50+ instructions organized by category:

| Category | Instructions | Effect |
|----------|-------------|--------|
| **Core** | ConstInt, ConstFloat, ConstBool, Copy, BinOp, UnaryOp | Compute |
| **Memory** | Load, Store, LocalAddr, GetElementPtr, GcAlloc, Wait | Varies |
| **Collections** | ArrayLit, TupleLit, DictLit, IndexGet, IndexSet, SliceOp, Spread | GcAlloc |
| **Strings** | ConstString, ConstSymbol, FStringFormat | GcAlloc |
| **Closures** | ClosureCreate, IndirectCall | GcAlloc |
| **Objects** | StructInit, FieldGet, FieldSet | Compute/GcAlloc |
| **Methods** | MethodCallStatic, MethodCallVirtual, BuiltinMethod | Io |
| **Patterns** | PatternTest, PatternBind, EnumDiscriminant, EnumPayload | Compute |
| **Enums** | EnumUnit, EnumWith | GcAlloc |
| **Async** | FutureCreate, Await, ActorSpawn, ActorSend, ActorRecv | Wait/Io |
| **Generators** | GeneratorCreate, Yield, GeneratorNext | Wait/Io |
| **Errors** | TryUnwrap, OptionSome, OptionNone, ResultOk, ResultErr | Wait/GcAlloc |
| **Fallback** | InterpCall, InterpEval | Io |

**Codegen coverage note (runtime FFI)**: Actors, generators, and futures are wired to runtime imports (`rt_actor_spawn/send/recv`, `rt_generator_new/yield/next`, `rt_future_new/await`) and now pass `(body_func, ctx)` to the runtime. `body_block` is still a no-op stub until outlining/capture plumbing is implemented, so compiled bodies do not run yet; the interpreter remains the source of correct behavior.

**Planned codegen upgrades (in progress)**:
- Body outlining (Plan 20): turn `body_block` into standalone `fn(ctx)` with copied captures (Rust ABI, Erlang isolation) so compiled actors/generators/futures run real bodies.
- Generator state machine (Plan 21): transform yields into a stackless state machine so compiled `yield/next` suspend/resume instead of eager collection.
- Future execution (Plan 22): execute outlined future body, store result, and make `await` return it.

### Runtime Value Representation

The `RuntimeValue` type uses a 64-bit tagged pointer layout:

```
| Payload (61 bits)                              | Tag (3 bits) |
```

**Tag values:**
- `000`: Signed integer (61-bit, sign-extended)
- `001`: Heap pointer to object
- `010`: Float (NaN-boxing)
- `011`: Special values (nil, bool, symbol ID)

### Interpreter Fallback Design

**Granularity**: Function-level (cleanest boundary)

**FFI Bridge Functions**:
```rust
#[no_mangle]
extern "C" fn simple_interp_call(
    func_name: *const c_char,
    argc: usize,
    argv: *const BridgeValue,
) -> BridgeValue;

#[no_mangle]
extern "C" fn simple_interp_init(module_ptr: *const Module);
```

**Fallback Reasons** (20+ reasons tracked in `compilability.rs`):
- Closures, lambdas, decorators
- Actors, async/await, generators
- Dynamic dispatch, method missing
- Macros, context blocks
- Complex pattern matching

### Effect Tracking

All MIR instructions maintain effect annotations for formal verification:
- **Compute**: Pure operations (literals, field access, pattern test)
- **Io**: Non-blocking I/O (ActorSend, method calls)
- **Wait**: Blocking operations (Await, ActorRecv)
- **GcAlloc**: Heap allocation (collections, closures, objects)

---

## GC / Memory Management Strategy (from spec: GC-managed default)

### Architecture
```
┌─────────────────────────────────────────────────────────────┐
│                        common/gc.rs                          │
│  ┌──────────────┐    ┌──────────┐                           │
│  │ GcAllocator  │    │ GcHandle │  ← Traits/contracts only  │
│  │   (trait)    │    │ (marker) │                           │
│  └──────┬───────┘    └──────────┘                           │
└─────────┼───────────────────────────────────────────────────┘
          │
          │ implements
          ▼
┌─────────────────────────────────────────────────────────────┐
│                     runtime/memory/                          │
│  ┌─────────────┐              ┌───────────────┐             │
│  │  GcRuntime  │              │ NoGcAllocator │             │
│  │  (Abfall)   │              │  (GC-off)     │             │
│  └─────────────┘              └───────────────┘             │
└─────────────────────────────────────────────────────────────┘
```

### Key Principles
- **Wrapper API** in `runtime/memory/gc.rs`: handles, roots, FFI-safe allocation
- **Backend**: Abfall behind GcRuntime; no other module depends on Abfall
- **Stable interfaces in `common/`**:
  - `GcAllocator` trait (alloc_bytes/collect) - compiler targets this
  - `GcHandle` marker trait - for future GC-managed references
- Compiler emits calls only to GcAllocator trait
- Runtime plugs in concrete implementation
- Loaders are GC-unaware

## Watch/Build/Run Flow (driver)
- `dependency_cache` parses imports/macros → cache (`target/simple_watch_cache.json`).
- `watcher` uses `notify` to track changes, maps to dependents via cache, triggers rebuild + run via `runner`.
- `runner` calls `CompilerPipeline` → SMF → load with `loader` → execute `main`.
- Each step only touches its immediate neighbors.

## Code Quality Tools

### Test Coverage
Uses `cargo-llvm-cov` for accurate coverage measurement.

```bash
make coverage          # Generate HTML report in target/coverage/html/
make coverage-summary  # Print summary to console
make coverage-lcov     # Generate LCOV format for CI integration
```

Install: `cargo install cargo-llvm-cov`

### Code Duplication Detection
Uses `jscpd` for detecting copy-paste code that should be refactored.

```bash
make duplication       # Generate report in target/duplication/
```

Configuration in `.jscpd.json`:
- Minimum 5 lines / 50 tokens to flag as duplicate
- Ignores test files and target/

Install: `npm install -g jscpd`

### Linting & Formatting
```bash
make lint              # Run clippy with warnings as errors
make lint-fix          # Auto-fix clippy suggestions
make fmt               # Format all code
make fmt-check         # Check formatting (CI-friendly)
```

### Combined Checks
```bash
make check             # fmt-check + lint + test
make check-full        # All checks + coverage + duplication
```

### Additional Tools
```bash
make audit             # Security vulnerability scan (cargo-audit)
make outdated          # Check for outdated dependencies
make unused-deps       # Find unused dependencies (requires nightly)
```

Install all tools: `make install-tools`

---

## Feature Implementation Guidance

### Adding a New Feature: Checklist

```
1. [ ] Is this syntax? → parser/ only
2. [ ] Is this types? → type/ only
3. [ ] Is this evaluation? → compiler/interpreter*.rs
4. [ ] Is this a new pointer/handle? → common/ trait, runtime/ impl, compiler/ wrapper
5. [ ] Is this cross-module? → common/ contract first
6. [ ] Does it need GC? → Use GcAllocator trait, NOT GcRuntime directly
```

### Feature → Module Mapping

| Feature Category | Modify | DON'T Modify |
|-----------------|--------|--------------|
| New syntax (keywords, operators) | `parser/` | compiler, runtime |
| New AST nodes | `parser/ast.rs` | anywhere else |
| Type system additions | `type/lib.rs` | compiler/interpreter |
| New Value variants | `compiler/value.rs` | common/, driver/ |
| Builtin methods | `compiler/interpreter_method.rs` | driver/ |
| Builtin functions | `compiler/interpreter_call.rs` | driver/ |
| New pointer kinds | `common/manual.rs` + `compiler/value.rs` wrapper | driver/ |
| Actor features | `common/actor.rs` contract + impl | compiler (uses only) |
| GC features | `common/gc.rs` trait + `runtime/memory/` impl | compiler (uses only) |
| IO/stdlib | `lib/` | compiler/, runtime/ |
| Hot reload | `loader/registry.rs` | compiler/, driver/ |
| Package management | `pkg/` | compiler/, runtime/ |
| Runtime FFI functions | `runtime/value/` | compiler/ (imports only) |
| Generator state machine | `compiler/mir/generator.rs` + `runtime/value/async_gen.rs` | driver/ |
| Module system parsing | `parser/` (tokens, AST, statements) | compiler/ (stubs only) |
| Project configuration | `compiler/project.rs` | driver/, runtime/ |
| Module resolution | `compiler/module_resolver.rs` | driver/, parser/ |

### Example: Adding a New Builtin Method (e.g., `array.sum()`)

```rust
// 1. ONLY modify compiler/interpreter_method.rs
// 2. Find the array method dispatch section
// 3. Add the new method:

"sum" => {
    let sum = arr.iter()
        .filter_map(|v| v.as_int().ok())
        .sum::<i64>();
    Ok(Value::Int(sum))
}

// DON'T:
// - Add this to driver/
// - Create a new file
// - Modify common/
```

### Example: Adding a New Pointer Kind

```rust
// Step 1: Define in common/manual.rs
pub struct NewPtr<T> { ... }

// Step 2: Create wrapper in compiler/value.rs
pub struct NewPtrValue {
    ptr: NewPtr<Value>,  // Uses generic from common
}

// Step 3: Add Value variant in compiler/value.rs
pub enum Value {
    // ...
    NewPtr(NewPtrValue),
}

// Step 4: Handle in interpreter (evaluate_expr, etc.)

// DON'T:
// - Put NewPtrValue in common/
// - Create multiple wrapper implementations
```

### Cross-Module Communication Rules

```
┌─────────────────────────────────────────────────────────────┐
│ If module A needs to call module B:                         │
│                                                             │
│ 1. Define trait in common/                                  │
│ 2. B implements trait                                       │
│ 3. A uses trait, not B directly                             │
│                                                             │
│ Example: compiler → GC                                      │
│ - common/gc.rs: trait GcAllocator                          │
│ - runtime/memory/gc.rs: impl GcAllocator for GcRuntime     │
│ - compiler/pipeline.rs: fn with_gc(gc: Arc<dyn GcAllocator>)│
└─────────────────────────────────────────────────────────────┘
```

## Logging Strategy (cross-cutting)
- Use `tracing` for structured, span-based logging; init once via `simple_log::init()` (respects `SIMPLE_LOG`/`RUST_LOG`).
- Use `#[tracing::instrument]` to capture entry/exit/args with minimal overhead—this is the closest to AOP weaving Rust offers.
- Prefer spans with fields (`tracing::info_span!(...)`) over ad-hoc prints; keep logging opt-in for perf-sensitive paths.
- Rust has no runtime AOP; lean on proc-macros and DSL transforms if we need cross-cutting concerns.

---

## Formal Verification (Lean 4)

The `verification/` directory contains Lean 4 proofs for key safety invariants. Each model has a corresponding Rust implementation that exactly matches the Lean definitions.

### Model-Implementation Correspondence

| Model | Lean Project | Rust Location | Verified Properties |
|-------|--------------|---------------|---------------------|
| **Manual Pointer Borrow** | `manual_pointer_borrow/` | `common/manual.rs` | Borrow operations preserve validity |
| **GC Manual Borrow** | `gc_manual_borrow/` | `common/manual.rs` | GC collection preserves borrowed ⊆ live |
| **Async Compile (Async Safety)** | `async_compile/` | `compiler/mir/types.rs` | Non-blocking functions compose safely |
| **NoGC Compile** | `nogc_compile/` | `compiler/mir/types.rs` | NoGC programs compose safely |
| **Type Inference** | `type_inference_compile/` | `type/lib.rs` | Type inference is deterministic |

### Building Proofs

```bash
# Install Lean 4
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh

# Build individual proof
cd verification/manual_pointer_borrow && lake build

# All proofs verified with Lean 4.x
```

### Rust Types Matching Lean

```rust
// common/manual.rs - matches ManualPointerBorrow.lean
pub struct BorrowState { pub exclusive: bool, pub shared: Nat }
pub fn take_exclusive(s: BorrowState) -> BorrowState { ... }
pub fn borrow_state_valid(s: &BorrowState) -> bool { ... }

// compiler/mir/types.rs - matches AsyncCompile.lean (Async Safety)
// AsyncEffect tracks which operations may block (Wait = blocking, others = non-blocking)
pub enum AsyncEffect { Compute, Io, Wait }  // Wait = blocking operation
pub fn is_async(e: AsyncEffect) -> bool { !matches!(e, AsyncEffect::Wait) }  // Lean: is_async
pub fn pipeline_safe(es: &[AsyncEffect]) -> bool { es.iter().all(|e| is_async(*e)) }

// type/lib.rs - matches TypeInferenceCompile.lean
pub enum LeanTy { Nat, Bool, Arrow(Box<LeanTy>, Box<LeanTy>) }
pub fn lean_infer(expr: &LeanExpr) -> Option<LeanTy> { ... }
```

See `doc/formal_verification.md` for detailed correspondence tables and proofs.

---

## Refactoring Plan (grounded in current code)
- **Stabilize the memory boundary**: keep `simple_common::gc::GcAllocator` the only compiler/runtime contract; re-export `GcRuntime`/`NoGcAllocator` from `runtime::memory` and thread selection through the driver via config/env without leaking Abfall or manual allocators across crates.
- **Introduce a MIR/CFG layer in `compiler`**: lower parsed AST into a stable, borrow-checkable IR to host alias analysis, region checks, and later optimizations. Keep this IR independent of runtime details so features like borrowing or async safety (async) checks stay local.
- **Isolate pointer-kind semantics in `common`**: move any new borrow/region markers or handle pool ABI types into `common` and keep parser/runtime unaware of each other; compiler should translate to these markers only.
- **Module hygiene in runtime**: keep GC backends under `runtime::memory::{gc,no_gc}` and pool/concurrency in separate submodules; avoid cross-imports so swapping GC or introducing arenas does not affect the scheduler.
- **Diagnostics pipeline**: add a small error-reporting helper crate or module consumed by parser/type/borrow passes so new analyses (borrow checker, effects) can emit consistent spans without coupling passes together.
- **Driver simplification**: keep watch/build/run orchestration in `driver` using published interfaces only (`compiler::CompilerPipeline`, loaders, `runtime::memory` selection) to avoid circular reach as new features land.
