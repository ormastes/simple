# Architecture Overview

## Project Structure

```
simple/
├── CLAUDE.md                # Development guide
├── Cargo.toml               # Workspace definition
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
│   ├── waitless_compile/        # Effect tracking proofs
│   ├── nogc_compile/            # NoGC instruction proofs
│   └── type_inference_compile/  # Type inference proofs
│
├── src/                     # Source code (see below)
└── tests/                   # Integration tests
```

## Goals (grounded in feature list & language spec)
- Feature work should stay locally scoped: each feature touches parser → compiler → runtime via narrow contracts in `src/common/`.
- Minimize dependency fan-out: no "reach across" into unrelated modules to add a feature from `doc/feature.md`.
- Standardise interfaces (GC, ABI, loader) in `src/common/` so new features don't create ad-hoc couplings.
- Provide clear contracts for runtime/GC so memory management stays behind a stable boundary while implementing GC-managed default from the spec/feature list.
- Keep watch/build/run predictable and isolated to driver+compiler+loader; adding a language feature should not require touching them.
- Logging should be structured, low-overhead, and opt-in: prefer `tracing` spans/fields over ad-hoc prints. Use `#[tracing::instrument]` on hot paths when diagnostics are needed; avoid pervasive logging in perf-sensitive code paths by default.
- **Prevent Duplication**: Each concern belongs to exactly ONE module. If logic is needed in multiple places, define a shared abstraction in `common/` or create helper modules.
- **Formal Verification**: Key invariants (borrow safety, GC safety, effects) are modeled in Lean 4 and implemented exactly in Rust.

---

## Module Dependency Diagram

```
                    ┌─────────────┐
                    │   common    │  ← Zero dependencies, defines all contracts
                    └─────┬───────┘
                          │
        ┌─────────────────┼─────────────────┐
        │                 │                 │
        ▼                 ▼                 ▼
  ┌──────────┐      ┌──────────┐      ┌──────────┐
  │  parser  │      │   type   │      │  runtime │
  └────┬─────┘      └────┬─────┘      └────┬─────┘
       │                 │                 │
       └────────┬────────┘                 │
                │                          │
                ▼                          │
          ┌──────────┐                     │
          │ compiler │ ←───────────────────┘
          └────┬─────┘
               │
       ┌───────┼───────┐
       │       │       │
       ▼       │       ▼
  ┌────────┐   │  ┌──────────────┐
  │ loader │   │  │ native_loader│
  └────┬───┘   │  └──────┬───────┘
       │       │         │
       └───────┼─────────┘
               │
               ▼
          ┌────────┐
          │ driver │  ← Orchestrates everything
          └────────┘
```

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
│   ├── parser.rs        # Recursive descent parser
│   └── error.rs         # Parse error types
│
├── type/                # Type checking/inference
│   └── lib.rs           # TypeChecker, Substitution, Type enum, unify()
│                        # LeanTy/LeanExpr for formal verification
│
├── compiler/            # Compilation pipeline
│   ├── lib.rs           # Re-exports CompilerPipeline, Value, CompileError
│   ├── error.rs         # CompileError enum
│   ├── pipeline.rs      # CompilerPipeline - orchestrates compilation
│   ├── value.rs         # Value enum, Env, pointer wrappers
│   ├── effects.rs       # Effect checking (waitless violations)
│   ├── interpreter.rs   # Tree-walking interpreter entry
│   ├── interpreter_*.rs # Interpreter sub-modules (call, method, macro, extern, context)
│   ├── hir/             # High-level IR
│   │   ├── mod.rs
│   │   ├── types.rs     # HIR type representations
│   │   └── lower.rs     # AST → HIR lowering
│   ├── mir/             # Mid-level IR
│   │   ├── mod.rs
│   │   ├── types.rs     # MIR type representations
│   │   └── lower.rs     # HIR → MIR lowering
│   ├── codegen/         # Code generation
│   │   ├── mod.rs
│   │   └── cranelift.rs # Cranelift backend
│   └── linker/          # SMF emission
│       ├── mod.rs
│       └── smf_writer.rs
│
├── loader/              # SMF binary loading
│   ├── lib.rs           # Re-exports
│   ├── loader.rs        # ModuleLoader (DynLoader impl)
│   ├── module.rs        # LoadedModule (DynModule impl)
│   ├── registry.rs      # ModuleRegistry with symbol resolution
│   ├── smf/             # SMF format definitions
│   │   └── mod.rs       # SmfHeader, SmfSection, SmfSymbol, constants
│   └── memory/          # Memory mapping
│       ├── mod.rs
│       ├── common.rs    # Shared memory abstractions
│       ├── posix.rs     # POSIX mmap implementation
│       └── windows.rs   # Windows VirtualAlloc implementation
│
├── native_loader/       # OS dylib loading
│   ├── lib.rs           # Re-exports
│   ├── loader.rs        # ModuleLoader (DynLoader impl for .so/.dll)
│   ├── module.rs        # LoadedModule (DynModule impl)
│   └── registry.rs      # Type alias for common::ModuleRegistry
│
├── runtime/             # GC and concurrency
│   ├── lib.rs           # Re-exports gc module
│   ├── memory/
│   │   ├── mod.rs
│   │   ├── gc.rs        # GcRuntime (Abfall wrapper, logging)
│   │   └── no_gc.rs     # NoGcAllocator (GC-off profile)
│   └── concurrency/
│       └── mod.rs       # (Future: scheduler, async runtime)
│
├── driver/              # CLI and orchestration
│   ├── lib.rs           # Re-exports Runner, Interpreter, watch
│   ├── main.rs          # CLI entry point
│   ├── runner.rs        # Runner - compile & run files
│   ├── exec_core.rs     # ExecCore - shared compile/load/run logic
│   ├── interpreter.rs   # Interpreter - programmatic API
│   ├── dependency_cache.rs # Import/macro dependency tracking
│   └── watcher/
│       └── mod.rs       # File watching for hot reload
│
├── lib/                 # Native stdlib
│   └── src/
│       └── io/
│           └── term/    # Terminal I/O bindings
│
└── log/                 # Logging facade
    └── lib.rs           # simple_log::init(), tracing setup
```

---

## File-Based Type/Struct/Enum Listing

### common/src/

**`lib.rs`** - Core module traits and caching
- `trait DynModule` - Runtime module interface
- `trait DynLoader` - Module loader interface
- `struct ModuleCache<M,E>` - Generic thread-safe caching
- `struct ModuleRegistry<L>` - Loader + cache combination

**`gc.rs`** - GC contract
- `trait GcAllocator` - Memory allocation contract
- `trait GcHandle` - Marker for GC-managed references

**`config_env.rs`** - Configuration
- `struct ConfigEnv` - Dict-like config/env/args access

**`actor.rs`** - Actor system
- `enum Message` - Actor message types
- `enum ActorLifecycle` - Actor state machine
- `struct ActorHandle` - Communication handle
- `trait ActorSpawner` - Spawning interface
- `struct ThreadSpawner` - Thread-based spawner

**`manual.rs`** - Manual memory management
- `struct Nat` - Natural number newtype
- `struct BorrowState` - Borrow tracking
- `enum ValidBorrowState` - Verified borrow states
- `struct BorrowTracker` - Runtime borrow checker
- `struct ValidBorrowTracker` - Verified tracker
- `struct GcState` - GC state tracking
- `struct GcStateVerify` - GC verification
- `struct GcStateTracker` - GC tracker
- `struct ManualGc` - Manual memory arena
- `struct Unique<T>` - Unique ownership pointer
- `struct Shared<T>` - Reference-counted pointer
- `struct WeakPtr<T>` - Weak reference
- `struct HandlePool<T>` - Handle allocation pool
- `struct Handle<T>` - Pool-managed handle

---

### parser/src/

**`lexer.rs`** - Tokenization
- `struct Lexer<'a>` - Source → Token stream

**`token.rs`** - Token types
- `struct Span` - Source location range
- `enum FStringToken` - F-string parts
- `enum TokenKind` - Token type enum
- `struct Token` - Token with position

**`parser.rs`** - Parsing
- `struct Parser<'a>` - Token stream → AST

**`error.rs`** - Errors
- `enum ParseError` - Parse error types

**`ast.rs`** - AST nodes
- `enum Visibility` - Pub/private
- `enum Mutability` - Mut/immut
- `enum RangeBound` - Range bounds
- `enum SelfMode` - Self parameter modes
- `enum Node` - Top-level AST node
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

**`interpreter.rs`** - Interpreter entry
- `enum Control` - Control flow (via include!)
- Includes: `interpreter_call.rs`, `interpreter_method.rs`, `interpreter_macro.rs`, `interpreter_extern.rs`, `interpreter_context.rs`

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
- `enum WaitlessEffect`
- `enum NogcInstr`
- `enum Effect` ⚠️ *Also in ast.rs*
- `struct EffectSet`
- `trait HasEffects`
- `enum BuiltinFunc`, `CallTarget`
- `struct BlockId`, `VReg`
- `enum MirInst`, `Terminator`
- `enum BlockBuildState`, `BlockBuildError`
- `struct BlockBuilder`, `MirBlock`
- `struct MirLocal`, `MirFunction`, `MirModule`

**`mir/lower.rs`** - HIR→MIR
- `struct LoopContext`
- `enum LowererState`, `BlockState`
- `enum MirLowerError`
- `type MirLowerResult<T>`
- `struct MirLowerer`

**`codegen/cranelift.rs`** - Code generation
- `enum CodegenError`
- `type CodegenResult<T>`
- `struct Codegen`

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

**`memory/gc.rs`** - GC runtime
- `enum GcLogEventKind`
- `struct GcLogEvent`
- `struct GcRuntime`

**`memory/no_gc.rs`** - No-GC allocator
- `struct NoGcAllocator`

**`concurrency/mod.rs`** - Concurrency
- `struct ScheduledSpawner`

---

### driver/src/

**`exec_core.rs`** - Low-level execution engine (shared logic)
- `struct ExecCore`
  - `compile_source(source, out)` - Compile source to SMF file
  - `compile_file(path, out)` - Compile file to SMF
  - `compile_to_memory(source)` - Compile to bytes, no disk I/O (TODO)
  - `load_module(path)` - Load SMF from file
  - `load_module_from_memory(bytes)` - Load SMF from memory (TODO)
  - `run_smf(path)` - Run pre-compiled SMF file
  - `run_smf_from_memory(bytes)` - Run SMF from memory (TODO)
  - `run_source(source)` - Compile and run (uses temp file)
  - `run_source_in_memory(source)` - Compile and run, no disk I/O (TODO)
  - `run_file(path)` - Auto-detect .spl/.smf and run

**`runner.rs`** - Mid-level public API
- `struct Runner`
  - `run_source(source)` - Compile and run source string
  - `run_file(path)` - Run .spl or .smf file (auto-detect)
  - `run_smf(path)` - Run pre-compiled SMF directly
  - `compile_to_smf(source, out)` - Compile source to SMF file
  - `compile_to_memory(source)` - Compile to bytes (TODO)

**`interpreter.rs`** - High-level API with I/O capture
- `struct Interpreter`
  - Uses `Runner` internally (delegates execution)
  - `run(code, config)` - Run with configuration
  - `run_simple(code)` - Run without config
  - `run_in_memory(code)` - Run without disk I/O (TODO)
  - `runner()` - Access underlying Runner
- `struct RunResult` - exit_code, stdout, stderr
- `struct RunConfig` - args, stdin, timeout_ms, in_memory

**`dependency_cache.rs`** - Caching
- `struct DepInfo`
- `struct BuildCache`

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

### parser (depends: common)
- Pure syntax; no semantic analysis
- Adding new syntax: ONLY modify parser/
- No interpretation, no type checking

### type (depends: parser, common)
- Type inference and checking
- No runtime values, no interpretation

### compiler (depends: parser, type, common, loader/smf)
- Interpretation lives HERE (not in driver)
- Value types live HERE (not in common)
- Uses loader/smf only for format structs

### loader/native_loader (depends: common)
- DynLoader/DynModule implementations
- No parser/compiler/runtime dependencies
- Hot reload logic stays HERE

### runtime (depends: common)
- GcAllocator implementation
- Scheduler (future)
- No compiler/parser dependencies

### driver (depends: all except runtime internals)
- Uses `GcAllocator` trait, not `GcRuntime` directly
- Orchestration only; no business logic

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
| **Waitless Compile** | `waitless_compile/` | `compiler/mir/types.rs` | Waitless effects compose safely |
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

// compiler/mir/types.rs - matches WaitlessCompile.lean
pub enum WaitlessEffect { Compute, Io, Wait }
pub fn waitless(e: WaitlessEffect) -> bool { !matches!(e, WaitlessEffect::Wait) }
pub fn pipeline_safe(es: &[WaitlessEffect]) -> bool { es.iter().all(|e| waitless(*e)) }

// type/lib.rs - matches TypeInferenceCompile.lean
pub enum LeanTy { Nat, Bool, Arrow(Box<LeanTy>, Box<LeanTy>) }
pub fn lean_infer(expr: &LeanExpr) -> Option<LeanTy> { ... }
```

See `doc/formal_verification.md` for detailed correspondence tables and proofs.

---

## Refactoring Plan (grounded in current code)
- **Stabilize the memory boundary**: keep `simple_common::gc::GcAllocator` the only compiler/runtime contract; re-export `GcRuntime`/`NoGcAllocator` from `runtime::memory` and thread selection through the driver via config/env without leaking Abfall or manual allocators across crates.
- **Introduce a MIR/CFG layer in `compiler`**: lower parsed AST into a stable, borrow-checkable IR to host alias analysis, region checks, and later optimizations. Keep this IR independent of runtime details so features like borrowing or waitless checks stay local.
- **Isolate pointer-kind semantics in `common`**: move any new borrow/region markers or handle pool ABI types into `common` and keep parser/runtime unaware of each other; compiler should translate to these markers only.
- **Module hygiene in runtime**: keep GC backends under `runtime::memory::{gc,no_gc}` and pool/concurrency in separate submodules; avoid cross-imports so swapping GC or introducing arenas does not affect the scheduler.
- **Diagnostics pipeline**: add a small error-reporting helper crate or module consumed by parser/type/borrow passes so new analyses (borrow checker, effects) can emit consistent spans without coupling passes together.
- **Driver simplification**: keep watch/build/run orchestration in `driver` using published interfaces only (`compiler::CompilerPipeline`, loaders, `runtime::memory` selection) to avoid circular reach as new features land.
