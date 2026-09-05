# Architecture: Data Flow and Execution

Part of [Architecture Overview](architecture.md).

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


---

Next: [Development Guide](architecture_dev.md)
