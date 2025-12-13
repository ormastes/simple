# Simple Language Compiler - Development Guide

## Current File Structure

```
simple/
├── Cargo.toml                     # Workspace definition (12 crates)
├── Makefile                       # Build automation (test, coverage, lint, etc.)
├── .jscpd.json                    # Code duplication detection config
├── CLAUDE.md                      # This file - development guide
├── public_api.yml                 # Public API definitions for coverage
│
├── lib/                           # Simple standard library (written in Simple)
│   └── std/                       # stdlib root
│       ├── __init__.spl           # Root manifest with #[deny(primitive_api)]
│       ├── core/                  # Variant-agnostic pure core (mutable)
│       ├── core_immut/            # Variant-agnostic, #[immutable]
│       ├── core_nogc/             # Variant-agnostic, #[no_gc] (mutable)
│       ├── core_nogc_immut/       # Variant-agnostic, #[no_gc] + #[immutable]
│       ├── simd/                  # Cross-platform SIMD & vector math
│       ├── host/                  # OS-based stdlib overlays
│       │   └── async_nogc_mut/    # DEFAULT: async + no_gc + mutable
│       ├── bare/                  # Baremetal (single variant: async+nogc+immut)
│       ├── gpu/                   # GPU device & host APIs
│       │   ├── kernel/            # Device-side (single: async+nogc+immut)
│       │   └── host/async_nogc_mut/  # Host-side GPU control
│       └── tools/                 # Diagnostics, testing, reflection
│
├── native_lib/                    # Native implementations (written in Rust)
│   ├── core/                      # Memory allocation, GC interface, math intrinsics
│   ├── io/                        # Filesystem, networking, terminal I/O
│   ├── sys/                       # Args, env, process, time
│   ├── sync/                      # Mutexes, channels, atomics
│   └── ffi/                       # FFI bridge and type conversions
│
├── log/                           # Logging crate (tracing wrapper)
│   └── src/lib.rs                 # simple_log::init() entry point
│
├── doc/                           # Documentation
│   ├── architecture.md            # Design principles and dependency rules
│   ├── codegen_technical.md       # Codegen implementation details
│   ├── feature.md                 # Feature list with importance/difficulty ratings
│   ├── formal_verification.md     # Lean 4 formal verification docs
│   ├── import_export_and__init__.md  # Module system specification (v4)
│   ├── test.md                    # Test policy (mock control, coverage, test levels)
│   ├── spec/                      # Language specifications
│   │   ├── language.md            # Spec index with quick reference
│   │   ├── syntax.md              # Lexical structure, literals, operators
│   │   ├── types.md               # Type system, mutability, primitive warnings
│   │   ├── units.md               # Unit types, semantic typing, lint policy
│   │   ├── data_structures.md     # Structs, classes, enums, unions
│   │   ├── functions.md           # Functions, pattern matching, constructors
│   │   ├── traits.md              # Traits and implementations
│   │   ├── memory.md              # Memory management, ownership, pointers
│   │   ├── concurrency.md         # Actors, async/await, threads, futures
│   │   ├── metaprogramming.md     # Macros, DSL, decorators, comprehensions
│   │   ├── stdlib.md              # Standard library spec (lib/, native_lib/)
│   │   ├── gpu_simd.md            # GPU and SIMD specification
│   │   └── lexer_parser.md        # Parser/lexer specification
│   ├── design/                    # Design documents
│   │   ├── memory.md              # Memory management design
│   │   ├── type_inference.md      # Type inference design
│   │   └── concurrency.md         # Concurrency design
│   ├── status/                    # Feature implementation status (79+ files)
│   ├── plans/                     # Implementation plans
│   └── research/                  # Research notes
│
├── verification/                  # Lean 4 formal verification projects
│   ├── manual_pointer_borrow/     # Borrow checker model
│   ├── gc_manual_borrow/          # GC safety model
│   ├── async_compile/             # Effect tracking model
│   ├── nogc_compile/              # NoGC instruction model
│   └── type_inference_compile/    # Type inference model
│
├── tests/                         # Integration/system tests
│
└── src/
    ├── common/                    # Shared contracts (no dependencies)
    │   └── src/
    │       ├── lib.rs             # DynLoader, DynModule traits
    │       └── config_env.rs      # ConfigEnv - dict interface for config/env/args
    │
    ├── parser/                    # Lexer, Parser, AST (depends: common)
    │   └── src/
    │       ├── lib.rs
    │       ├── lexer.rs           # Tokenization with INDENT/DEDENT
    │       ├── parser.rs          # Main parser entry point
    │       ├── ast.rs             # AST node definitions
    │       ├── token.rs           # Token types
    │       ├── error.rs           # Parse error types
    │       ├── expressions/       # Expression parsing (Pratt parser)
    │       │   └── mod.rs
    │       ├── statements/        # Statement parsing
    │       │   └── mod.rs
    │       └── types_def/         # Type parsing
    │           └── mod.rs
    │
    ├── type/                      # Type checker/inference (HM scaffold)
    │   └── src/lib.rs             # Unification, generalize/instantiate, core expr inference
    │
    ├── compiler/                  # HIR, MIR, Codegen (depends: parser, common, runtime)
    │   └── src/
    │       ├── lib.rs             # Compilation entry point
    │       ├── pipeline.rs        # CompilerPipeline orchestration
    │       ├── project.rs         # ProjectContext - project detection & config
    │       ├── module_resolver.rs # ModuleResolver - path→file resolution
    │       ├── value.rs           # Value enum, Env, pointer wrappers
    │       ├── effects.rs         # Effect checking (async safety)
    │       ├── interpreter.rs     # Tree-walking interpreter (main entry)
    │       ├── interpreter_call.rs     # Function call handling
    │       ├── interpreter_control.rs  # Control flow (if, match, loops)
    │       ├── interpreter_context.rs  # Execution context management
    │       ├── interpreter_extern.rs   # External function bindings
    │       ├── interpreter_ffi.rs      # FFI bridge for compiled↔interpreter
    │       ├── interpreter_helpers.rs  # Utility functions
    │       ├── interpreter_macro.rs    # Macro expansion
    │       ├── interpreter_method.rs   # Method dispatch
    │       ├── value_bridge.rs    # FFI value marshalling (BridgeValue)
    │       ├── compilability.rs   # Compilability analysis (20+ fallback reasons)
    │       ├── hir/               # High-level IR
    │       │   ├── mod.rs
    │       │   ├── types.rs       # Type system
    │       │   └── lower.rs       # AST → HIR lowering
    │       ├── mir/               # Mid-level IR
    │       │   ├── mod.rs
    │       │   ├── types.rs       # MIR types, effects, patterns
    │       │   ├── instructions.rs # 50+ MIR instruction variants
    │       │   ├── blocks.rs      # Basic block management
    │       │   ├── function.rs    # Function-level MIR
    │       │   ├── effects.rs     # Effect tracking and analysis
    │       │   ├── generator.rs   # Generator state machine lowering
    │       │   └── lower.rs       # HIR → MIR lowering
    │       ├── codegen/
    │       │   ├── mod.rs
    │       │   ├── cranelift.rs   # AOT Cranelift backend
    │       │   ├── jit.rs         # JIT Cranelift backend
    │       │   ├── runtime_ffi.rs # Shared FFI function specs (50+ functions)
    │       │   └── types_util.rs  # Type conversion utilities
    │       └── linker/            # SMF emission
    │           ├── mod.rs
    │           └── smf_writer.rs
    │
    ├── loader/                    # SMF binary loader (depends: common)
    │   └── src/
    │       ├── lib.rs
    │       ├── loader.rs          # ModuleLoader
    │       ├── module.rs          # LoadedModule
    │       ├── registry.rs        # ModuleRegistry with symbol resolution
    │       ├── smf/               # SMF format definitions
    │       │   ├── mod.rs
    │       │   ├── header.rs
    │       │   ├── section.rs
    │       │   ├── symbol.rs
    │       │   └── reloc.rs
    │       └── memory/            # Memory mapping
    │           ├── mod.rs
    │           ├── posix.rs
    │           └── windows.rs
    │
    ├── native_loader/             # OS dylib loader (depends: common)
    │   └── src/lib.rs
    │
    ├── runtime/                   # GC, concurrency, and runtime values
    │   └── src/
    │       ├── lib.rs             # Re-exports
    │       ├── value/             # Runtime value system (9 modules)
    │       │   ├── mod.rs         # Re-exports all value types and 50+ FFI functions
    │       │   ├── core.rs        # RuntimeValue - 64-bit tagged pointer
    │       │   ├── tags.rs        # Tag constants
    │       │   ├── heap.rs        # HeapHeader, HeapObjectType
    │       │   ├── collections.rs # RuntimeArray, RuntimeTuple, RuntimeDict, RuntimeString + FFI
    │       │   ├── objects.rs     # RuntimeObject, RuntimeClosure, RuntimeEnum + FFI
    │       │   ├── ffi.rs         # Value conversion and core FFI
    │       │   ├── actors.rs      # RuntimeActor + FFI (spawn/send/recv)
    │       │   └── async_gen.rs   # RuntimeFuture, RuntimeGenerator + FFI
    │       ├── memory/
    │       │   ├── mod.rs         # Memory allocation abstraction
    │       │   ├── gc.rs          # GcRuntime + logging hooks
    │       │   ├── gcless.rs      # GC-less allocator wrapper
    │       │   └── no_gc.rs       # NoGcAllocator
    │       └── concurrency/
    │           └── mod.rs         # Actor scheduler
    │
    ├── pkg/                       # Package manager (UV-style)
    │   └── src/
    │       ├── lib.rs             # Package manager entry
    │       ├── manifest.rs        # simple.toml parsing
    │       ├── lock.rs            # simple.lock format
    │       ├── cache.rs           # Global cache with hard links
    │       ├── version.rs         # Version and VersionReq
    │       ├── resolver/          # Dependency resolution
    │       │   └── graph.rs       # Topological ordering
    │       └── commands/          # CLI: init, add, install, update, list, cache
    │
    └── driver/                    # CLI runner (depends: all)
        ├── src/
        │   ├── lib.rs
        │   ├── main.rs            # CLI entry (run, --gc-log)
        │   ├── runner.rs          # Compile and execute
        │   ├── exec_core.rs       # Shared compile/load/run logic
        │   ├── interpreter.rs     # High-level API with I/O capture
        │   ├── dependency_cache.rs # Import/macro tracking
        │   └── watcher/
        │       └── mod.rs         # File watching for hot reload
        └── tests/                 # Driver integration tests (17 files)
            ├── runner_tests.rs         # Core runner tests
            ├── runner_async_tests.rs   # Async/concurrency tests
            ├── module_tests.rs         # Module system tests (19 tests)
            ├── watcher_tests.rs        # File watcher tests
            └── interpreter_*.rs        # Interpreter tests (13 files)
                                        # async, basic, bindings, collections,
                                        # control, expressions, extern, jit,
                                        # macros, memory, oop, strings, types
```

## Compilation Pipeline

```
Source Code (.spl)
       │
       ▼
   ┌─────────┐
   │  Lexer  │  → Tokens (with INDENT/DEDENT)
   └────┬────┘
        │
        ▼
   ┌─────────┐
   │ Parser  │  → AST (Node, Statement, Expr)
   └────┬────┘
        │
        ▼
   ┌─────────┐
   │   HIR   │  → Type-checked IR
   └────┬────┘
        │
        ▼
   ┌─────────┐
   │   MIR   │  → 50+ instructions with effect annotations
   └────┬────┘
        │
    ┌───┴───┐
    ▼       ▼
┌────────┐ ┌──────────────┐
│Compiled│ │ Interpreter  │  ← Hybrid execution
│(Crane- │ │  Fallback    │
│ lift)  │ │              │
└───┬────┘ └──────┬───────┘
    │             │
    └──────┬──────┘
           ▼
   ┌─────────┐
   │   SMF   │  → Binary module format
   └────┬────┘
        │
        ▼
   ┌─────────┐
   │ Loader  │  → Memory-mapped executable
   └────┬────┘
        │
        ▼
   Execution (main → exit code)
```

### Syntax Notes
- `match` arms accept both `case pattern:` (spec style) and `pattern =>` (existing tests); colon form requires a newline + indented block.

## Current Status

| Component | Status |
|-----------|--------|
| Lexer | Complete |
| Parser | Complete (modular: expressions, statements, types_def) |
| AST | Complete |
| HIR | Complete (type-checked IR) |
| MIR | Complete (50+ instructions, generator state machine lowering) |
| Codegen | Hybrid (Cranelift + Interpreter fallback, 50+ runtime FFI functions) |
| RuntimeValue | Complete (9 modules, tagged pointers, 50+ FFI functions) |
| SMF Loader | Complete |
| Driver | Complete (exec_core, runner, interpreter layers) |
| Runtime/GC | Abfall-backed wrapper with optional logging |
| Package Manager | Complete (UV-style: manifest, lock, cache, resolution) |
| Module System | Parsing complete, resolution infrastructure ready |

### MIR Instruction Categories

| Category | Count | Examples |
|----------|-------|----------|
| Core | 6 | ConstInt, BinOp, UnaryOp, Copy |
| Memory | 6 | Load, Store, GcAlloc, Wait |
| Collections | 7 | ArrayLit, TupleLit, DictLit, IndexGet, Slice |
| Strings | 3 | ConstString, ConstSymbol, FStringFormat |
| Closures | 2 | ClosureCreate, IndirectCall |
| Objects | 6 | StructInit, FieldGet, FieldSet, MethodCall* |
| Patterns | 6 | PatternTest, PatternBind, EnumDiscriminant |
| Async | 5 | FutureCreate, Await, ActorSpawn, ActorSend |
| Generators | 3 | GeneratorCreate, Yield, GeneratorNext |
| Errors | 5 | TryUnwrap, OptionSome, ResultOk, ResultErr |
| Fallback | 2 | InterpCall, InterpEval |

### Codegen status snapshot (runtime FFI)
- Actors: Spawn/Send/Recv now call runtime FFI; actor bodies still use a no-op stub until outlining is added.
- Generators: Yield/Next wired to runtime eager collector; generator bodies also use the stub pointer (no state machine yet).
- Futures: FutureCreate uses the same stubbed body pointer; Await calls runtime stub.

## Logging Strategy
- Use `tracing` for structured, span-based logging. Initialize once via `simple_log::init()` (respects `SIMPLE_LOG`/`RUST_LOG`).
- For cross-cutting “AOP-like” logging, prefer `#[tracing::instrument]` on functions to capture args/latency without manual boilerplate.
- Keep logging opt-in to avoid overhead; avoid ad-hoc `println!` on hot paths.

## Test Strategy

See `doc/test.md` for the complete test policy. Tests use `simple_mock_helper` for mock control and coverage tracking.

**Current Test Count: 631+ tests**

### Test Levels and Coverage Metrics

| Level | Tests | Mock Policy | Coverage Metric | Command |
|-------|-------|-------------|-----------------|---------|
| **Unit** | 631+ | All mocks | Branch/Condition | `make test-unit` |
| **Integration** | 9 | HAL-only | Public func on class/struct | `make test-it` |
| **System** | 8 | No mocks | Class/struct method | `make test-system` |
| **Environment** | 7 | HAL/External/Lib | Branch/Condition | `make test-env` |

### Coverage Commands

```bash
# Show coverage by test level
make coverage-unit      # Unit: branch/condition coverage
make coverage-it        # IT: public function on class/struct
make coverage-system    # System: class/struct method coverage
make coverage-env       # Environment: branch/condition
make coverage-all       # Generate all reports
```

### Test Binary Initialization

Each test binary initializes its mock policy via `#[ctor::ctor]`:

```rust
use ctor::ctor;
use simple_mock_helper::{init_unit_tests, validate_test_config};

#[ctor]
fn init() {
    init_unit_tests!("my_crate_unit");
}

#[test]
fn validate_config() {
    validate_test_config().expect_pass();
}
```

### TDD Cycle

```
Red    → Write failing test
Green  → Minimal implementation to pass
Refactor → Clean up, maintain passing tests
```

## Running Tests

```bash
# All tests
cargo test --workspace

# Specific crate
cargo test -p simple-driver

# Specific test
cargo test -p simple-driver runner_compiles
```

## Code Quality Tools

### Quick Commands (Makefile)

```bash
make check             # fmt + lint + test (before commit)
make check-full        # All checks + coverage + duplication
make help              # Show all available targets
```

### Test Coverage

Uses `cargo-llvm-cov` for accurate coverage measurement. Coverage metrics vary by test level:

| Test Level | Coverage Metric | Target |
|------------|-----------------|--------|
| Unit | Branch/Condition | 100% |
| Integration | Public function on class/struct | 100% |
| System | Class/struct method | 100% |
| Environment | Branch/Condition (merged with Unit) | 100% |

```bash
# Coverage by test level
make coverage-unit      # Unit: branch/condition (all 631+ tests)
make coverage-it        # IT: public function on class/struct
make coverage-system    # System: class/struct method coverage
make coverage-env       # Environment: branch/condition

# Combined reports
make coverage           # HTML report → target/coverage/html/index.html
make coverage-all       # All test level reports
make coverage-summary   # Print summary to console
```

Install: `cargo install cargo-llvm-cov`

**Coverage Goals:**
- Unit tests: 100% branch and condition coverage
- IT tests: 100% public function coverage on class/struct (defined in public_api.yml)
- System tests: 100% class/struct method coverage (defined in public_api.yml)
- Focus on: parser edge cases, type system branches, error handling paths

**Test Helper Pattern (reduces duplication):**
```rust
/// Helper to run source and assert expected exit code
fn run_expect(src: &str, expected: i32) {
    let runner = Runner::new();
    let exit = runner.run_source(src).expect("run ok");
    assert_eq!(exit, expected);
}

#[test]
fn test_arithmetic() {
    run_expect("main = 1 + 2", 3);
    run_expect("main = 10 - 3", 7);
    run_expect("main = 6 * 7", 42);
}
```

### Code Duplication Detection

Uses `jscpd` for detecting copy-paste code that should be refactored.

```bash
make duplication       # Full report → target/duplication/
make duplication-simple # Grep-based fallback (no npm needed)
jscpd ./src            # Direct run with .jscpd.json config
```

**Configuration (`.jscpd.json`):**
```json
{
  "threshold": 2,        // Max allowed duplication % (fail if exceeded)
  "minLines": 5,         // Minimum lines to detect as clone
  "minTokens": 50,       // Minimum tokens to detect as clone
  "ignore": ["**/target/**", "**/*.md"]
}
```

**Adjusting Detection Sensitivity:**
```bash
# For stricter detection (find smaller duplicates):
jscpd ./src --min-lines 3 --min-tokens 10

# For test files specifically:
jscpd ./src/driver/tests --min-lines 3 --min-tokens 10
```

**Refactoring Duplicates:**
1. Run `jscpd` to identify clones
2. Extract common patterns into helper functions/structs
3. Use builder patterns for complex object creation (see `SmfBuilder` in loader_tests.rs)
4. Use parameterized test helpers (see `run_expect` in runner_tests.rs)

Install: `npm install -g jscpd`

### Linting & Formatting

```bash
make lint              # Clippy with warnings as errors
make lint-fix          # Auto-fix clippy suggestions
make fmt               # Format all code
make fmt-check         # Check formatting (CI-friendly)
```

### Install All Tools

```bash
make install-tools     # Installs cargo-llvm-cov, cargo-audit, cargo-outdated
```

Optional (requires npm): `npm install -g jscpd`

## Logging Strategy
- Use `tracing` for structured, span-based logging. Initialize via `simple_log::init()` (respects `SIMPLE_LOG`/`RUST_LOG` filters).
- For “AOP-like” logging, prefer `#[tracing::instrument]` on functions to auto-capture args/latency without scattering manual logs.
- Avoid noisy logging on hot paths by default; keep it opt-in via env filters. Rust doesn’t do runtime AOP—proc macros + spans give the “weaving” you need at compile time.

## How to Write System Tests (CLI/TUI)
- Add `shadow-terminal` to the crate hosting the CLI tests (likely `src/driver`) so tests can spawn the binary in a fake PTY, send keys, and assert the screen/output without a real terminal.
- Follow the flow in `doc/test.md`:
  - Create a temp dir and write a `main.spl` (and any imports) to exercise dependency analysis and SMF emission.
  - Spawn the CLI via `shadow_terminal::Command::new([...])` with `rows/cols` set; wait for banners or diagnostics with `wait_for_stdout`.
  - Assert exit code (`wait_for_exit_success`), artifact existence (`.with_extension("smf")` non-empty), and readable buffers (no ANSI errors or wrapped lines).
  - For watch-mode scenarios, mutate the source after starting the command and assert a rebuild message + updated `.smf` mtime; remember to stop the process (`kill`) at the end of the test.
- Keep system tests fast and isolated: no network, only temp directories, and avoid assuming a specific shell. Use plain-text assertions for errors so failures are legible in CI logs.
- System tests must use `init_system_tests!()` - no mocks allowed.

## Key Files

### Compiler Core
- `src/compiler/src/lib.rs` - Compilation entry point
- `src/compiler/src/pipeline.rs` - CompilerPipeline orchestration
- `src/compiler/src/hir/mod.rs` - AST → HIR lowering
- `src/compiler/src/mir/generator.rs` - Generator state machine lowering
- `src/compiler/src/codegen/cranelift.rs` - AOT Cranelift backend
- `src/compiler/src/codegen/jit.rs` - JIT Cranelift backend
- `src/compiler/src/codegen/runtime_ffi.rs` - FFI function specs (50+ functions)

### Interpreter
- `src/compiler/src/interpreter.rs` - Main interpreter entry
- `src/compiler/src/interpreter_*.rs` - 8 interpreter modules

### Runtime
- `src/runtime/src/value/` - Runtime value system (9 modules)
- `src/runtime/src/memory/` - Memory management (4 modules)

### Driver & Tests
- `src/driver/src/exec_core.rs` - Shared compile/load/run logic
- `src/driver/tests/runner_tests.rs` - Core runner tests
- `src/driver/tests/interpreter_*.rs` - Interpreter tests (13 files)

### Module System
- `src/compiler/src/project.rs` - ProjectContext (project detection, simple.toml parsing)
- `src/compiler/src/module_resolver.rs` - ModuleResolver (path→file resolution, __init__.spl parsing)
- `src/parser/src/ast.rs` - Module AST nodes (ModulePath, ImportTarget, UseStmt, etc.)
- `src/driver/tests/module_tests.rs` - Module system tests (19 tests)

### Package Manager
- `src/pkg/src/` - UV-style package manager

### Documentation
- `doc/codegen_technical.md` - Codegen implementation details
- `doc/import_export_and__init__.md` - Module system specification
- `doc/status/` - Feature implementation status (79+ files)
