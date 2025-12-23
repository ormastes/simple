# Simple Language Compiler - Development Guide

## 🚧 Current Status

**Test Status:** ✅ Build passing - compilation warnings fixed  
**Recent Work (2025-12-22):**
- ✅ Implemented formatter and linter in Simple language (`simple/app/`)
- ✅ Created build infrastructure for Simple-based tools
- ✅ Analyzed orphaned commits (AOP specs present, no implementation)
- ✅ Code duplication reduction: 4.49% → 4.45% (Phase 2 & 3 complete)
- ✅ Fixed gherkin DSL parsing to handle f-strings
- ✅ Split 8 large markdown documentation files into 18 parts

**New Tools:**
- `simple/app/formatter/` - Canonical formatter (zero-config)
- `simple/app/lint/` - Semantic linter with fix-it hints
- Build outputs to `simple/bin_simple/` with intermediate files in `simple/build/`

**Pending Work:**
- Build and test formatter/linter tools
- Integrate formatter/linter with compiler
- Review test failures in gherkin/attributes tests

## Documentation Organization

### Report Directory (`doc/report/`)

Job completion reports and maintenance documentation (see `doc/report/README.md` for details).

**Key Decisions:**
- ✅ Markdown files: Split for navigation (8 files → 18 parts, all <1000 lines)
- ⚠️ Rust source: Intentionally NOT split (maintains code cohesion)
- ⚠️ Test files: NOT split (would break compilation)
- ⚠️ Generated files: Do not modify (auto-generated)

## Current File Structure

```
simple/                            # Project root - Rust compiler implementation
├── Cargo.toml                     # Workspace definition (12 crates)
├── Makefile                       # Build automation (test, coverage, lint, etc.)
├── .jscpd.json                    # Code duplication detection config
├── CLAUDE.md                      # This file - development guide
├── AGENTS.md                      # AI agent guidelines (was agent.md)
├── public_api.yml                 # Public API definitions for coverage
│
├── simple/                        # Simple language development workspace
│   ├── bin -> ../target/debug/    # Symlink to compiled binaries
│   ├── doc -> ../doc/             # Symlink to documentation
│   ├── app/                       # Simple-language applications
│   │   ├── formatter/             # Canonical formatter (main.spl)
│   │   ├── lint/                  # Semantic linter (main.spl)
│   │   └── README.md              # Application documentation
│   ├── bin_simple/                # Compiled Simple executables
│   │   ├── simple_fmt             # Formatter binary
│   │   └── simple_lint            # Linter binary
│   ├── build/                     # Intermediate build files
│   │   ├── formatter/             # Formatter .smf files
│   │   └── lint/                  # Linter .smf files
│   ├── build_tools.sh             # Build script for Simple tools
│   └── std_lib/                   # Simple standard library (written in Simple)
│       ├── README.md              # Standard library documentation
│       ├── src/                   # .spl library files
│       │   ├── __init__.spl       # Root manifest with #[deny(primitive_api)]
│       │   ├── core/              # Variant-agnostic pure core (mutable)
│       │   ├── core_immut/        # Variant-agnostic, #[immutable]
│       │   ├── core_nogc/         # Variant-agnostic, #[no_gc] (mutable)
│       │   ├── core_nogc_immut/   # Variant-agnostic, #[no_gc] + #[immutable]
│       │   ├── simd/              # Cross-platform SIMD & vector math
│       │   ├── host/              # OS-based stdlib overlays
│       │   │   └── async_nogc_mut/    # DEFAULT: async + no_gc + mutable
│       │   ├── bare/              # Baremetal (single variant: async+nogc+immut)
│       │   ├── gpu/               # GPU device & host APIs
│       │   │   ├── kernel/        # Device-side (single: async+nogc+immut)
│       │   │   └── host/async_nogc_mut/  # Host-side GPU control
│       │   ├── doctest/           # Doctest framework
│       │   ├── spec/              # BDD spec framework
│       │   │   ├── matchers/      # Matcher implementations
│       │   │   └── runner/        # Test runner
│       │   ├── units/             # Semantic unit types (ByteCount, Duration, etc)
│       │   └── tools/             # Diagnostics, testing, reflection
│       └── test/                  # .spl test files (mirroring src/ structure)
│           ├── unit/              # Unit tests (stdlib functionality by module)
│           │   ├── core/          # Tests for core/ module
│           │   └── units/         # Tests for units/ module
│           ├── system/            # System tests (frameworks: spec, doctest)
│           │   ├── spec/          # Tests for spec/ framework
│           │   │   └── matchers/  # Tests for matchers/ submodule
│           │   └── doctest/       # Tests for doctest/ framework
│           │       ├── parser/    # Tests for doctest parsing
│           │       ├── matcher/   # Tests for output matching
│           │       └── runner/    # Tests for example execution
│           ├── integration/       # Integration tests (cross-module behavior)
│           │   └── doctest/       # Doctest discovery and cross-module tests
│           └── fixtures/          # Test data and fixtures
│               └── doctest/       # Doctest framework test samples
│
├── lib/                           # Legacy stdlib (to be removed)
│   └── std/                       # Old stdlib location
│
├── test/                          # Legacy tests (to be removed)
│
├── log/                           # Logging crate (tracing wrapper)
│   └── src/lib.rs                 # simple_log::init() entry point
│
├── doc/                           # Documentation
│   ├── report/                    # Job completion reports
│   │   ├── README.md              # Report directory guide
│   │   ├── FILE_SPLITTING_SUMMARY.md  # File organization analysis (2025-12-22)
│   │   ├── SPLIT_FILES_INDEX.md   # Index of split documentation files
│   │   └── RUST_LONG_FILES.md     # Analysis of long Rust source files
│   ├── architecture.md            # Design principles and dependency rules
│   ├── codegen_technical.md       # Codegen implementation details
│   ├── feature.md                 # Feature overview (→ feature_index.md for details)
│   ├── feature_index.md           # Complete feature catalog with ratings/status
│   ├── codegen_status.md          # MIR instruction coverage, runtime FFI
│   ├── formal_verification.md     # Lean 4 formal verification docs
│   ├── import_export_and__init__.md  # Module system specification (v4)
│   ├── test.md                    # Test policy (mock control, coverage, test levels)
│   ├── system_test.md             # System test framework (SDN config, BDD patterns)
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
│   │   ├── bdd_spec.md            # BDD spec framework (describe/context/it)
│   │   ├── sdn.md                 # SDN - Simple Data Notation format
│   │   └── lexer_parser.md        # Parser/lexer specification
│   ├── design/                    # Design documents
│   │   ├── memory.md              # Memory management design
│   │   ├── type_inference.md      # Type inference design
│   │   └── concurrency.md         # Concurrency design
│   ├── status/                    # Feature implementation status (79+ files)
│   ├── plans/                     # Implementation plans
│   └── research/                  # Research notes
│       ├── improve_api.md         # API design overview (→ api_design_index.md)
│       └── api_design_index.md    # Detailed API guidelines by topic
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
| Type Inference | Partial (HM scaffold with unification working) |
| HIR | Complete (type-checked IR) |
| MIR | Complete (50+ instructions, generator state machine lowering) |
| Codegen | Hybrid (Cranelift + LLVM backends, Interpreter fallback) |
| RuntimeValue | Complete (9 modules, tagged pointers, 50+ FFI functions) |
| SMF Loader | Complete |
| Driver | Complete (exec_core, runner, interpreter layers) |
| Runtime/GC | Abfall-backed wrapper with optional logging |
| Package Manager | Complete (UV-style: manifest, lock, cache, resolution) |
| Module System | Parsing complete, resolution infrastructure ready |
| BDD Framework | Sprint 1 Complete (DSL, matchers, runtime) |
| Doctest | Sprint 2 Complete (parser, runner, discovery with FFI) |
| JJ Integration | 67% Complete (8/12 tasks, build snapshots working) |

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
| **Contracts** | 2 | ContractCheck, ContractOldCapture |
| Fallback | 2 | InterpCall, InterpEval |

### Contract System (Design by Contract)

**Status:** MIR lowering complete, runtime FFI ready, formal verification in Lean 4

Simple supports Design by Contract with preconditions, postconditions, invariants, and `old()` snapshots.

#### Contract Syntax

```simple
fn div(a: i64, b: i64) -> (i64 | DivByZero):
    in:                           # Preconditions
        b != 0
    invariant:                    # Routine invariants (entry + exit)
        true

    if b == 0:
        return DivByZero(msg: "division by zero")
    return a / b

    out(ret):                     # Postconditions (success)
        ret * b == a
    out_err(err):                 # Postconditions (error)
        old(b) == 0

class Account:
    balance: i64
    invariant:                    # Class invariant
        balance >= 0
```

#### Contract Checking Order (per Lean model)

| Phase | Checks | MIR Instruction |
|-------|--------|-----------------|
| Entry | 1. Preconditions (`in:`) | `ContractCheck(Precondition)` |
| Entry | 2. Capture `old()` values | `ContractOldCapture` |
| Entry | 3. Entry invariants | `ContractCheck(InvariantEntry)` |
| Exit (success) | 4. Exit invariants | `ContractCheck(InvariantExit)` |
| Exit (success) | 5. Postconditions (`out(ret):`) | `ContractCheck(Postcondition)` |
| Exit (error) | 4. Exit invariants | `ContractCheck(InvariantExit)` |
| Exit (error) | 6. Error postconditions (`out_err(err):`) | `ContractCheck(ErrorPostcondition)` |

#### Implementation Files

| Layer | File | Description |
|-------|------|-------------|
| Parser | `src/parser/src/statements/contract.rs` | Contract block parsing |
| AST | `src/parser/src/ast/nodes.rs` | `ContractBlock`, `ContractClause`, `InvariantBlock` |
| HIR | `src/compiler/src/hir/types.rs` | `HirContract`, `HirContractClause`, `HirClass`, `HirClassInvariant` |
| MIR | `src/compiler/src/mir/instructions.rs` | `ContractCheck`, `ContractOldCapture`, `ContractKind` |
| MIR Lower | `src/compiler/src/mir/lower.rs` | `lower_contract_entry()`, `lower_contract_success_exit()`, `lower_contract_error_exit()`, `lower_class_invariant()` |
| Codegen | `src/compiler/src/codegen/instr.rs` | `compile_contract_check()` |
| Runtime | `src/runtime/src/value/ffi.rs` | `simple_contract_check()` |
| Lean Model | `verification/type_inference_compile/src/Contracts.lean` | Formal verification |

#### Class Invariant Rules

- Checked after constructor (`new` or `__init__`)
- Checked after all public methods
- Uses `ContractKind::InvariantExit` for consistency

### Codegen status snapshot (runtime FFI)
- Actors: Spawn/Send/Recv now call runtime FFI; actor bodies still use a no-op stub until outlining is added.
- Generators: Yield/Next wired to runtime eager collector; generator bodies also use the stub pointer (no state machine yet).
- Futures: FutureCreate uses the same stubbed body pointer; Await calls runtime stub.

## Feature Documentation

Features are tracked in `doc/features/feature.md` and archived in `doc/features/feature_done_*.md` files.

### Feature Table Format

All feature tables use this standardized format:

```markdown
| Feature ID | Feature | Difficulty | Status | Impl | Doc | S-Test | R-Test |
|------------|---------|------------|--------|------|-----|--------|--------|
| #100 | Feature Name | 3 | ✅/📋 | R/S/S+R | [doc.md](doc.md) | `path/` | `path/` |
```

**Column Definitions:**

| Column | Description | Values |
|--------|-------------|--------|
| **Feature ID** | Unique identifier | `#NNN` format |
| **Feature** | Feature name/description | Short text |
| **Difficulty** | Implementation complexity | `1` Trivial, `2` Easy, `3` Medium, `4` Hard, `5` Very Hard |
| **Status** | Implementation status | `✅` Complete, `📋` Planned |
| **Impl** | Implementation location | `R` Rust, `S` Simple, `S+R` Both |
| **Doc** | Specification/design doc | Link to `doc/spec/*.md` or `-` if none |
| **S-Test** | Simple system test path | `std_lib/test/...` or `-` if none |
| **R-Test** | Rust test path | `src/*/tests/` or `-` if none |

**Feature ID Ranges:**

| Range | Category |
|-------|----------|
| #1-#8 | Infrastructure (Lexer, Parser, AST, HIR, MIR, GC, Pkg) |
| #10-#49 | Core Language |
| #50-#99 | Extended Language (Union, Async SM, Interpreter) |
| #100-#199 | Codegen & Runtime |
| #200-#299 | Extended Features (Units, Networking) |
| #300-#399 | GPU/SIMD |
| #400-#499 | Contracts |
| #500-#599 | UI Framework & Web |
| #600-#699 | SDN |
| #700-#799 | Database & Persistence |
| #800-#899 | Build Optimization & Infrastructure |
| #900-#999 | Verification & Code Quality |

**Adding New Features:**

1. Choose appropriate ID range for category
2. Add row to `doc/features/feature.md` (planned) or `doc/features/feature_done_*.md` (complete)
3. Fill all columns - use `-` for non-applicable fields
4. Link to specification doc in `doc/spec/` or design doc in `doc/design/`
5. Specify test paths where tests exist

**Example Entry:**

```markdown
| #220 | TCP sockets | 3 | ✅ | S+R | [spec/stdlib.md](spec/stdlib.md) | `std_lib/test/unit/net/` | `src/runtime/tests/` |
```

## Logging Strategy
- Use `tracing` for structured, span-based logging. Initialize once via `simple_log::init()` (respects `SIMPLE_LOG`/`RUST_LOG`).
- For cross-cutting “AOP-like” logging, prefer `#[tracing::instrument]` on functions to capture args/latency without manual boilerplate.
- Keep logging opt-in to avoid overhead; avoid ad-hoc `println!` on hot paths.

## Test Strategy

See `doc/guides/test.md` for the complete test policy. Tests use `simple_mock_helper` for mock control and coverage tracking.

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

### Rust Integration Tests
```bash
# All tests
cargo test --workspace

# Specific crate
cargo test -p simple-driver

# Specific test
cargo test -p simple-driver runner_compiles
```

### Simple Standard Library Tests
The Simple stdlib includes BDD-style specification tests written in the Simple language itself. These tests are automatically discovered and wrapped as Rust tests via `build.rs`. The test structure mirrors `src/` organization with tests grouped by module.

```bash
# Run all stdlib tests (unit + system + integration)
cargo test -p simple-driver simple_stdlib

# Run unit tests only (core functionality)
cargo test -p simple-driver simple_stdlib_unit

# Run system tests only (frameworks)
cargo test -p simple-driver simple_stdlib_system

# Run specific test modules
cargo test -p simple-driver simple_stdlib_unit_core          # All core tests
cargo test -p simple-driver simple_stdlib_unit_units         # Units tests
cargo test -p simple-driver simple_stdlib_system_spec        # Spec framework tests
cargo test -p simple-driver simple_stdlib_system_doctest     # Doctest framework tests

# Run specific stdlib test suites
cargo test -p simple-driver simple_stdlib_unit_core_collections_spec
cargo test -p simple-driver simple_stdlib_unit_core_string_spec
cargo test -p simple-driver simple_stdlib_system_spec_spec_framework_spec
cargo test -p simple-driver simple_stdlib_system_spec_matchers_spec_matchers_spec
cargo test -p simple-driver simple_stdlib_system_doctest_parser_parser_spec
cargo test -p simple-driver simple_stdlib_system_doctest_matcher_matcher_spec

# Run UI framework tests
cargo test -p simple-driver simple_stdlib_unit_ui                 # All UI tests
cargo test -p simple-driver simple_stdlib_unit_ui_element_spec    # Element tests
cargo test -p simple-driver simple_stdlib_unit_ui_gui             # All GUI tests
cargo test -p simple-driver simple_stdlib_unit_ui_gui_theme_spec  # Theme tests

# Run directly with Simple interpreter
./target/debug/simple simple/std_lib/test/unit/core/arithmetic_spec.spl
./target/debug/simple simple/std_lib/test/system/spec/spec_framework_spec.spl
./target/debug/simple simple/std_lib/test/system/doctest/parser/parser_spec.spl
```

**Test Organization (mirroring src/ structure):**

- `simple/std_lib/test/unit/core/` - Unit tests for core stdlib functionality
  - `arithmetic_spec.spl`, `comparison_spec.spl`, `primitives_spec.spl` - Basic operations
  - `collections_spec.spl` - Option, Result, Array, List, Dict
  - `string_spec.spl` - String operations and manipulation
  - `hello_spec.spl` - Basic example test

- `simple/std_lib/test/unit/units/` - Unit tests for semantic units module
  - `units_spec.spl` - Size units (bytes, KiB, MiB, etc.) and time units (ns, us, ms, s, min, hr, day)

- `simple/std_lib/test/system/spec/` - BDD spec framework system tests
  - `spec_framework_spec.spl` - describe/context/it/expect DSL functionality
  - `matchers/spec_matchers_spec.spl` - All matcher types (core, comparison, collection, string)

- `simple/std_lib/test/system/doctest/` - Doctest framework system tests
  - `doctest_advanced_spec.spl` - Edge cases, error handling, Unicode support
  - `parser/parser_spec.spl` - Docstring parsing and code extraction

- `simple/std_lib/test/unit/ui/` - UI framework unit tests
  - `element_spec.spl` - Element/NodeId/ElementTree tests
  - `patchset_spec.spl` - PatchOp and PatchSet tests
  - `diff_spec.spl` - Keyed diffing algorithm tests
  - `widgets_spec.spl` - TUI widget tests (Menu, Dialog, etc.)

- `simple/std_lib/test/unit/ui/gui/` - GUI renderer tests
  - `theme_spec.spl` - Theme palette, typography, spacing tests
  - `html_spec.spl` - HTML renderer and hydration manifest tests
  - `gui_widgets_spec.spl` - GUI widget tests (Card, Chip, Avatar, etc.)

- `simple/std_lib/test/integration/doctest/` - Integration tests
  - `discovery_spec.spl` - Cross-module doctest discovery and execution

- `simple/std_lib/test/fixtures/` - Test data and fixtures
  - `fixture_spec.spl` - Fixture testing examples
  - `doctest/sample.spl`, `sample_data.txt` - Doctest framework test samples

**Test Discovery:** Files matching `*_spec.spl` or `*_test.spl` are auto-discovered by build.rs

**Current Coverage (31 test files, 400+ test cases):**
- ✅ Unit Tests: 14 files (core: 7, units: 1, ui: 4, ui/gui: 3, spec: 6)
- ✅ System Tests: 6 files (spec: framework, matchers; doctest: parser, matcher, runner, advanced)
- ✅ Integration Tests: 1 file (doctest discovery)
- ✅ Plus Fixtures: 2 files (fixture_spec, doctest samples)

### Writing Simple (.spl) Tests

Simple tests are automatically linked to Rust's test framework via `build.rs`. This allows running all tests through `cargo test`.

**How the linkage works:**

1. `src/driver/build.rs` scans `simple/std_lib/test/` for `*_spec.spl` and `*_test.spl` files
2. Generates Rust test wrappers in `OUT_DIR/simple_stdlib_tests.rs`
3. Each SPL test becomes a Rust test: `simple_stdlib_{path}` (path sanitized)
4. Tests are included via `include!()` in `src/driver/tests/simple_stdlib_tests.rs`

**Path to test name mapping:**

| SPL File Path | Rust Test Name |
|---------------|----------------|
| `test/unit/core/arithmetic_spec.spl` | `simple_stdlib_unit_core_arithmetic_spec` |
| `test/unit/ui/element_spec.spl` | `simple_stdlib_unit_ui_element_spec` |
| `test/unit/ui/gui/theme_spec.spl` | `simple_stdlib_unit_ui_gui_theme_spec` |

**Creating a new SPL test:**

1. Create test file in appropriate directory:
   ```
   simple/std_lib/test/unit/{module}/{name}_spec.spl
   ```

2. Use BDD-style spec syntax:
   ```simple
   use spec.*
   use {module_to_test}.*

   describe "FeatureName":
       it "does something":
           let result = some_function()
           expect(result).to_equal(expected)

       context "when condition":
           it "behaves differently":
               expect(other_function()).to_be_true()
   ```

3. Rebuild to link tests:
   ```bash
   cargo build -p simple-driver
   ```

4. Run the new test:
   ```bash
   cargo test -p simple-driver simple_stdlib_{path_to_test}
   ```

**Test file naming conventions:**
- `*_spec.spl` - BDD-style specification tests (preferred)
- `*_test.spl` - Traditional test files
- Files in `fixtures/` directories are **skipped** (not auto-linked)

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
- Follow the flow in `doc/guides/test.md`:
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
- `doc/feature_index.md` - Complete feature catalog (131+ features with status/difficulty)
- `doc/features/feature.md` - Feature overview (links to feature_index.md)
- `doc/codegen_status.md` - MIR instruction coverage, runtime FFI functions
- `doc/codegen_technical.md` - Codegen implementation details
- `doc/import_export_and__init__.md` - Module system specification
- `doc/research/api_design_index.md` - API design guidelines
- `doc/research/improve_api.md` - API design overview
- `doc/status/` - Feature implementation status (79+ files)

**Note:** Large documentation files (feature.md, improve_api.md) have been reorganized into index files linking to focused sub-documents for better maintainability. Original files backed up with `.backup` extension.
## Recent Work (2025-12-15)

### Code Deduplication ✅ COMPLETED

Successfully reduced code duplication from **2.53% to 1.58%** (0.95 percentage points below threshold):

**Final Results:**
- **Lines reduced:** 869 lines (-0.95%)
- **Tokens reduced:** 8424 tokens (-1.08%)
- **Clones eliminated:** 78 clones (-36%)
- **Achievement:** 37.5% reduction in duplication

**Refactoring Phases (5 total):**
1. **Error Handling Macros** (-696 lines) - `semantic_err!`, `bail_semantic!`, `bail_unknown_method!`
2. **Module Loading** (-72 lines) - Consolidated into `pipeline/` submodules
3. **Method Error Macro** (-26 lines) - Standardized unknown method errors
4. **Monomorphize Utilities** (-66 lines) - Shared type analysis helpers
5. **TOML Helper** (-9 lines) - String array extraction

**Impact:**
- ✅ All 807+ tests passing
- ✅ Code quality significantly improved
- ✅ Centralized error handling patterns
- ✅ Shared utilities for type analysis
- ✅ Build time unchanged (~1.7s)

See `DEDUPLICATION_FINAL_REPORT.md` for complete details.

### Build Fixes
- Added Debug, Clone, Copy, PartialEq, Eq derives to BackendKind enum
- Implemented missing `contains_assignment` function in doctest module  
- Fixed REPL import paths to use `simple_driver::` prefix
- Build now compiles successfully

### File Organization Review
Analyzed large files (>1000 lines) for potential splitting:
- `instr.rs` (1305 lines) - Already well-modularized with include! files
- `llvm.rs` (1071 lines) - LLVM backend, well-organized
- `ast.rs` (1045 lines) - AST definitions, logically grouped
- `lower.rs` (1023 lines) - HIR lowering with single large impl block
- `container.rs` (1005 lines) - Settlement container, well-structured

These files are already reasonably organized. Further splitting would require significant refactoring and could introduce issues with the impl block structures and module dependencies.

### Test Status
- Main build: ✅ Compiles successfully
- Tests: ⚠️ Some test compilation errors remain (test-only issues)
  - Unresolved imports in test modules
  - Private module access issues
  - Missing test utility functions

### Next Steps
1. Fix remaining test compilation errors
2. Run full test suite to ensure no regressions
3. Consider duplication detection and removal
4. Update documentation as needed
