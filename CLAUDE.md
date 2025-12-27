# Simple Language Compiler - Development Guide

**Key Features:**
- **LLM-Friendly**: IR export, context packs, lint framework (15/40 implemented, 28/40 specified, 70% effective completion)
- **Pattern Matching Safety**: Exhaustiveness checking, unreachable detection, strong enums (5/5 complete)
- Memory model: Reference capabilities (`mut T`, `iso T`, `T`), concurrency modes (`actor`, `lock_base`, `unsafe`)
- SC-DRF guarantee: Formally verified memory consistency model
- Formatter/linter: Simple-based tools in `simple/app/`
- AOP & Unified Predicates: Compile-time weaving, architecture rules (19/51 features, 611 tests)
- See `doc/architecture/memory_model_implementation.md`
- use jj version contoll rather git.

## Implementing Applications in Simple Language

**YES - Applications can and should be implemented in Simple!**

Simple language is designed to be self-hosting and practical for real-world applications. The compiler itself includes an interpreter that can execute Simple code, and the language has full support for:


**How to Create a Simple Application:**

1. **Create your application structure:**
   ```bash
   mkdir my_app
   cd my_app
   # Create main.spl
   ```

2. **Write your Simple code:**
   ```simple
   # main.spl
   import std.io
   import std.args

   fn main():
       args = args.get_args()
       if args.len() > 1:
           io.println("Hello, " + args[1] + "!")
       else:
           io.println("Hello, World!")
   ```

3. **Run with interpreter:**
   ```bash
   ./target/debug/simple main.spl arg1 arg2
   ```

4. **Build to executable (when AOT ready):**
   ```bash
   ./target/debug/simple --compile main.spl -o my_app
   ./my_app arg1 arg2
   ```

**Example Applications:**
- See `simple/app/formatter/` - Complete formatter in 166 lines
- See `simple/app/lint/` - Full linter with 14 rules in 262 lines
- See `simple/std_lib/test/` - 31 test files demonstrating language features

**Best Practices:**
- Use the standard library (`simple/std_lib/src/`) for common operations
- Write BDD tests alongside your code (`*_spec.spl`)
- Follow the module structure: `__init__.spl` for packages
- Use contracts for critical functions (`in:`, `out:`, `invariant:`)
- Leverage AOP for cross-cutting concerns (logging, metrics, validation)

See `simple/app/README.md` for complete details. 

## Bug Reports & Improvement Requests

When working with Simple standard library or applications and you discover bugs or potential improvements:

**Bug Reports:** File in `simple/bug_report.md`
- Compiler/interpreter bugs
- Standard library issues
- Runtime errors or crashes
- Incorrect behavior in self-hosted tools

**Improvement Requests:** File in `simple/improve_request.md`
- API design suggestions
- Performance optimization ideas
- Missing stdlib functionality
- Developer experience improvements
- New language features

**Format:**
```markdown
### [Component] Brief description

**Type:** Bug | Improvement
**Priority:** High | Medium | Low
**Discovered:** YYYY-MM-DD

**Description:**
[Detailed explanation]

**Expected:**
[What should happen]

**Actual:**
[What actually happens]

**Reproduction:**
[Steps to reproduce or code example]
```

## Documentation Organization

### Report Directory (`doc/report/`)

**Purpose:** Store job completion reports, session summaries, and maintenance documentation. Make any docuement which user not specifically requested documents on doc/report/ directory.

**When to Use:**
- ✅ **After completing a significant feature or task** - Create a completion report documenting what was done
- ✅ **Session summaries** - Document work completed in a development session
- ✅ **Maintenance activities** - File organization, refactoring, code quality improvements
- ✅ **Implementation summaries** - Technical details of how features were implemented

**How to Report:**
1. Create a descriptive markdown file in `doc/report/` (e.g., `CONTRACTS_PHASE_2_2025-12-23.md`)
2. Include: date, summary, features completed, files modified, test results, next steps
3. Update `doc/report/README.md` with a link to your report
4. Reference from `CLAUDE.md` if relevant for future AI agent context

**Examples:**

See `doc/report/README.md` for full details and guidelines.

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
│   ├── app/                       # Simple-language applications (self-hosted tools)
│   │   ├── formatter/             # Canonical formatter (main.spl) ✅
│   │   ├── lint/                  # Semantic linter (main.spl) ✅
│   │   ├── lsp/                   # Language server (main.spl) 🔄
│   │   ├── dap/                   # Debug adapter (main.spl) 🔄
│   │   └── README.md              # Application documentation
│   ├── bin_simple/                # Compiled Simple executables
│   │   ├── simple_fmt             # Formatter binary ✅
│   │   ├── simple_lint            # Linter binary ✅
│   │   ├── simple_lsp             # LSP server binary 🔄
│   │   └── simple_dap             # DAP server binary 🔄
│   ├── build/                     # Intermediate build files
│   │   ├── formatter/             # Formatter .smf files
│   │   ├── lint/                  # Linter .smf files
│   │   ├── lsp/                   # LSP .smf files 🔄
│   │   └── dap/                   # DAP .smf files 🔄
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
│   ├── architecture/README.md     # Design principles and dependency rules
│   ├── codegen_technical.md       # Codegen implementation details
│   ├── feature.md                 # Feature catalog
│   ├── feature_index.md           # Feature index with links
│   ├── codegen/status.md          # MIR instruction coverage, runtime FFI
│   ├── formal_verification.md     # Lean 4 formal verification docs
│   ├── import_export_and__init__.md  # Module system specification (v4)
│   ├── test.md                    # Test policy (mock control, coverage, test levels)
│   ├── system_test.md             # System test framework (SDN config, BDD patterns)
│   ├── spec/                      # Language specifications (53 specs total)
│   │   ├── README.md              # Main specification index and navigation
│   │   ├── language.md            # Spec index with quick reference (legacy)
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
│   │   ├── sandboxing.md          # Runtime & environment isolation (#916-923)
│   │   ├── sdn.md                 # SDN - Simple Data Notation format
│   │   ├── lexer_parser.md        # Parser/lexer specification
│   │   ├── gpu_simd/              # GPU & SIMD specifications
│   │   │   └── README.md          # GPU compute, SIMD overview
│   │   ├── graphics_3d/           # 3D Graphics specifications
│   │   │   └── README.md          # 3D rendering overview
│   │   ├── parser/                # Parser implementation specs
│   │   │   └── overview.md        # Parser architecture
│   │   ├── testing/               # Testing framework specifications (6 files)
│   │   │   ├── testing_bdd_framework.md  # BDD testing, matchers, Gherkin
│   │   │   ├── sdoctest.md        # Documentation testing
│   │   │   ├── mock.md            # Test doubles and mocking
│   │   │   ├── property_testing.md  # Property-based testing
│   │   │   ├── snapshot_testing.md  # Snapshot regression testing
│   │   │   └── semantic_diff.md   # Semantic code comparison
│   │   └── tooling/               # Development tool specifications (5 files)
│   │       ├── formatter.md       # Code formatting
│   │       ├── formatting_lints.md  # Linter rules
│   │       ├── build_audit.md     # Build auditing
│   │       ├── vscode_extension.md  # VSCode support
│   │       └── basic_mcp.md       # Model Context Protocol
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
│   ├── type_inference_compile/    # Type inference model
│   ├── memory_capabilities/       # Reference capability verification (#1104)
│   └── memory_model_drf/          # SC-DRF memory model verification (#1105-1106)
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

### Contract System

**Status:** MIR lowering complete, runtime FFI ready, Lean 4 verified

Supports `in:`, `out(ret):`, `out_err(err):`, `invariant:`, and `old()`. Checks: preconditions → capture old → entry invariants → (function) → exit invariants → postconditions. Class invariants checked after constructors and public methods.

### Codegen status snapshot (runtime FFI)
- Actors: Spawn/Send/Recv now call runtime FFI; actor bodies still use a no-op stub until outlining is added.
- Generators: Yield/Next wired to runtime eager collector; generator bodies also use the stub pointer (no state machine yet).
- Futures: FutureCreate uses the same stubbed body pointer; Await calls runtime stub.

## Feature Documentation

Tracked in `doc/features/feature.md` with archived features in `doc/features/done/feature_done_*.md`. Format: Feature ID (#NNN by category), Difficulty (1-5), Status (✅/📋), Impl (R/S/S+R), Doc, Tests.

**ID Ranges:** #1-8 Infrastructure, #10-49 Core, #50-99 Extended, #100-199 Codegen, #200-299 Extended Features, #300-399 GPU/SIMD, #400-499 Contracts, #500-599 UI/Web, #600-699 SDN, #700-799 DB, #800-899 Build, #900-999 Verification.

## Test Strategy

See `doc/guides/test.md`. Tests use `simple_mock_helper` for mock control and coverage tracking.

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

Each test binary uses `#[ctor::ctor]` with `init_unit_tests!("crate_name")` and `validate_test_config()`.

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
BDD-style tests written in Simple, auto-discovered by `build.rs` and wrapped as Rust tests.

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

**Test Organization:** Mirrors `src/` structure - `unit/`, `system/`, `integration/`, `fixtures/`

**Coverage:** 31 test files, 400+ test cases (14 unit, 6 system, 1 integration, 2 fixtures)

### Writing Simple (.spl) Tests

SPL tests auto-link to Rust via `build.rs`. Files matching `*_spec.spl`/`*_test.spl` → `simple_stdlib_{path}` test names.

Create in `simple/std_lib/test/{unit|system|integration}/`, use BDD syntax, rebuild with `cargo build -p simple-driver`.

## Code Quality Tools

### Quick Commands (Makefile)

```bash
make check             # fmt + lint + test (before commit)
make check-full        # All checks + coverage + duplication
make help              # Show all available targets
```

### Test Coverage

Uses `cargo-llvm-cov`. All targets: 100% coverage.

```bash
make coverage-unit/it/system/env  # Per-level reports
make coverage                      # HTML → target/coverage/html/index.html
make coverage-all                  # All reports
```

Install: `cargo install cargo-llvm-cov`

### Code Duplication Detection

Uses `jscpd` (threshold: 2%, minLines: 5, minTokens: 50).

```bash
make duplication        # Report → target/duplication/
jscpd ./src             # Direct run
```

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

## Logging Strategy
- Use `tracing` with `simple_log::init()` (respects `SIMPLE_LOG`/`RUST_LOG`)
- Prefer `#[tracing::instrument]` for cross-cutting logging
- Keep opt-in to avoid overhead on hot paths

## System Tests (CLI/TUI)
Use `shadow-terminal` for PTY simulation. Create temp dirs, spawn CLI, assert exit codes/artifacts. No network, no mocks (`init_system_tests!()`). See `doc/guides/test.md`.

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

## Postponed Jobs & Features

### Planned Features (by Priority)

**High Priority:**
1. LLM-Friendly Features (#880-919) - 40 features planned
2. Test Framework Completion - BDD + Doctest finishing
3. Language Server (LSP) - Editor support

**Medium Priority:**
4. Test CLI Integration (#302) - Unified `simple test`
5. Convention Documentation
6. TUI Framework
7. Package Registry (crates.io-style)

**Low Priority:**
8. Web Framework (Rails-style)
9. GUI Framework (Native/Immediate Mode)
10. Debugger (DAP)

### Deferred/Postponed

**Blocked:**
- Test state storage (JJ integration - needs test framework)
- Doctest CLI/interpreter (needs infrastructure)
- Generator JIT codegen (needs block layout)

**Deferred:**
- GPU backends (WGPU, Metal)
- 32-bit architecture support (needs LLVM)
- Unit conversion methods

See `TODO.md` and `doc/features/done/feature_done_*.md` for archived features.

