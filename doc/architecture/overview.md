# Architecture Overview

This document describes the architecture of the Simple Language Compiler.

## Index

This specification is split into multiple files:

| File | Content |
|------|---------|
| [architecture.md](architecture.md) | Overview, Structure, Dependencies |
| [architecture_modules.md](architecture_modules.md) | Module Details, Type/Struct Listing |
| [architecture_flows.md](architecture_flows.md) | Data Flow, Execution, Memory Management |
| [architecture_dev.md](architecture_dev.md) | Feature Guidance, Code Quality, Verification |
| [file_class_structure.md](file_class_structure.md) | **Comprehensive codebase inventory** (2,649 files, 623K lines, duplication analysis) |

---


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
- Minimize dependency fan-out: no "reach across" into unrelated modules to add a feature from `doc/features/feature.md`.
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

---

Next: [Module Details](architecture_modules.md)
