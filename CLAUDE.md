# Simple Language Compiler - Development Guide

## Current File Structure

```
simple/
├── Cargo.toml                     # Workspace definition
├── Makefile                       # Build automation (test, coverage, lint, etc.)
├── .jscpd.json                    # Code duplication detection config
├── CLAUDE.md                      # This file - development guide
├── public_api.yml                 # Public API definitions for coverage
│
├── doc/                           # Documentation
│   ├── architecture.md            # Design principles and dependency rules
│   ├── feature.md                 # Feature list with importance/difficulty ratings
│   ├── formal_verification.md     # Lean 4 formal verification docs
│   ├── test.md                    # Test policy (mock control, coverage, test levels)
│   ├── spec/                      # Language specifications
│   │   ├── language.md            # Language specification
│   │   └── lexer_parser.md        # Parser/lexer specification
│   ├── design/                    # Design documents
│   │   ├── memory.md              # Memory management design
│   │   ├── type_inference.md      # Type inference design
│   │   └── concurrency.md         # Concurrency design
│   ├── status/                    # Feature implementation status
│   ├── plans/                     # Implementation plans
│   └── research/                  # Research notes
│
├── verification/                  # Lean 4 formal verification projects
│   ├── manual_pointer_borrow/     # Borrow checker model
│   ├── gc_manual_borrow/          # GC safety model
│   ├── async_compile/          # Effect tracking model
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
    │       ├── lexer.rs           # 943 lines - tokenization
    │       ├── parser.rs          # 1747 lines - recursive descent
    │       ├── ast.rs             # 389 lines - AST nodes
    │       └── token.rs           # 170 lines - token types
    │
    ├── type/                      # Type checker/inference (HM scaffold)
    │   └── src/lib.rs             # Unification, generalize/instantiate, core expr inference
    │
    ├── compiler/                  # HIR, MIR, Codegen (depends: parser, common, runtime)
    │   └── src/
    │       ├── lib.rs             # Compilation entry point
    │       ├── hir/               # High-level IR
    │       │   ├── mod.rs
    │       │   ├── types.rs       # Type system
    │       │   └── lower.rs       # AST → HIR lowering
    │       ├── mir/               # Mid-level IR
    │       │   ├── mod.rs
    │       │   ├── types.rs       # 50+ MIR instructions, effects, patterns
    │       │   └── lower.rs       # HIR → MIR lowering
    │       ├── codegen/
    │       │   ├── mod.rs
    │       │   ├── cranelift.rs   # AOT Cranelift backend
    │       │   └── jit.rs         # JIT Cranelift backend
    │       ├── value_bridge.rs    # FFI value marshalling (BridgeValue)
    │       ├── interpreter_ffi.rs # Interpreter FFI for hybrid execution
    │       └── compilability.rs   # Compilability analysis
    │
    ├── loader/                    # SMF binary loader (depends: common)
    │   └── src/
    │       ├── lib.rs
    │       └── loader.rs          # SMF format handling
    │
    ├── native_loader/             # OS dylib loader (depends: common)
    │   └── src/lib.rs
    │
    ├── lib/                       # Native stdlib (depends: native_loader)
    │   └── src/
    │       └── term.rs            # Terminal I/O
    │
    ├── log/                       # Tracing/log init (structured logging)
    │   └── src/lib.rs             # simple_log::init(); tracing subscriber setup
    │
    ├── runtime/                   # GC, concurrency, and runtime values
    │   └── src/
    │       ├── lib.rs             # Re-exports
    │       ├── value.rs           # RuntimeValue (tagged pointers, collection FFI)
    │       ├── memory/
    │       │   ├── gc.rs          # GcRuntime + logging hooks
    │       │   └── no_gc.rs       # NoGcAllocator
    │       └── concurrency/
    │           └── mod.rs         # Actor scheduler
    │
    └── driver/                    # CLI runner (depends: all)
        └── src/
            ├── lib.rs
            ├── runner.rs          # Compile and execute
            ├── watcher.rs         # File watching
            ├── main.rs            # CLI entry (run, --gc-log)
            └── tests/
                ├── runner_tests.rs
                └── watcher_tests.rs
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
| Parser | Complete |
| AST | Complete |
| HIR | Complete (type-checked IR) |
| MIR | Complete (50+ instructions) |
| Codegen | Hybrid (Cranelift + Interpreter fallback) |
| RuntimeValue | Complete (tagged pointers, collection FFI) |
| SMF Loader | Complete |
| Driver | Complete |
| Runtime/GC | Abfall-backed wrapper with optional logging (requires Rust 1.90+) |

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

## Current Feature: Integer Literals (#1)

**Goal**: Make `main = 42` return 42 instead of always 0.

### What Works Now
```rust
// This test passes but is wrong - compiler ignores source
runner.run_source("main = 0").expect("run ok");  // Returns 0
runner.run_source("main = 42").expect("run ok"); // Also returns 0!
```

### What We're Implementing
```rust
// After implementation:
assert_eq!(runner.run_source("main = 42")?, 42);
assert_eq!(runner.run_source("main = 0")?, 0);
assert_eq!(runner.run_source("main = -1")?, -1);  // Future
```

### Implementation Plan

1. **System Test** (runner_tests.rs)
   - `runner.run_source("main = 42")` should return 42

2. **HIR Lowering** (hir/mod.rs)
   - Parse AST integer literal → HIR integer constant
   - Track integer type (i32 for now)

3. **Cranelift Codegen** (codegen/cranelift.rs)
   - Generate `iconst` instruction
   - Return value from main function

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

## Key Files for Current Work

- `src/compiler/src/lib.rs` - Entry point, needs to actually compile
- `src/compiler/src/hir/mod.rs` - AST → HIR lowering
- `src/compiler/src/codegen/cranelift.rs` - HIR → machine code
- `src/driver/tests/runner_tests.rs` - System tests
