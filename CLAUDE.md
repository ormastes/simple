# Simple Language Compiler - Development Guide

## Current File Structure

```
simple/
├── Cargo.toml                     # Workspace definition
├── Makefile                       # Build automation (test, coverage, lint, etc.)
├── .jscpd.json                    # Code duplication detection config
├── feature.md                     # Feature list with importance/difficulty ratings
├── architecture.md                # Design principles and dependency rules
├── simple_language_spec.md        # Language specification
├── simple_lexer_parser_spec.md    # Parser/lexer specification
├── test.md                        # Test policy (mock control, coverage, test levels)
├── status/                        # Feature implementation status tracking
│   ├── basic_types_integer_literals.md
│   ├── operators_arithmetic.md
│   ├── variables_let_bindings.md
│   ├── config_env.md
│   └── code_quality_tools.md
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
    ├── compiler/                  # HIR, MIR, Codegen (depends: parser, common)
    │   └── src/
    │       ├── lib.rs             # Compilation entry point
    │       ├── hir/               # High-level IR
    │       │   ├── mod.rs
    │       │   └── types.rs       # Type system
    │       ├── mir/               # Mid-level IR
    │       └── codegen/
    │           └── cranelift.rs   # Cranelift backend
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
    ├── runtime/                   # GC wrapper (depends: abfall)
    │   └── src/
    │       └── gc/mod.rs          # GcRuntime + logging hooks
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
   │   HIR   │  → Type-checked IR (TODO)
   └────┬────┘
        │
        ▼
   ┌─────────┐
   │   MIR   │  → Simplified IR (TODO)
   └────┬────┘
        │
        ▼
   ┌──────────┐
   │ Cranelift │  → Machine code
   └────┬─────┘
        │
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
| HIR | Stub |
| MIR | Stub |
| Codegen | Stub (returns 0 always) |
| SMF Loader | Complete |
| Driver | Complete |
| Runtime/GC | Abfall-backed wrapper with optional logging (requires Rust 1.90+) |

## Logging Strategy
- Use `tracing` for structured, span-based logging. Initialize once via `simple_log::init()` (respects `SIMPLE_LOG`/`RUST_LOG`).
- For cross-cutting “AOP-like” logging, prefer `#[tracing::instrument]` on functions to capture args/latency without manual boilerplate.
- Keep logging opt-in to avoid overhead; avoid ad-hoc `println!` on hot paths.

## Test Strategy

See `test.md` for the complete test policy. Tests use `simple_mock_helper` for mock control and coverage tracking.

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
- Follow the flow in `test.md`:
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
