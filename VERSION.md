# Simple Language Version History

## Current Version: 0.3.0

---

## Versions

### 0.3.0 (2026-01-30)

**Bootstrap Complete** - The Simple compiler can now compile itself, and the default CLI is now the Simple-language implementation.

#### Key Achievements

**Bootstrap & Self-Compilation**
- Fixed critical Gen2 bootstrap bug (dictionary mutation in compiled mode)
- 3-stage verified bootstrap pipeline: `simple_runtime → simple_new1 → simple_new2 → simple_new3`
- Deterministic compilation verified: `simple_new2` and `simple_new3` are bitwise identical
- Root cause: Interpreter used value semantics, compiled mode used reference semantics
- Fix: Rewrote copy-modify-reassign patterns to direct nested field mutation

**Binary Architecture Refactoring**
- Renamed `simple_old` → `simple_runtime` (canonical name)
- `simple` (default CLI) now runs Simple implementation (`src/app/cli/main.spl`)
- New env var: `SIMPLE_RUNTIME_PATH` (preferred over `SIMPLE_OLD_PATH`)

**Stable Release Workflow**
- `make bootstrap-promote` — Promote verified compiler to `target/stable/`
- `bootstrap.sdn` — Track bootstrap metadata (hashes, revisions)
- `make bootstrap-from-stable` — Verify stable compiler reproducibility

#### Statistics
- Files modified: 11
- Lines changed: ~200
- Tests: 2254 passed (lib tests)
- Bootstrap stages: All 3 stages ✅
- Verification: `SHA256(simple_new2) == SHA256(simple_new3)` ✅

#### Deferred to v0.4.0
- Port more modules to Simple (loader, compiler, interpreter)
- Performance optimization (2-3x faster compilation, 30% less memory)
- LLM training/inference examples
- Architecture refactoring (remove duplication, layer separation)
- Fix pre-existing test failures

---

### 0.2.0 (2026-01-25)

**Standard Library Draft Complete** - First complete draft of the standard library with all core modules implemented and tested.

#### Standard Library (Draft Complete)
- **Core modules**: `Option`, `Result`, `String`, `List`, `Dict`, `Set`
- **Collections**: iterators, comprehensions, slicing
- **Concurrency**: channels, threads, async primitives
- **File I/O**: file operations, memory-mapped files
- **Networking**: TCP/UDP sockets
- **Resource management**: leak tracking, resource registry, cleanup protocols

#### Error/Warning Fixes
- All compiler errors resolved
- All compiler warnings fixed
- Doc-test failures corrected
- Clean build with zero warnings

#### Testing Infrastructure
- 631+ tests passing
- SSpec BDD framework complete
- Slow test separation (`slow_it`)
- Test run tracking and cleanup
- Auto-generated test reports

#### Documentation
- Auto-generated feature docs (`doc/feature/`)
- Test result reports (`doc/test/`)
- Build error tracking (`doc/build/`)
- Syntax quick reference guide

#### Language Features
- Pattern matching with exhaustiveness checking
- Optional chaining (`?.`) and null coalescing (`??`)
- Existence check (`.?`) operator
- Negative indexing and slicing
- String interpolation by default

#### Tooling
- Lint framework (75% complete)
- Memory leak finder app
- Resource cleanup validation

#### Technical Stats
- **Test count**: 631+ tests
- **Build status**: Clean (0 errors, 0 warnings)
- **Compiler**: Hybrid (Cranelift + Interpreter)

---

### 0.1.0 (2024-12)

Initial release with core language features and tooling.

#### Language Features
- Basic types: integers (i8-i64, u8-u64), floats (f32, f64), bool, str, nil
- Variables with `let`, `const`, and type inference
- Control flow: if/elif/else, for, while, loop, break, continue
- Functions with parameters and return types
- Structs (immutable by default) and classes (mutable by default)
- Enums with variants and pattern matching
- Arrays, dictionaries, and tuples
- Lambdas with `\x: expr` syntax
- String interpolation with `"Hello, {name}!"`
- Operators: arithmetic, comparison, logical, bitwise
- Indentation-based blocks (Python-like)
- Comments with `#`

#### Compiler & Runtime
- Tree-walking interpreter for compile-time evaluation
- SMF (Simple Module Format) binary generation
- x86-64 native code generation via Cranelift
- GC-managed memory with Abfall collector
- No-GC mode for manual memory management
- In-memory compilation and execution

#### CLI (`simple` command)
- Interactive REPL with history
- Run source files: `simple file.spl`
- Run compiled binaries: `simple file.smf`
- Run code strings: `simple -c "expr"`
- Compile command: `simple compile src.spl -o out.smf`
- Watch mode: `simple watch file.spl`
- GC options: `--gc-log`, `--gc=off`

#### Testing
- 1,200+ tests across unit, integration, and system levels
- Coverage tracking per test level
- Code duplication detection

#### Internationalization (i18n) Support

**Unified Diagnostics System**
- New `simple-diagnostics` crate providing i18n-aware error reporting
- Three output formatters: Text (colored terminal), JSON (machine-readable), Simple (specs)
- Builder pattern API for constructing diagnostics with localized messages
- Context helpers (`ctx1()`, `ctx2()`, `ctx3()`, `ContextBuilder`) for message interpolation

**Korean Language Support**
- Full Korean translations for all parser errors (E0001-E0012)
- Full Korean translations for all compiler errors (E1001-E3005)
- Localized severity names ("error" → "오류", "warning" → "경고")
- Formal polite tone (합니다체) for professional error messages

**I18n Infrastructure**
- Global i18n context with lazy-loaded message catalogs
- Automatic locale detection from environment variables (`LANG`, `SIMPLE_LANG`)
- Fallback chain: specific locale → language → English (e.g., ko_KR → ko → en)
- Simple language format (`.spl`) for message catalogs
- Template-based message interpolation with `{placeholder}` syntax

**CLI Integration**
- `--lang` flag to select output language: `simple build main.spl --lang ko`
- Environment variable support: `SIMPLE_LANG=ko simple build main.spl`
- Defaults to English if no language specified

**Error Catalogs**
- `i18n/__init__.spl` - English UI strings
- `i18n/__init__.ko.spl` - Korean UI strings
- `i18n/parser.spl` - English parser error messages (E0001-E0012)
- `i18n/compiler.spl` - English compiler error messages (E1001-E3005)
- `i18n/verification.spl` - English verification error messages (21 codes)
- `i18n/lint.spl` - English lint messages (8 codes)
- Plus Korean translations for all catalogs

**Technical Details**
- 66 tests covering i18n functionality (52 unit + 14 integration)
- ~4000+ lines of new code
- 64 error messages fully localized (parser, compiler, verification, lint)
- Zero performance impact - catalogs lazy-loaded once per process (~1ms)
- 100KB memory for English + Korean catalogs
- UTF-8 native - full Unicode support for all languages

---

## Planned Versions

### 0.4.0 (Target: Q2 2026)

**Goals:**
- 80%+ Simple Codebase — Move loader, compiler, interpreter to Simple
- Performance — 2-3x faster compilation, 30% less memory
- LLM training/inference examples with dimension checking
- Architecture refactoring — Remove duplication, enforce layer boundaries
- Stability — Fix pre-existing test failures, 100% pass rate

### 0.5.0 (Planned)

- Improved error messages with suggestions
- Enhanced standard library
- Performance optimizations

### 1.0.0 (Planned)

- Stable language specification
- Complete standard library
- Production-ready tooling
- Full documentation

---

## Version Numbering

Simple follows [Semantic Versioning](https://semver.org/):

- **MAJOR** (x.0.0): Breaking changes to language or APIs
- **MINOR** (0.x.0): New features, backward compatible
- **PATCH** (0.0.x): Bug fixes, backward compatible

Pre-1.0 versions may have breaking changes in minor releases.
