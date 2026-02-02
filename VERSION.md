# Simple Language Version History

## Current Version: 0.4.0

---

## Versions

### 0.4.0 (2026-02-02)

**Coverage Stability** - Focus on test coverage stability and build system maturity.

#### Goals
- Coverage stability and reliability
- Test pass rate improvements
- Build system refinements

---

### 0.3.0 (2026-01-30)

**Bootstrap Complete** - The Simple compiler can now compile itself, and the default CLI is now the Simple-language implementation.

#### Key Achievements

**Self-Hosting Build System**
- Complete build system written in Simple (~11,000 lines total)
- 8 phases: Foundation, Testing, Coverage, Quality, Bootstrap, Package, Migration, Advanced
- 4,440 lines of implementation, 2,370 lines of SSpec tests (290+ tests)
- Commands: `build`, `test`, `coverage`, `lint`, `fmt`, `check`, `bootstrap`, `package`, `watch`, `metrics`
- Replaces Makefile with type-safe Simple code

**Package Management System**
- Bootstrap package: minimal runtime-only installation (~6 MB)
- Full package: complete source distribution with binaries
- `simple package` CLI: build, install, uninstall, list, verify, upgrade
- Multi-platform: Linux x86_64, macOS ARM64/x86_64, Windows x86_64
- GitHub Actions automated release workflow with GHCR publishing

**Bootstrap & Self-Compilation**
- Fixed critical Gen2 bootstrap bug (dictionary mutation in compiled mode)
- 3-stage verified bootstrap pipeline: `simple_runtime → simple_new1 → simple_new2 → simple_new3`
- Deterministic compilation verified: `simple_new2` and `simple_new3` are bitwise identical

**Binary Optimization**
- Reduced runtime binary size from 508 MB to 22 MB (95.7% reduction)
- Bootstrap profile: 9.3 MB (76.8% reduction from release)
- UPX compression support: ~4.5 MB (88.8% total reduction)

**Binary Architecture Refactoring**
- Renamed `simple_old` → `simple_runtime` (canonical name)
- `simple` (default CLI) now runs Simple implementation (`src/app/cli/main.spl`)
- New env var: `SIMPLE_RUNTIME_PATH` (preferred over `SIMPLE_OLD_PATH`)

#### Statistics
- Build system: ~11,000 lines (impl + tests + docs)
- Tests: 2254 passed (lib tests), 290+ SSpec build system tests
- Bootstrap stages: All 3 stages verified
- Package sizes: Bootstrap ~6 MB, Full ~200-300 MB

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
