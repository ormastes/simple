# Simple Language Version History

## Current Version: 0.6.0

---

## Versions

### 0.6.0 (2026-02-14)

**Infrastructure & Performance Edition** - Advanced type system, SIMD optimization, baremetal support, and comprehensive testing infrastructure.

#### Key Achievements

**Advanced Type System**
- Hindley-Milner type inference implementation
- Union types, intersection types, refinement types
- Type variable unification and constraint solving
- Generic type instantiation and specialization
- Type error diagnostics with source locations

**SIMD Optimization**
- x86_64 AVX2 support (256-bit vectors, 4-8x speedup)
- ARM NEON support (128-bit vectors)
- Auto-vectorization for math operations
- Platform detection and fallback to scalar code
- SIMD intrinsics for array operations

**Baremetal Support**
- ARM Cortex-M startup code (ARMv7-M, ARMv8-M)
- x86_64 baremetal startup code (no OS dependencies)
- RISC-V RV32I/RV64I startup code
- 4 memory allocators: bump, freelist, buddy, slab
- Minimal footprint: 6-7 KB for basic programs
- Exception vectors and interrupt handlers

**Threading Infrastructure**
- Thread pool workers (Linux, macOS, Windows, FreeBSD)
- Thread SFFI layer (create, join, detach, yield)
- Atomic operations (load, store, CAS, fetch-add)
- Cross-platform thread primitives
- Producer-consumer patterns with work queues

**Documentation Coverage System**
- SDoctest integration for executable documentation
- Tag system: `@tag:api`, `@tag:internal`, `@tag:experimental`, `@tag:deprecated`
- Compiler warnings: `--warn-docs` flag for build-time checks
- Multiple output formats: Terminal, JSON, CSV, Markdown
- Configurable thresholds with exit codes
- Missing inline comment detection
- Group comment analysis

**Compiler Warning Systems**
- Closure capture warnings (nested function variable modification)
- Ignored return value warnings (discarded function results)
- Multiline boolean expression support (parentheses-based)
- Warning collection and reporting APIs
- 40+ tests covering all warning scenarios

**Platform Abstraction Library**
- Send/receive pattern for platform conversions (Go-inspired)
- PlatformConfig: arch, OS, endianness, newlines, pointer size
- Zero-cost same-platform conversions
- Auto-detection: `host_config()` detects current platform
- Type-safe platform-specific I/O
- WireWriter/WireReader serialization
- Newline mode translation (LF, CRLF, CR)

**Grammar Documentation**
- Core grammar specification (core_grammar.md)
- Full grammar with all extensions (full_grammar.md)
- Keyword reference with tier classification (keyword_reference.md)
- Seed grammar for bootstrap compiler (seed_grammar.md)
- Tree-sitter grammar status tracking (treesitter_status.md)
- Tier keywords SDN format (tier_keywords.sdn)

#### Test Suite Growth

**Statistics**
- 4,067 tests passing (100% pass rate)
- +976 new tests since v0.5.0 (3,091 → 4,067)
- Execution time: 17.4 seconds (4.3ms per test average)
- 5 core interpreter tests
- 5 platform library tests
- 4 package management tests
- 40+ compiler warning tests

**Test Runner Improvements**
- Fixed 8 timeout issues (120s → 4-6ms per test)
- Bootstrap rebuild activation (transitive imports)
- Import syntax corrections across test suite
- Result→tuple conversion for package management
- Zero test runner bugs (all issues were module-level)

#### Technical Stats
- Simple files: 1,200+
- Simple lines: 200,000+
- Tests: 4,067 passing (100%)
- Platforms: 7 (Linux, macOS, Windows, FreeBSD × x86_64/arm64)
- Rust source: 0 lines (pure Simple)

---

### 0.5.0 (2026-02-08)

**Pure Simple Release** - 100% self-hosting with Rust source completely removed. Major grammar updates, cross-platform CI, and production-ready infrastructure.

#### Key Achievements

**100% Pure Simple Architecture**
- Rust source code completely removed (24.2GB freed)
- Pre-built runtime binary (33MB) — no Rust toolchain needed
- 1,109+ Simple source files, 190,000+ lines
- Pure Simple parser (2,144 lines, fully self-hosting)

**Grammar Updates (3 Weeks)**
- Parser support for `async`, `await`, `spawn`, `actor`, `#[]` attributes
- `with` statement (context managers) — `enter()` + `cleanup()` protocol, LIFO cleanup
- Set literals `s{1, 2, 3}` — full compiler pipeline (Parser → HIR → MIR → Codegen)
- Async state machine generation and `Future<T>` type support in HIR
- Async/await error diagnostics integrated into HIR pipeline
- Desugaring pass integrated into compilation pipeline

**Cross-Platform CI & Release**
- All CI workflows rewritten for pure Simple (no Rust/cargo references)
- Multi-platform bootstrap loader with auto-detection (`bin/simple`)
- 7 platform packages: linux-x86_64, linux-aarch64, macos-x86_64, macos-arm64, windows-x86_64, windows-aarch64, freebsd-x86_64
- FreeBSD support via Linuxulator (Linux binary compatibility)
- `-c` flag uses temp file approach for full module resolution
- Direct `.spl`/`.smf` file execution bypass

**Test Suite**
- 100% pass rate on all active tests
- 3,606/4,379 broad lib tests passing (82%)
- 458 spec files, 324 fully passing
- Test suite repair infrastructure (bulk syntax fixes across 54+ files)
- SDoctest system complete — documentation testing (669 files, 4,963 blocks)

**Production Infrastructure**
- Unified Database Library — production-ready (98/115 tests, 85.2%)
- MCP Server — JSON-RPC 2.0 with pagination, structured output, roots
- Stdlib SFFI — 5 phases complete (String, Collections, Math, System, Path)
- Static method desugaring — `impl Type: static fn` → `Type__method()` rewriting
- Script migration — 25/25 Python/Bash scripts migrated to Simple

**Developer Experience**
- Self-hosting build system (8 phases, 4,440 lines, 290+ tests)
- SSpec BDD framework with skip/pending/mode-aware decorators
- Import system analysis and documentation
- File I/O protection (heredoc-based shell-safe writes)
- Runtime fault detection stubs

#### Statistics
- Simple files: 1,109+
- Simple lines: 190,000+
- Tests: 3,606+ passing (broad suite)
- Platforms: 7 (Linux, macOS, Windows, FreeBSD × x86_64/arm64)
- Rust source: 0 lines (removed)

---

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

### 0.7.0 (Planned) - Deep Learning Edition

- Deep learning examples and library improvements
- Fix `lib.pure.*` module resolution for interpreter
- GPU acceleration via SFFI (PyTorch/CUDA backend)
- Model serialization/deserialization
- Training loop utilities
- Comprehensive DL examples (XOR, regression, iris, MNIST)

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
