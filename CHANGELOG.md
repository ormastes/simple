# Changelog

All notable changes to the Simple compiler will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [0.3.0] - Planned

### Goals

#### Performance Improvements
- JIT compilation optimization for hot paths
- Reduced interpreter overhead
- Memory allocation optimization
- Faster startup time

#### All Simple Executables
- Rewrite all internal tools in Simple language
- `simple fmt` - formatter written in Simple
- `simple lint` - linter written in Simple
- `simple test` - test runner written in Simple
- Self-hosting milestone

#### Migrate Rust to Simple
- Gradual migration of compiler components
- Parser rewrite in Simple (bootstrap phase)
- Type checker in Simple
- Reduce Rust dependency

#### LLM Interface Enhancement
- Improved context pack generation
- Better IR export for LLM analysis
- Enhanced lint suggestions for AI-assisted coding
- Structured output for IDE integration

---

## [0.2.0] - 2026-01-25

### Summary

**Standard Library Draft Complete** - First complete draft of the standard library with all core modules implemented and tested.

### Completed

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

### Technical Stats
- **Test count**: 631+ tests
- **Build status**: Clean (0 errors, 0 warnings)
- **Compiler**: Hybrid (Cranelift + Interpreter)

---

## [0.1.0] - Previous

### Added

#### Internationalization (i18n) Support

- **Unified Diagnostics System** (`src/diagnostics/`)
  - New `simple-diagnostics` crate providing i18n-aware error reporting
  - Three output formatters: Text (colored terminal), JSON (machine-readable), Simple (specs)
  - Builder pattern API for constructing diagnostics with localized messages
  - Context helpers (`ctx1()`, `ctx2()`, `ctx3()`, `ContextBuilder`) for message interpolation

- **Korean Language Support**
  - Full Korean translations for all parser errors (E0001-E0012)
  - Full Korean translations for all compiler errors (E1001-E3005)
  - Localized severity names ("error" → "오류", "warning" → "경고")
  - Formal polite tone (합니다체) for professional error messages

- **I18n Infrastructure** (`src/i18n/`)
  - Global i18n context with lazy-loaded message catalogs
  - Automatic locale detection from environment variables (`LANG`, `SIMPLE_LANG`)
  - Fallback chain: specific locale → language → English (e.g., ko_KR → ko → en)
  - Simple language format (`.spl`) for message catalogs
  - Template-based message interpolation with `{placeholder}` syntax

- **CLI Integration**
  - `--lang` flag to select output language: `simple build main.spl --lang ko`
  - Environment variable support: `SIMPLE_LANG=ko simple build main.spl`
  - Defaults to English if no language specified

- **Error Catalogs**
  - `i18n/__init__.spl` - English UI strings (severity names)
  - `i18n/__init__.ko.spl` - Korean UI strings
  - `i18n/parser.spl` - English parser error messages (E0001-E0012)
  - `i18n/parser.ko.spl` - Korean parser error messages
  - `i18n/compiler.spl` - English compiler error messages (E1001-E3005)
  - `i18n/compiler.ko.spl` - Korean compiler error messages
  - `i18n/verification.spl` - English verification error messages (21 codes)
  - `i18n/verification.ko.spl` - Korean verification error messages
  - `i18n/lint.spl` - English lint messages (8 codes)
  - `i18n/lint.ko.spl` - Korean lint messages

- **Documentation**
  - User guide: `doc/guide/i18n.md` - How to use `--lang` flag
  - Contributor guide: `doc/contributing/i18n.md` - How to add translations
  - Catalog documentation: `i18n/README.md` - Message format specification
  - Architecture guide: `src/diagnostics/ARCHITECTURE.md` - System design
  - Usage examples: `src/diagnostics/USAGE.md` - API usage patterns

- **Diagnostic Conversion Layer** (`src/driver/src/diagnostics_conversion.rs`)
  - Converts parser diagnostics to i18n-aware diagnostics
  - Extracts context from error messages for proper localization
  - Maintains backward compatibility with existing error reporting

### Changed

- **Feature Flags**
  - `simple_i18n` now has optional `simple-format` feature for catalog parsing
  - Prevents circular dependency between parser, diagnostics, and i18n

- **Error Reporting Architecture**
  - Parser continues using lightweight `simple-common::Diagnostic`
  - Driver converts to `simple-diagnostics::Diagnostic` with i18n support
  - Layered architecture prevents circular dependencies

### Technical Details

- **66 tests** covering i18n functionality (52 unit + 14 integration)
- **~4000+ lines** of new code
- **25 files** created/modified
- **64 error messages** fully localized (parser, compiler, verification, lint)
- **Zero performance impact** - catalogs lazy-loaded once per process (~1ms)
- **100KB memory** for English + Korean catalogs
- **UTF-8 native** - full Unicode support for all languages

### Korean Language Considerations

- Sentence structure adapted for SOV (Subject-Object-Verb) word order
- Neutral particle forms used: "을(를)", "이(가)"
- Future enhancement planned: dynamic particle selection based on final consonant (받침)
- All technical terms consistently translated or transliterated

### Migration Path

- Old diagnostic API (`Diagnostic::error("msg")`) continues to work unchanged
- New i18n API (`Diagnostic::error_i18n("domain", "code", &ctx)`) for localized messages
- Gradual migration: parser errors completed, compiler integration pending
- Full backward compatibility maintained

### Future Enhancements

Planned for future releases:
- Additional languages: Japanese, Chinese (Simplified/Traditional), Spanish, French
- Improved Korean particle selection algorithm
- Translation coverage metrics and validation
- LSP integration for translated hover messages
- CLDR plural rules for all languages

## References

- Design based on Rust compiler's i18n effort, avoiding Fluent complexity
- See `src/diagnostics/ARCHITECTURE.md` for design decisions
- See `doc/contributing/i18n.md` for translation guidelines
