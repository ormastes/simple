# Changelog

All notable changes to Simple Language will be documented in this file.

## [0.7.0] - 2026-02-24

### Added
- Type system Wave 2: flow narrowing (M2), associated types (M3), effect system (M4)
- Bitfield feature — hardware register definitions with zero-overhead bit manipulation
- Pass keyword variants: `pass_do_nothing`, `pass_dn` (intentional no-ops with semantic meaning)
- Binary architecture documentation (temporal C bootstrap vs real Simple binary)
- C bootstrap preprocessing for pass keywords and bitfield syntax compatibility

### Changed
- `build/bootstrap/c_simple/` established as canonical bootstrap location
- `src/compiler_cpp/` documented as temporal bootstrap (generated C from Simple source)
- Bootstrap pipeline docs updated with temporal vs real binary distinction

### Fixed
- Corrupted pass_variants_spec.spl test file (keywords replaced with `0`)
- Module loader crash bugs + memory efficiency improvements
- Heap-allocation leaks in MIR C codegen
- C backend `simple_int_to_str` type mismatch for string backend field

### Infrastructure
- Bootstrap binary updated to v0.7.0 with pass keyword and bitfield support
- `bin/release/simple` updated as current release binary

## [0.6.1] - 2026-02-23

### Added
- Async I/O driver infrastructure with platform backends (epoll, io_uring, kqueue, IOCP)
- Sanitizer CI workflow (ASan builds)
- Valgrind check script
- Optimized build script

### Changed
- Mass test suite repair: +831 passing test cases across all suites
- MIR codegen trait unification (C/LLVM shared trait)
- All stale version references updated from 0.5.0 to 0.6.1

### Fixed
- Memory leak elimination across all 9 categories (slice, substr, lex args, program args, etc.)
- C backend string escaping and C++ keyword safety
- Runtime intrinsics for codegen
- Test runner binary resolution
- Parse errors in test files

### Infrastructure
- Bootstrap build updated to use v0.6.0 as base
- 11-platform release matrix (added FreeBSD x86, Windows x86, Windows ARM64)

## [0.6.0] - 2026-02-14

### Added
- Grammar documentation system with tier-based keyword tracking
- Thread pool worker implementation complete (100% coverage)
- Threading integration with startup/bootstrap systems
- Windows build system with MinGW and ClangCL toolchains
- Module loading investigation and fixes
- File stat implementation for runtime (rt_file_stat)
- Grammar specification files (core, full, seed, tier keywords)
- Tree-sitter grammar status documentation
- Comprehensive test coverage (4067/4067 tests passing - 100%)

### Changed
- Bootstrap workflow now uses v0.5.0 release for reproducible builds
- Release workflow enhanced with automatic runtime building
- Test coverage improved from 3916 to 4067 tests (+151 tests)
- Platform library integration verified with zero regressions
- Documentation coverage system marked production ready

### Fixed
- 8 timeout issues in test suite (all resolved)
- Module-level import and closure issues
- Bootstrap rebuild activating transitive imports
- Package management Result→tuple conversion
- Platform detection and newline handling

### Documentation
- 10+ comprehensive status reports added
- Grammar reference documentation complete
- Windows build guides (quick start + detailed)
- Threading implementation documentation
- Bootstrap status and progress tracking
- Implementation completion report (92% core features)

### Infrastructure
- GitHub Actions workflow updated for 0.6.0 release
- Multi-platform bootstrap packages (7 platforms)
- Automated testing with downloaded v0.5.0 bootstrap
- Release artifact creation and publishing to GHCR

### Test Suite
- **100% pass rate**: 4067/4067 tests passing
- Platform abstraction: 80/80 tests (100%)
- Package management: All tests fixed and passing
- Effect system: Production ready
- Parser error recovery: Comprehensive coverage
- Zero test regressions

## [0.5.1-rc.1] - 2026-02-11

### Added
- Async/await parser implementation (Phases 1-7 infrastructure complete)
- VHDL backend with verification constraints and tests
- VHDL examples, golden files, CI integration, and user guide
- Test enablement progress tracking documentation
- Expression slice evaluation support in interpreter (Phase 1.1 partial)

### Changed
- MCP server enhanced for production readiness with robustness improvements
- Generic template tests enabled (5 tests - Phase 1.3 validation)
- Deep learning config system improved for runtime compatibility

### Fixed
- MCP server crashes: prompts/get (enum match), bugdb, uri templates
- Runtime compatibility issues with reserved keywords
- DL config default function replaced with standalone for runtime compatibility
- FFI skip test and SFFI wrapper verification

### Documentation
- Runtime parser bug root cause and rebuild limitations documented
- Duplication analysis and intentional duplications documented
- Test enablement progress tracking added

## [0.5.1-alpha] - 2026-02-09

### Added
- macOS self-hosting test automation (Intel x86_64 and Apple Silicon ARM64)
- Windows native compilation support with MSVC
- Windows cross-compilation from Linux using MinGW-w64
- FreeBSD bootstrap support via Linuxulator (experimental)
- FreeBSD QEMU testing infrastructure
- Comprehensive CI with 6 automated test jobs

### Changed
- GitHub Actions workflow expanded to 6 test jobs
- Bootstrap testing now covers 5 platforms

### Known Limitations
- Windows: Interpreter mode limited (use for compilation only)
- FreeBSD: Experimental support via Linuxulator

### Documentation
- 9 new documentation files for platform support and testing

## [0.5.0] - 2026-02-06

### Added
- 100% Pure Simple (Rust source removed)
- Self-hosting parser
- Pre-built runtime


