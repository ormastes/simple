# Changelog

All notable changes to Simple Language will be documented in this file.

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

See git history for older versions.
