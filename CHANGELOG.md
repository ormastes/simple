# Changelog

All notable changes to Simple Language will be documented in this file.

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
