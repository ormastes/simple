# Changelog

All notable changes to Simple Language will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [0.5.0-rc.1] - 2026-02-06

### Added

#### Multi-Platform Bootstrap System
- **7-platform support**: linux-x86_64, linux-arm64, linux-riscv64, macos-x86_64, macos-arm64, windows-x86_64, windows-arm64
- **Smart platform detection**: Automatic OS and architecture detection in `bin/simple` wrapper
- **GitHub Actions CI/CD**: Automated builds for all platforms in parallel (~20 minutes)
- **Multi-platform build script**: `script/build-bootstrap-multi-platform.sh` for local builds
- **Comprehensive documentation**:
  - `bin/bootstrap/README.md` - Bootstrap guide
  - `doc/build/bootstrap_multi_platform.md` - Technical documentation
  - `doc/build/github_actions_bootstrap_guide.md` - CI/CD guide
  - `PLATFORMS.md` - Platform support overview

#### Testing Infrastructure
- **Bootstrap test suite**: 32 tests covering all functionality
- **Test scripts**:
  - `test/test_bootstrap.spl` - Core feature tests
  - `test/test_bootstrap_wrapper.sh` - Wrapper functionality tests
  - `test/test_bootstrap_comprehensive.sh` - Complete system verification
- **100% pass rate**: All 32 tests passing

#### Documentation
- **Multi-platform setup guide**: Complete instructions for all platforms
- **GitHub Actions integration**: Step-by-step workflow documentation
- **Platform-specific notes**: Requirements and troubleshooting for each OS
- **Implementation report**: Full technical details in `doc/report/`

### Changed

#### Bootstrap Structure
- **Reorganized binary locations**: From `bin/bootstrap/simple_runtime` to `bin/bootstrap/<platform>/simple`
- **Platform-specific naming**: `.exe` extension for Windows binaries
- **Fallback chain**: Smart fallback to legacy locations for backwards compatibility

#### Pure Simple Implementation
- **Removed Rust source dependency**: System works without `rust/` directory
- **Fixed circular dependencies**: Between `app.io` and `std.platform` modules
- **Environment-based platform detection**: Using `WINDIR` check instead of `rt_host_os()`

### Fixed

- **Module loading errors**: Fixed `is_windows` not found error
- **Circular dependencies**: Broken circular dependency between `app.io` and `std.platform`
- **Platform detection**: Robust detection with clear error messages

### Performance

- **Binary size**: 31-32 MB per platform (optimized)
- **Startup time**: ~6ms (very fast)
- **CI/CD build time**: ~20 minutes for all 7 platforms (parallel)

### Infrastructure

- **GitHub Actions**: Automated multi-platform builds
- **Artifact retention**: 30 days (binaries), 90 days (release packages)
- **Cross-compilation**: Support via `cross-rs` tool

## [0.4.0] - 2026-02-05

### Added
- Self-hosting build system (100% complete)
- Unified database library (production-ready)
- MCP server integration
- Pure Simple implementation (no Rust dependencies)

### Changed
- Migrated to 100% Pure Simple codebase
- Deleted 24.2 GB of Rust source code

## [0.3.0] - 2026-01-31

### Added
- Initial bootstrap runtime
- Basic platform support
- Simple language core features

---

[0.5.0-rc.1]: https://github.com/simple-lang/simple/releases/tag/v0.5.0-rc.1
[0.4.0]: https://github.com/simple-lang/simple/releases/tag/v0.4.0
[0.3.0]: https://github.com/simple-lang/simple/releases/tag/v0.3.0
