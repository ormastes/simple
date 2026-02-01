# Changelog

All notable changes to the Simple Language project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

### Added

#### Self-Hosting Build System (2026-02-01)
- **Complete build system written in Simple** (~11,000 lines total)
  - 8 phases fully implemented: Foundation, Testing, Coverage, Quality, Bootstrap, Package, Migration, Advanced
  - 4,440 lines of implementation across 14 modules
  - 2,370 lines of SSpec tests (290+ comprehensive tests)
  - 2,000+ lines of documentation
- **Build Commands** (`simple build`):
  - `simple build` - Debug/release/bootstrap builds
  - `simple build test` - Unified test orchestration (Rust + doc-tests + Simple)
  - `simple build coverage` - Coverage analysis with cargo-llvm-cov (4 levels, 4 formats)
  - `simple build lint` - Clippy integration with auto-fix
  - `simple build fmt` - Rustfmt integration
  - `simple build check` - Combined quality checks (lint + fmt + test)
  - `simple build bootstrap` - 3-stage bootstrap pipeline with SHA256 verification
  - `simple build package` - Package creation (bootstrap + full)
  - `simple build watch` - Watch mode with auto-rebuild
  - `simple build incremental` - Incremental builds with caching
  - `simple build metrics` - Build performance metrics
  - `simple build clean` - Clean build artifacts
- **Implementation** (`src/app/build/`):
  - `main.spl` - CLI entry point
  - `cargo.spl` - Cargo FFI integration
  - `test.spl` - Test orchestration (parallel/serial, filtering)
  - `coverage.spl` - Coverage workflows
  - `quality.spl` - Lint, format, check commands
  - `bootstrap.spl` - 3-stage bootstrap pipeline
  - `package.spl` - Package creation
  - `metrics.spl`, `watch.spl`, `incremental.spl` - Advanced features
- **Type-Safe Configuration**:
  - `BuildConfig`, `TestConfig`, `CoverageConfig` types
  - Compile-time validation
  - Profile support (Debug, Release, Bootstrap)
- **Makefile Migration**:
  - Deprecation warnings on all make targets
  - Full backward compatibility maintained
  - Migration guide: `doc/build/migration_guide.md`
- **Documentation**:
  - Getting started: `doc/build/getting_started.md`
  - Phase completion reports (8 files)
  - Final summary: `doc/report/build_system_final_summary_2026-02-01.md`
- **FFI Integration**:
  - Uses existing `ffi/` infrastructure (env_process, file_io, time, hash)
  - No new FFI modules required

## [0.3.0] - 2026-01-31

### Added

#### Package Management System
- **Bootstrap Package**: Minimal runtime-only installation (~6 MB)
  - Essential 5 apps: cli, run, compile, check, repl
  - Optimized binary (22 MB → 6 MB compressed)
  - Cross-platform support (Linux, macOS, Windows)
- **Full Package**: Complete source distribution with binaries
- **Package CLI**: `simple package` command for build/install/uninstall
  - `simple package build` - Build packages
  - `simple package install` - Install packages
  - `simple package uninstall` - Uninstall packages
  - `simple package list` - List installed packages
  - `simple package verify` - Verify package integrity
  - `simple package upgrade` - Upgrade packages
- **Build Scripts**:
  - `script/build-bootstrap.sh` - Build bootstrap package
  - `script/build-full.sh` - Build full package
  - `script/install.sh` - Quick installer
- **Makefile Targets**:
  - `make package-bootstrap` - Build bootstrap package
  - `make package-full` - Build full package
  - `make install` - Install to ~/.local
  - `make install-system` - Install system-wide
  - `make uninstall` - Uninstall package
- **Platform Installers**:
  - Debian/Ubuntu .deb packages
  - Red Hat/Fedora .rpm packages
  - Homebrew formula for macOS
  - Windows MSI installer (WiX)
- **GitHub Actions**: Automated release workflow
  - Multi-platform builds (Linux, macOS, Windows)
  - Automatic uploads to GitHub Releases
  - SHA256 checksum generation
  - Installation testing

#### FFI Layer
- **Package Operations** (`rust/runtime/src/value/ffi/package.rs`):
  - `rt_package_sha256` - Calculate SHA256 checksums
  - `rt_package_create_tarball` - Create compressed archives
  - `rt_package_extract_tarball` - Extract archives
  - `rt_package_file_size` - Get file sizes
  - `rt_package_copy_file` - Copy files
  - `rt_package_mkdir_all` - Create directories
  - `rt_package_remove_dir_all` - Remove directories
  - `rt_package_create_symlink` - Create symbolic links
  - `rt_package_chmod` - Set file permissions
  - `rt_package_exists` - Check path existence
  - `rt_package_is_dir` - Check if path is directory

#### Documentation
- **Installation Guide** (`doc/guide/installation.md`):
  - Platform-specific instructions
  - Package manager integration
  - Manual installation steps
  - Troubleshooting section
- **Quick Install** (`INSTALL.md`):
  - One-line installers
  - Package sizes
  - System requirements
- **Implementation Report** (`doc/report/package_system_implementation_2026-01-31.md`):
  - Detailed implementation notes
  - Testing results
  - Performance metrics
  - Next steps

### Changed

#### Binary Optimization
- Reduced runtime binary size from 508 MB to 22 MB (95.7% reduction)
- Compressed package size: 6.4 MB (98.7% reduction from baseline)
- Optimizations:
  - Host-only architecture (removed `all-arch` Cranelift feature)
  - Optional TUI dependencies
  - LTO + single codegen-unit
  - Strip symbols in release builds

### Fixed
- Fixed array merge operation in interpreter (`collections.rs`)
  - Changed `.extend()` on slice to `.extend_from_slice()` on Vec
  - Resolved type mismatch error

### Dependencies
- Added `tar = "0.4"` - TAR archive support
- Added `flate2 = "1.0"` - gzip compression
- Added `sha2 = "0.10"` (already present) - SHA256 hashing

### Infrastructure
- GitHub Actions workflow for automated releases
- Multi-platform build pipeline (Linux x86_64, macOS ARM64/x86_64, Windows x86_64)
- Checksum verification for all packages
- Automated testing of installations

## [0.2.0] - Previous Release

### Added
- Self-hosted CLI implementation
- BDD test framework (SSpec)
- Hybrid execution (Cranelift + interpreter)
- 631+ tests

### Changed
- Migrated from Python to Simple for CLI tools
- Improved runtime performance

## [0.1.0] - Initial Release

### Added
- Lexer, parser, and AST
- HIR and MIR intermediate representations
- Cranelift code generation
- Interpreter fallback
- Basic standard library
- REPL

---

## Release Dates

- **0.3.0**: 2026-01-31 - Package Management System
- **0.2.0**: 2026-01-15 - Self-Hosted CLI
- **0.1.0**: 2025-12-01 - Initial Release

---

## Migration Guides

### 0.2.0 → 0.3.0

**No breaking changes**. Installation is now easier:

Before:
```bash
git clone https://github.com/simple-lang/simple.git
cd simple && make install
```

After:
```bash
curl -fsSL https://install.simple-lang.org/bootstrap.sh | sh
```

Or via package manager:
```bash
# Ubuntu/Debian
sudo apt-get install simple-lang

# macOS
brew install simple-lang/tap/simple

# Windows
choco install simple-lang
```

---

## Links

- [GitHub Repository](https://github.com/simple-lang/simple)
- [Documentation](https://simple-lang.org/docs)
- [Releases](https://github.com/simple-lang/simple/releases)
- [Installation Guide](doc/guide/installation.md)
