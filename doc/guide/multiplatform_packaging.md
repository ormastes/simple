# Multi-Platform Packaging Guide

**Status:** Complete ✅
**Version:** 0.5.0

This guide explains how to build and distribute Simple packages for multiple platforms.

---

## Overview

Simple provides **Rust-free distribution** packages for all major platforms:
- Users download pre-compiled binaries + Simple source code
- **Zero Rust files** in distribution (development only)
- Cross-platform support: Linux, macOS, Windows × x86_64/ARM64

### Package Types

| Type | Size | Contents | Use Case |
|------|------|----------|----------|
| **Bootstrap** | ~10MB | Runtime + stdlib + examples | End users |
| **Full** | ~50MB | Runtime + all Simple source + docs | Developers |
| **Source** | ~20MB | All source (including Rust) | Contributors |

---

## Supported Platforms

### Official Releases

| Platform | Architecture | Binary Name | Status |
|----------|--------------|-------------|--------|
| Linux | x86_64 | `simple` | ✅ Tier 1 |
| Linux | aarch64 (ARM64) | `simple` | ✅ Tier 2 |
| macOS | x86_64 (Intel) | `simple` | ✅ Tier 1 |
| macOS | arm64 (Apple Silicon) | `simple` | ✅ Tier 1 |
| Windows | x86_64 | `simple.exe` | ✅ Tier 2 |
| Windows | aarch64 (ARM64) | `simple.exe` | 🔄 Tier 3 |

**Tier Definitions:**
- **Tier 1**: Native builds, CI tests, full support
- **Tier 2**: Cross-compiled, CI tests, supported
- **Tier 3**: Cross-compiled only, experimental

---

## Building Packages

### Prerequisites

**Required:**
- Rust toolchain (1.70+)
- Simple runtime (bootstrap or previous release)
- tar, gzip

**Optional:**
- UPX (for compression, reduces size by ~50%)
- Cross-compilation toolchains (for non-native platforms)

### Quick Start

Build packages for current platform:

```bash
# Build all package types
simple scripts/package-dist.spl

# Build bootstrap only
simple scripts/package-dist.spl --bootstrap-only

# Build with compression
simple scripts/package-dist.spl --compress

# Build specific platform
simple scripts/package-dist.spl --platform=linux-x86_64
```

### Build Options

```bash
simple scripts/package-dist.spl [OPTIONS]

Options:
  --version=VERSION        Package version (default: from simple.sdn)
  --profile=PROFILE        Build profile (bootstrap, release-opt)
  --platform=PLATFORM      Target platform (linux-x86_64, etc.)
  --bootstrap-only         Build only bootstrap packages
  --full-only              Build only full packages
  --compress               Compress with UPX (~50% size reduction)
  --help                   Show help
```

### Examples

```bash
# Build all platforms (requires cross-compilation setup)
simple scripts/package-dist.spl --platform=all

# Build macOS packages only
simple scripts/package-dist.spl --platform=darwin-arm64
simple scripts/package-dist.spl --platform=darwin-x86_64

# Build compressed bootstrap for current platform
simple scripts/package-dist.spl --bootstrap-only --compress

# Build specific version
simple scripts/package-dist.spl --version=0.5.0 --full-only
```

---

## Cross-Compilation

### Linux ARM64 (from x86_64)

```bash
# Install cross-compiler
sudo apt-get install gcc-aarch64-linux-gnu g++-aarch64-linux-gnu

# Add Rust target
rustup target add aarch64-unknown-linux-gnu

# Configure linker
export CARGO_TARGET_AARCH64_UNKNOWN_LINUX_GNU_LINKER=aarch64-linux-gnu-gcc

# Build
simple scripts/package-dist.spl --platform=linux-aarch64
```

### Windows (from Linux/macOS)

```bash
# Install mingw-w64
sudo apt-get install mingw-w64  # Linux
brew install mingw-w64          # macOS

# Add Rust target
rustup target add x86_64-pc-windows-gnu

# Build
simple scripts/package-dist.spl --platform=windows-x86_64
```

### macOS (from Linux)

```bash
# Install osxcross
# Follow: https://github.com/tpoechtrager/osxcross

# Add Rust targets
rustup target add x86_64-apple-darwin
rustup target add aarch64-apple-darwin

# Build
simple scripts/package-dist.spl --platform=darwin-x86_64
simple scripts/package-dist.spl --platform=darwin-arm64
```

---

## Package Contents

### Bootstrap Package

```
simple-bootstrap-0.5.0-linux-x86_64.tar.gz
├── bin/
│   └── simple              # Pre-compiled runtime (10MB, stripped)
├── lib/
│   └── std/                # Standard library (.spl source)
├── examples/               # Example programs
├── README.md
└── LICENSE
```

**Installation:**
```bash
tar -xzf simple-bootstrap-0.5.0-linux-x86_64.tar.gz -C ~/.local
export PATH="$HOME/.local/bin:$PATH"
simple --version
```

### Full Package

```
simple-full-0.5.0-linux-x86_64.tar.gz
├── bin/
│   └── simple              # Pre-compiled runtime
├── src/
│   ├── compiler/           # Compiler (100% Simple)
│   ├── app/                # Applications (100% Simple)
│   ├── std/                # Standard library
│   └── lib/                # Core libraries
├── lib/std/                # Installed stdlib
├── examples/               # Examples
├── doc/                    # Documentation
│   ├── guide/
│   └── spec/
├── README.md
├── LICENSE
├── CHANGELOG.md
└── simple.sdn              # Project manifest
```

**What's NOT included:**
- ❌ `rust/` directory (development only)
- ❌ Build artifacts (`build/`, `target/`)
- ❌ Test files (`test/`)
- ❌ Git metadata (`.git/`)

**Users see:**
- ✅ 100% Simple source code (compiler, stdlib, apps)
- ✅ Pre-compiled runtime binary (10MB)
- ✅ All documentation

### Source Package

```
simple-src-0.5.0.tar.gz
├── src/                    # All Simple source
├── rust/                   # Rust runtime source
├── test/                   # Test suite
├── examples/
├── doc/
└── ...                     # Full repository
```

**Use Case:** Contributors who want to modify the runtime

---

## CI/CD Integration

### GitHub Actions

The release workflow (`.github/workflows/release.yml`) automatically builds packages for all platforms:

**Trigger:**
- Tag push: `git tag v0.5.0 && git push --tags`
- Manual: GitHub Actions → Release → Run workflow

**Process:**
1. **Build runtime** for each platform (6 platforms)
2. **Create packages** (bootstrap + full)
3. **Generate checksums** (SHA256)
4. **Upload to GitHub Releases**
5. **Publish to GHCR** (GitHub Container Registry)

**Matrix:**
```yaml
strategy:
  matrix:
    include:
      - os: ubuntu-latest
        platform: linux-x86_64
        target: x86_64-unknown-linux-gnu

      - os: ubuntu-latest
        platform: linux-aarch64
        target: aarch64-unknown-linux-gnu
        cross_compile: true

      - os: macos-latest
        platform: darwin-arm64
        target: aarch64-apple-darwin

      - os: macos-15
        platform: darwin-x86_64
        target: x86_64-apple-darwin

      - os: windows-latest
        platform: windows-x86_64
        target: x86_64-pc-windows-msvc

      - os: windows-latest
        platform: windows-aarch64
        target: aarch64-pc-windows-msvc
        cross_compile: true
```

### Release Artifacts

Each release includes:
- `simple-bootstrap-VERSION-PLATFORM.tar.gz` (6 platforms)
- `simple-full-VERSION-PLATFORM.tar.gz` (6 platforms)
- `simple-src-VERSION.tar.gz` (source-only)
- `*.sha256` checksums for all packages

**Download:**
```bash
# Latest release
wget https://github.com/simple-lang/simple/releases/latest/download/simple-bootstrap-0.5.0-linux-x86_64.tar.gz

# Specific version
wget https://github.com/simple-lang/simple/releases/download/v0.5.0/simple-bootstrap-0.5.0-darwin-arm64.tar.gz
```

---

## Platform-Specific Notes

### Linux

**Glibc version:** Requires glibc 2.31+ (Ubuntu 20.04+, Debian 11+)

**Verify:**
```bash
ldd --version
# ldd (Ubuntu GLIBC 2.31-0ubuntu9.9) 2.31
```

**Static linking (future):**
```bash
# Build with MUSL for static binary (works on any Linux)
rustup target add x86_64-unknown-linux-musl
simple scripts/package-dist.spl --profile=musl
```

### macOS

**Minimum OS version:**
- x86_64: macOS 10.15+ (Catalina)
- arm64: macOS 11.0+ (Big Sur)

**Universal binary (future):**
```bash
# Combine x86_64 + arm64 into one binary
lipo -create \
  rust/target/x86_64-apple-darwin/bootstrap/simple \
  rust/target/aarch64-apple-darwin/bootstrap/simple \
  -output simple-universal
```

### Windows

**Runtime dependencies:**
- Visual C++ Redistributable (usually pre-installed)
- Windows 10 1809+ or Windows Server 2019+

**Installer (future):**
```bash
# Create .msi installer
cargo install cargo-wix
cargo wix --nocapture --target x86_64-pc-windows-msvc
```

---

## Size Optimization

### Binary Sizes

| Profile | Size | Techniques |
|---------|------|------------|
| Debug | 423 MB | No optimization |
| Release | 40 MB | Opt-level 3, strip |
| Bootstrap | 10 MB | Opt-level z, LTO, strip |
| Bootstrap + UPX | ~5 MB | + UPX compression |

### Cargo Profile (Bootstrap)

```toml
[profile.bootstrap]
inherits = "release"
opt-level = "z"           # Optimize for size
lto = "fat"               # Full LTO
codegen-units = 1         # Single codegen unit
strip = "debuginfo"       # Strip debug info
panic = "abort"           # Smaller panic handler
```

### UPX Compression

```bash
# Install UPX
sudo apt-get install upx-ucl  # Linux
brew install upx              # macOS

# Compress binary (automatic with --compress flag)
upx --best --lzma bin/simple

# Result: 10 MB → ~5 MB (50% reduction)
```

---

## Distribution Configuration

### simple.sdn

The package manifest (`simple.sdn`) controls distribution:

```sdn
distribution:
  # Files to include
  include:
    - bin/simple
    - lib/std/**/*.spl
    - src/**/*.spl
    - examples/**/*.spl

  # Files to exclude (never ship)
  exclude:
    - rust/**              # Rust source (dev only)
    - build/**
    - test/**

  # Binaries per platform
  binaries:
    simple_runtime:
      platforms:
        - linux-x86_64
        - darwin-arm64
        - windows-x86_64
      source: rust/target/{target}/{profile}/simple
      strip: true
      compress: upx

  # Package types
  formats:
    bootstrap:
      type: tar.gz
      includes: [bin, lib, examples]

    full:
      type: tar.gz
      includes: [bin, lib, src, examples, doc]
```

---

## Verification

### Checksums

Every package includes a SHA256 checksum:

```bash
# Verify download
sha256sum -c simple-bootstrap-0.5.0-linux-x86_64.tar.gz.sha256

# Expected output:
# simple-bootstrap-0.5.0-linux-x86_64.tar.gz: OK
```

### Package Contents

```bash
# List contents
tar -tzf simple-bootstrap-0.5.0-linux-x86_64.tar.gz | head -20

# Extract and verify
tar -xzf simple-bootstrap-0.5.0-linux-x86_64.tar.gz
./bin/simple --version
# Output: Simple 0.5.0
```

### No Rust Files

```bash
# Verify no Rust source in package
tar -tzf simple-bootstrap-0.5.0-linux-x86_64.tar.gz | grep -E '\.(rs|toml)$'
# Should return nothing (empty)

tar -tzf simple-full-0.5.0-linux-x86_64.tar.gz | grep 'rust/'
# Should return nothing (rust/ excluded)
```

---

## Troubleshooting

### Build Errors

**Problem:** `GLIBC_2.XX not found`

**Solution:** Build on older Linux (Ubuntu 20.04) or use MUSL:
```bash
rustup target add x86_64-unknown-linux-musl
cargo build --target=x86_64-unknown-linux-musl
```

**Problem:** Cross-compilation linker not found

**Solution:** Install cross-compiler:
```bash
# ARM64
sudo apt-get install gcc-aarch64-linux-gnu

# Windows
sudo apt-get install mingw-w64
```

**Problem:** UPX compression fails

**Solution:** Skip compression or update UPX:
```bash
# Skip compression
simple scripts/package-dist.spl --no-compress

# Update UPX
wget https://github.com/upx/upx/releases/download/v4.0.2/upx-4.0.2-amd64_linux.tar.xz
tar -xf upx-4.0.2-amd64_linux.tar.xz
sudo cp upx-4.0.2-amd64_linux/upx /usr/local/bin/
```

### Runtime Errors

**Problem:** `error while loading shared libraries: libc.so.6`

**Solution:** System glibc too old, use MUSL build or upgrade OS

**Problem:** `Permission denied` when running `simple`

**Solution:** Set executable bit:
```bash
chmod +x bin/simple
```

---

## Future Enhancements

### Planned Features

1. **Static Linking** (MUSL builds for Linux)
2. **Universal Binaries** (macOS: x86_64 + arm64 in one file)
3. **Windows Installer** (.msi with cargo-wix)
4. **Package Manager** Integration
   - Homebrew (macOS/Linux)
   - Chocolatey (Windows)
   - Scoop (Windows)
   - Snap/Flatpak (Linux)

5. **Container Images**
   - Docker: `docker run simple-lang/simple`
   - OCI artifacts in GHCR

6. **Auto-Update**
   ```bash
   simple update         # Check for new version
   simple update --install  # Download and install
   ```

### Contribution Areas

- [ ] MUSL static builds
- [ ] Windows ARM64 native CI runners
- [ ] macOS universal binary generation
- [ ] Package manager formulas (Homebrew, etc.)
- [ ] Auto-update mechanism
- [ ] Binary signing (code signing for macOS/Windows)

---

## See Also

- **CI/CD:** `.github/workflows/release.yml`
- **Package Script:** `scripts/package-dist.spl`
- **Platform API:** `src/std/platform/mod.spl`
- **Distribution Config:** `simple.sdn`
- **Installation Guide:** `README.md`
