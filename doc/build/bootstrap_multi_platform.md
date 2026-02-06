# Bootstrap Multi-Platform Build System

This document describes the multi-platform bootstrap system for Simple Language.

## Overview

The bootstrap system provides pre-built runtime binaries for multiple platforms, enabling:
- Fast setup without Rust toolchain
- Cross-platform development
- Consistent runtime across platforms
- Easy distribution

## Architecture

### Binary Naming Convention

```
bin/bootstrap/<os>-<arch>/simple[.exe]
```

Examples:
- `bin/bootstrap/linux-x86_64/simple`
- `bin/bootstrap/macos-arm64/simple`
- `bin/bootstrap/windows-x86_64/simple.exe`

### Platform Auto-Detection

The `bin/simple` wrapper automatically:
1. Detects current OS and architecture
2. Finds appropriate bootstrap binary
3. Falls back to alternative locations if needed
4. Executes Simple CLI with the runtime

### Supported Platforms

| Platform | Status | Build Method | Notes |
|----------|--------|--------------|-------|
| `linux-x86_64` | ✅ Production | Native | Primary development platform |
| `linux-arm64` | ✅ Tested | Cross | Raspberry Pi, ARM servers |
| `linux-riscv64` | 🔄 Experimental | Cross | Emerging RISC-V hardware |
| `macos-x86_64` | ✅ Tested | Native | Intel Macs |
| `macos-arm64` | ✅ Tested | Native | M1/M2/M3 Macs |
| `windows-x86_64` | ✅ Builds | Native/Cross | Standard Windows |
| `windows-arm64` | 🔄 Experimental | Cross | ARM Windows devices |

## Build Methods

### 1. Local Multi-Platform Build

Build all platforms locally (requires `cross`):

```bash
# Install cross-compilation tool
cargo install cross --git https://github.com/cross-rs/cross

# Build all platforms
script/build-bootstrap-multi-platform.sh
```

Output:
```
bin/bootstrap/
├── linux-x86_64/simple (32 MB)
├── linux-arm64/simple (32 MB)
├── macos-arm64/simple (32 MB)
└── windows-x86_64/simple.exe (32 MB)
```

### 2. GitHub Actions CI/CD

Automated builds on every push to `main`:

**Workflow:** `.github/workflows/bootstrap-build.yml`

**Jobs:**
1. **build-bootstrap** - Builds for all platforms in parallel
2. **create-release-package** - Combines binaries into release

**Runners:**
- Ubuntu (Linux x86_64, cross-compile ARM64/RISC-V)
- macOS-13 (Intel Mac)
- macOS-14 (Apple Silicon)
- Windows (x86_64, cross-compile ARM64)

**Artifacts:**
- Individual platform binaries (30-day retention)
- Multi-platform tarball (90-day retention)

### 3. Manual Platform-Specific Build

Build for a specific target:

```bash
# Add target
rustup target add aarch64-unknown-linux-gnu

# Build (native)
cargo build --release --target aarch64-unknown-linux-gnu

# Build (cross)
cross build --release --target aarch64-unknown-linux-gnu

# Copy to bootstrap directory
mkdir -p bin/bootstrap/linux-arm64
cp target/aarch64-unknown-linux-gnu/release/simple_runtime \
   bin/bootstrap/linux-arm64/simple
chmod +x bin/bootstrap/linux-arm64/simple
```

## Integration with Simple Build System

### Build Commands

The Simple build system integrates with bootstrap:

```bash
# Use bootstrap for build system commands
bin/simple build                # Build project
bin/simple build test           # Run tests
bin/simple build bootstrap      # Rebuild bootstrap binaries
bin/simple build package        # Create release package
```

### Bootstrap Rebuild Workflow

```bash
# 1. Build new runtime from source
bin/simple build --release

# 2. Copy to bootstrap directory
cp target/release/simple_runtime bin/bootstrap/linux-x86_64/simple

# 3. Test new bootstrap
bin/bootstrap/linux-x86_64/simple --version

# 4. Rebuild entire system with new bootstrap
bin/simple build bootstrap-rebuild
```

## Release Process

### Creating Multi-Platform Release

1. **Build all platforms:**
   ```bash
   script/build-bootstrap-multi-platform.sh
   ```

2. **Create release package:**
   ```bash
   bin/simple build package
   ```

3. **Upload to GitHub:**
   ```bash
   gh release create v0.5.0 \
     release/simple-multi-platform-*.tar.gz \
     --title "Simple v0.5.0 - Multi-Platform" \
     --notes "See CHANGELOG.md for details"
   ```

### Release Package Contents

```
simple-multi-platform-20260206.tar.gz (71 MB)
└── simple-multi-platform/
    ├── bin/
    │   ├── simple (wrapper script)
    │   └── bootstrap/
    │       ├── linux-x86_64/simple
    │       ├── linux-arm64/simple
    │       ├── macos-x86_64/simple
    │       ├── macos-arm64/simple
    │       ├── windows-x86_64/simple.exe
    │       └── windows-arm64/simple.exe
    ├── src/ (Simple source code)
    ├── doc/ (Documentation)
    ├── README.md
    ├── CLAUDE.md
    └── PLATFORMS.md
```

## Platform-Specific Notes

### Linux

**Dependencies:**
- GLIBC 2.17+ (CentOS 7+, Ubuntu 14.04+)
- Dynamic linking to libc, libm, libpthread

**Distribution:**
- Works on all major distros (Ubuntu, Debian, Fedora, Arch, etc.)
- AppImage format planned for future

### macOS

**Compatibility:**
- Intel Macs: macOS 10.12+
- Apple Silicon: macOS 11.0+

**Code Signing:**
- Unsigned binaries require: System Preferences → Security → Allow
- Signed binaries planned for future releases

### Windows

**Requirements:**
- Windows 10+ (x86_64)
- Windows 11+ (ARM64)
- MSVC runtime (usually pre-installed)

**PowerShell Support:**
- Full support via `bin/simple.exe` wrapper
- Git Bash also works

### RISC-V (Experimental)

**Status:** Builds successfully, limited testing
**Hardware:** Tested on QEMU, awaiting real hardware testing
**Issues:** None known

## Binary Size Optimization

Current bootstrap size: **~32 MB** per platform

**Optimization Techniques Used:**
- LTO (Link-Time Optimization)
- Strip debug symbols
- Optimize for size + speed balance
- Dead code elimination

**Future Optimizations:**
- UPX compression: ~15 MB (-53%)
- Static linking: Larger but more portable
- Split runtime: Core + plugins

## Troubleshooting

### Build Failures

**Cross-compilation fails:**
```bash
# Install Docker (required by cross)
sudo apt-get install docker.io
sudo usermod -aG docker $USER
newgrp docker

# Retry build
script/build-bootstrap-multi-platform.sh
```

**Target not found:**
```bash
# Add missing target
rustup target add <target-triple>
```

### Runtime Issues

**Wrong platform detected:**
```bash
# Force specific platform
export SIMPLE_BOOTSTRAP_PLATFORM=linux-x86_64
bin/simple --version
```

**Binary not executable:**
```bash
# Fix permissions
chmod +x bin/bootstrap/*/simple*
```

### GitHub Actions Failures

**Timeout:**
- Increase timeout in workflow YAML
- Split jobs into smaller units

**Artifact upload fails:**
- Check artifact size limits (10 GB max)
- Compress binaries if needed

## Performance Characteristics

### Build Times (GitHub Actions)

| Platform | Runner | Time | Notes |
|----------|--------|------|-------|
| linux-x86_64 | ubuntu-latest | ~5 min | Native |
| linux-arm64 | ubuntu-latest | ~15 min | Cross + QEMU |
| linux-riscv64 | ubuntu-latest | ~20 min | Cross + QEMU |
| macos-x86_64 | macos-13 | ~8 min | Native |
| macos-arm64 | macos-14 | ~6 min | Native |
| windows-x86_64 | windows-latest | ~10 min | Native |
| windows-arm64 | windows-latest | ~18 min | Cross |

### Runtime Performance

All platforms have similar performance characteristics:
- Startup: <100ms
- JIT compilation: ~50ms per function
- Interpretation: 5-10x slower than native
- Memory: 10-50 MB typical usage

## Future Enhancements

### Planned Features
- [ ] Static linking option (musl for Linux)
- [ ] WebAssembly target (browser + server)
- [ ] Android ARM64 support
- [ ] iOS ARM64 support
- [ ] FreeBSD x86_64 support
- [ ] Smaller binary sizes (UPX, upx-ucl)

### Under Consideration
- [ ] ARM32 (armv7) for older devices
- [ ] PowerPC64 for IBM systems
- [ ] s390x for mainframes
- [ ] MIPS64 for routers

### Bootstrap Evolution
- [ ] Self-extracting executables
- [ ] Incremental updates (delta patches)
- [ ] Binary verification (checksums, signatures)
- [ ] Download-on-demand from CDN

## Contributing

### Adding New Platform

1. **Test feasibility:**
   ```bash
   rustup target add <target-triple>
   cargo build --release --target <target-triple>
   ```

2. **Update build scripts:**
   - Add to `script/build-bootstrap-multi-platform.sh`
   - Add to `.github/workflows/bootstrap-build.yml`

3. **Update documentation:**
   - Add to platform table
   - Document any special requirements

4. **Test thoroughly:**
   - Native testing on target platform
   - Cross-compilation testing
   - CI/CD integration testing

5. **Submit PR:**
   - Include test results
   - Update CHANGELOG.md
   - Add platform-specific notes

### Testing Checklist

For each new platform:
- [ ] Binary builds successfully
- [ ] Binary runs without errors
- [ ] `--version` shows correct info
- [ ] Basic scripts execute
- [ ] Build system works
- [ ] Test suite passes
- [ ] Size is reasonable (<50 MB)
- [ ] Performance is acceptable

## References

- Rust Platform Support: https://doc.rust-lang.org/nightly/rustc/platform-support.html
- Cross Tool: https://github.com/cross-rs/cross
- GitHub Actions Runners: https://docs.github.com/en/actions/using-github-hosted-runners
- Target Triples: https://rust-lang.github.io/rfcs/0131-target-specification.html
