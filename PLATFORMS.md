# Simple Language - Platform Support

## Supported Platforms

Simple Language provides pre-built bootstrap binaries for multiple platforms:

### Linux

| Architecture | Status | Binary Location | Size |
|--------------|--------|-----------------|------|
| x86_64 (Intel/AMD) | ✅ **Production** | `bin/release/linux-x86_64/simple` | 32 MB |
| ARM64 (aarch64) | 🔄 Ready to Build | `bin/release/linux-arm64/simple` | 32 MB |
| RISC-V 64 | 🔄 Experimental | `bin/release/linux-riscv64/simple` | 32 MB |

**Requirements:**
- GLIBC 2.17+ (CentOS 7+, Ubuntu 14.04+, Debian 8+)
- 64-bit kernel and userspace

### macOS

| Architecture | Status | Binary Location | Size |
|--------------|--------|-----------------|------|
| x86_64 (Intel) | 🔄 Ready to Build | `bin/release/macos-x86_64/simple` | 32 MB |
| ARM64 (M-series) | 🔄 Ready to Build | `bin/release/macos-arm64/simple` | 32 MB |

**Requirements:**
- macOS 10.12+ (Intel)
- macOS 11.0+ (Apple Silicon)
- Xcode Command Line Tools (for system libraries)

### Windows

| Architecture | Status | Binary Location | Size |
|--------------|--------|-----------------|------|
| x86_64 (Intel/AMD) | 🔄 Ready to Build | `bin/release/windows-x86_64/simple.exe` | 32 MB |
| ARM64 | 🔄 Experimental | `bin/release/windows-arm64/simple.exe` | 32 MB |

**Requirements:**
- Windows 10+ (x86_64)
- Windows 11+ (ARM64)
- MSVC runtime (usually pre-installed)

## Quick Start

### 1. Download and Extract

```bash
# Download release
wget https://github.com/simple-lang/simple/releases/latest/download/simple-multi-platform.tar.gz

# Extract
tar xzf simple-multi-platform.tar.gz
cd simple-multi-platform/
```

### 2. Run Simple

The `bin/simple` wrapper automatically detects your platform:

```bash
# Check version
./bin/simple --version

# Run a script
./bin/simple hello.spl

# Interactive mode
./bin/simple
```

### 3. Add to PATH (Optional)

```bash
# Linux/macOS
export PATH="$PWD/bin:$PATH"
echo 'export PATH="/path/to/simple/bin:$PATH"' >> ~/.bashrc

# Windows (PowerShell)
$env:Path += ";C:\path\to\simple\bin"
```

## Platform Detection

The bootstrap system automatically detects your platform using:

1. **Architecture:** `uname -m` → x86_64, aarch64, riscv64
2. **Operating System:** `uname -s` → Linux, Darwin (macOS), Windows

The wrapper then selects the appropriate binary from `bin/release/<platform>/simple`.

## Manual Platform Selection

If automatic detection fails or you want to use a specific binary:

```bash
# Linux x86_64
bin/release/linux-x86_64/simple script.spl

# macOS ARM64 (M1/M2/M3)
bin/release/macos-arm64/simple script.spl

# Windows x86_64
bin\bootstrap\windows-x86_64\simple.exe script.spl
```

## Building from Source

If a pre-built binary isn't available for your platform:

### Requirements

- Rust toolchain (1.70+)
- Cargo (bundled with Rust)
- `cross` tool (for cross-compilation, optional)

### Native Build

```bash
# Install Rust (if not already installed)
curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh

# Build Simple runtime
cargo build --release

# Copy to bootstrap directory
mkdir -p bin/release/$(uname -s | tr '[:upper:]' '[:lower:]')-$(uname -m)
cp target/release/simple_runtime bin/release/*/simple
```

### Multi-Platform Build

```bash
# Install cross-compilation tool
cargo install cross --git https://github.com/cross-rs/cross

# Build all platforms
script/build-bootstrap-multi-platform.sh
```

## Unsupported Platforms

### 32-bit Systems

Simple Language requires 64-bit systems. 32-bit platforms (i686, armv7) are not supported.

### Other Platforms

We welcome contributions to add support for:
- FreeBSD (x86_64, ARM64)
- OpenBSD (x86_64)
- NetBSD (x86_64)
- Solaris/Illumos (x86_64)
- WebAssembly (WASM)
- Android (ARM64)
- iOS (ARM64)

See `doc/build/bootstrap_multi_platform.md` for contribution guidelines.

## Troubleshooting

### Binary Not Found

```
Error: No Simple runtime found for platform: linux-x86_64
```

**Solution:**
1. Check that `bin/release/linux-x86_64/simple` exists
2. Make sure the binary is executable: `chmod +x bin/release/linux-x86_64/simple`
3. Download the pre-built binary for your platform

### Permission Denied

```
bash: bin/simple: Permission denied
```

**Solution:**
```bash
chmod +x bin/simple
chmod +x bin/release/*/simple*
```

### Wrong Architecture

```
Error: Unsupported architecture: i686
```

**Solution:** Simple requires 64-bit systems. Upgrade to 64-bit OS or use a 64-bit machine.

### Dynamic Linking Errors (Linux)

```
error while loading shared libraries: libc.so.6
```

**Solution:**
- Update GLIBC: `sudo apt-get update && sudo apt-get upgrade`
- Use static build (if available)
- Build from source with musl target

### macOS Security Warning

```
"simple" cannot be opened because it is from an unidentified developer
```

**Solution:**
1. Open System Preferences → Security & Privacy
2. Click "Allow" next to the warning message
3. Alternatively: `xattr -d com.apple.quarantine bin/release/macos-*/simple`

### Windows SmartScreen

```
Windows protected your PC
```

**Solution:**
1. Click "More info"
2. Click "Run anyway"
3. Or: Download from official release page

## Platform-Specific Notes

### Linux

- **Package Managers:** Future plans for APT, DNF, Pacman repositories
- **AppImage:** Planned for maximum compatibility
- **Snap/Flatpak:** Under consideration

### macOS

- **Homebrew:** Formula planned for easy installation
- **Code Signing:** Will be added in future releases
- **Universal Binary:** Planned (x86_64 + ARM64 in one file)

### Windows

- **Chocolatey:** Package planned
- **Winget:** Package planned
- **Installer:** MSI installer planned
- **PowerShell:** Full support via wrapper

## Performance Characteristics

All platforms have similar performance:

- **Startup time:** <100ms
- **JIT compilation:** ~50ms per function
- **Memory usage:** 10-50 MB typical
- **Execution speed:** 5-10x slower than native (interpreted)

Native code generation (AOT compilation) is planned, which will provide:
- **Startup time:** ~1s (compilation + execution)
- **Execution speed:** Near-native (1-2x overhead)

## Getting Help

- **Documentation:** See `doc/` directory
- **Issues:** https://github.com/simple-lang/simple/issues
- **Discussions:** https://github.com/simple-lang/simple/discussions
- **Discord:** https://discord.gg/simple-lang (coming soon)

## License

Simple Language is open source under the MIT License.
See LICENSE file for details.

---

**Last Updated:** 2026-02-06
**Version:** 0.4.0-pure-simple
