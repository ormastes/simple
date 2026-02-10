# Bootstrap Binaries - Multi-Platform Support

This directory contains pre-built Simple runtime binaries for different platforms.

## Directory Structure

```
bin/release/
├── linux-x86_64/simple       # Linux Intel/AMD 64-bit
├── linux-arm64/simple        # Linux ARM 64-bit
├── linux-riscv64/simple      # Linux RISC-V 64-bit
├── macos-x86_64/simple       # macOS Intel
├── macos-arm64/simple        # macOS Apple Silicon (M1/M2/M3)
├── windows-x86_64/simple.exe # Windows Intel/AMD 64-bit
└── windows-arm64/simple.exe  # Windows ARM 64-bit
```

## Platform Support

| Platform | Architecture | Status | Size |
|----------|--------------|--------|------|
| **Linux** | x86_64 | ✅ Tested | ~32 MB |
| **Linux** | ARM64 | ✅ Builds | ~32 MB |
| **Linux** | RISC-V 64 | 🔄 Experimental | ~32 MB |
| **macOS** | x86_64 (Intel) | ✅ Tested | ~32 MB |
| **macOS** | ARM64 (M-series) | ✅ Tested | ~32 MB |
| **Windows** | x86_64 | ✅ Builds | ~32 MB |
| **Windows** | ARM64 | 🔄 Experimental | ~32 MB |

## Usage

### Automatic Platform Detection

The `bin/simple` wrapper automatically detects your platform:

```bash
bin/simple --version
bin/simple your_script.spl
```

### Direct Execution

You can also run the bootstrap binary directly:

**Linux x86_64:**
```bash
bin/release/linux-x86_64/simple your_script.spl
```

**macOS ARM64:**
```bash
bin/release/macos-arm64/simple your_script.spl
```

**Windows x86_64:**
```powershell
bin\bootstrap\windows-x86_64\simple.exe your_script.spl
```

## Building Bootstrap Binaries

### Local Build (All Platforms)

```bash
# Install cross-compilation tool (optional, for other platforms)
cargo install cross --git https://github.com/cross-rs/cross

# Build all platforms
script/build-bootstrap-multi-platform.sh
```

### Build Specific Platform

```bash
# Linux ARM64
cross build --release --target aarch64-unknown-linux-gnu
cp target/aarch64-unknown-linux-gnu/release/simple_runtime \
   bin/release/linux-arm64/simple

# macOS Apple Silicon
cargo build --release --target aarch64-apple-darwin
cp target/aarch64-apple-darwin/release/simple_runtime \
   bin/release/macos-arm64/simple

# Windows x86_64
cargo build --release --target x86_64-pc-windows-msvc
cp target/x86_64-pc-windows-msvc/release/simple_runtime.exe \
   bin/release/windows-x86_64/simple.exe
```

### GitHub Actions (CI/CD)

The `.github/workflows/bootstrap-build.yml` workflow automatically builds
all platforms on push to main:

- Runs on Ubuntu (Linux), macOS, Windows runners
- Uses `cross` for cross-compilation when needed
- Uploads artifacts for each platform
- Creates multi-platform release package

## Binary Characteristics

- **Format**: Native executable (ELF for Linux, Mach-O for macOS, PE for Windows)
- **Linking**: Dynamically linked (requires system libc)
- **Size**: ~32 MB (release build)
- **Debug Info**: Stripped for release
- **Optimizations**: Maximum speed + size optimizations

## Downloading Pre-Built Binaries

If you don't have a bootstrap binary for your platform:

1. **GitHub Releases:**
   ```bash
   wget https://github.com/simple-lang/simple/releases/latest/download/simple-linux-x86_64.tar.gz
   tar xzf simple-linux-x86_64.tar.gz
   ```

2. **Manual Installation:**
   - Download from: https://github.com/simple-lang/simple/releases
   - Extract to `bin/release/<platform>/`
   - Make executable: `chmod +x bin/release/<platform>/simple`

## Platform Detection Algorithm

The `bin/simple` wrapper uses this detection logic:

1. **Architecture Detection:**
   - `uname -m` → x86_64, aarch64, riscv64
   - Normalizes to: x86_64, arm64, riscv64

2. **OS Detection:**
   - `uname -s` → Linux, Darwin, MINGW*/MSYS*/CYGWIN*
   - Normalizes to: linux, macos, windows

3. **Binary Selection:**
   - First: `bin/release/<os>-<arch>/simple[.exe]`
   - Fallback 1: `bin/release/simple_runtime` (legacy)
   - Fallback 2: `bin/simple_runtime` (development)
   - Fallback 3: `release/simple-0.4.0-beta/bin/simple_runtime`

## Troubleshooting

### Binary Not Found

```
Error: No Simple runtime found for platform: linux-x86_64
```

**Solution:**
1. Download the bootstrap binary for your platform
2. Place it in `bin/release/linux-x86_64/simple`
3. Make it executable: `chmod +x bin/release/linux-x86_64/simple`

### Permission Denied

```
bash: bin/release/linux-x86_64/simple: Permission denied
```

**Solution:**
```bash
chmod +x bin/release/linux-x86_64/simple
```

### Wrong Architecture

```
Error: Unsupported architecture: i686
```

**Solution:** 32-bit architectures are not supported. Use 64-bit system.

### Cross-Platform Notes

- **Windows:** Use PowerShell or Git Bash for running scripts
- **macOS:** May need to allow unsigned binaries: System Preferences → Security
- **Linux:** Requires GLIBC 2.17+ (CentOS 7+, Ubuntu 14.04+, Debian 8+)

## Future Plans

- [ ] ARM32 support (armv7)
- [ ] FreeBSD x86_64
- [ ] Static linking option (for embedded/container use)
- [ ] Cross-compile to WebAssembly (WASM)
- [ ] Android ARM64
- [ ] iOS ARM64

## Contributing

To add support for a new platform:

1. Add platform to `PLATFORMS` in `script/build-bootstrap-multi-platform.sh`
2. Add platform to matrix in `.github/workflows/bootstrap-build.yml`
3. Test on the target platform
4. Update this README with status
5. Submit PR with test results

## License

Same as Simple Language project (see LICENSE file in project root).
