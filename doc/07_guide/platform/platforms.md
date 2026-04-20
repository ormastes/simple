# Platform Support Guide

Covers supported platforms, cross-compilation, platform abstraction library, and FreeBSD setup.

---

## Supported Platforms

### Linux

| Architecture | Status | Binary Location |
|--------------|--------|-----------------|
| x86_64 (Intel/AMD) | Production | `bin/release/linux-x86_64/simple` |
| ARM64 (aarch64) | Ready to Build | `bin/release/linux-arm64/simple` |
| RISC-V 64 | Experimental | `bin/release/linux-riscv64/simple` |

**Requirements:** GLIBC 2.17+ (CentOS 7+, Ubuntu 14.04+), 64-bit kernel and userspace.

### macOS

| Architecture | Status | Binary Location |
|--------------|--------|-----------------|
| x86_64 (Intel) | Ready to Build | `bin/release/macos-x86_64/simple` |
| ARM64 (M-series) | Ready to Build | `bin/release/macos-arm64/simple` |

**Requirements:** macOS 10.12+ (Intel), macOS 11.0+ (Apple Silicon), Xcode Command Line Tools.

### Windows

| Architecture | Status | Binary Location |
|--------------|--------|-----------------|
| x86_64 | Ready to Build | `bin/release/windows-x86_64/simple.exe` |
| ARM64 | Experimental | `bin/release/windows-arm64/simple.exe` |

**Requirements:** Windows 10+ (x86_64), Windows 11+ (ARM64), MSVC runtime.

### FreeBSD

| Architecture | Status | Binary Location |
|--------------|--------|-----------------|
| x86_64 | Experimental | `bin/release/freebsd-x86_64/simple` |

**Requirements:** FreeBSD 13+, 64-bit kernel and userspace.

Hosted Simple compiler binaries currently require 64-bit kernel/userspace. SimpleOS guest targets are separate from hosted compiler binaries and include 32-bit OS build lanes.

### SimpleOS Guest Targets

| Target | Architecture | Bits | Boot/Run Status |
|--------|--------------|------|-----------------|
| `x86_64-simpleos` | x86_64 | 64 | QEMU `qemu-system-x86_64` |
| `i686-simpleos` | x86_32 / i686 | 32 | QEMU `qemu-system-i386`, Multiboot1 C/ASM boot support |
| `aarch64-simpleos` | ARM64 | 64 | QEMU `qemu-system-aarch64` |
| `armv7-simpleos` | ARM32 | 32 | QEMU `qemu-system-arm` |
| `riscv64gc-simpleos` | RISC-V 64 | 64 | QEMU `qemu-system-riscv64` |
| `riscv32imac-simpleos` | RISC-V 32 | 32 | QEMU `qemu-system-riscv32` |

The multi-platform target catalog lives in `src/os/port/simpleos_multiplatform_build.spl`. It records target aliases, C and assembly boot sources, freestanding C/ASM flags, linker scripts, and QEMU defaults.

---

## Quick Start

```bash
# Download release
wget https://github.com/simple-lang/simple/releases/latest/download/simple-multi-platform.tar.gz
tar xzf simple-multi-platform.tar.gz && cd simple-multi-platform/

# The bin/simple wrapper auto-detects your platform
./bin/simple --version
./bin/simple hello.spl

# Add to PATH
export PATH="$PWD/bin:$PATH"
```

**Platform detection** uses `uname -m` (architecture) and `uname -s` (OS) to select the appropriate binary from `bin/release/<platform>/simple`.

**Manual selection** (if auto-detection fails):

```bash
bin/release/linux-x86_64/simple script.spl
bin/release/macos-arm64/simple script.spl
```

---

## Native Linker Support

The compiler supports automatic linker detection per platform:

| Platform | Linker Priority | Default Libraries |
|----------|----------------|-------------------|
| Linux | mold > lld > ld | c, pthread, dl, m, gcc_s, lzma |
| macOS | lld > ld64 | c, System |
| Windows | lld-link > link.exe | c, msvcrt, kernel32, ws2_32, advapi32 |
| FreeBSD | mold > lld > ld | c, pthread, m, execinfo |

Override with `SIMPLE_LINKER=<name>` environment variable.

---

## Building from Source

```bash
# Install Rust (if not already installed)
curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh

# Build the Rust seed bootstrap
cd src/compiler_rust
cargo build --profile bootstrap -p simple-driver

# Use the seed to compile the full Simple compiler
```

### Cross-Compilation

```bash
# Install cross-compilation tool
cargo install cross --git https://github.com/cross-rs/cross

# Build all platforms
scripts/build-bootstrap-multi-platform.sh
```

---

## Platform Abstraction Library

**Location:** `src/lib/platform/`

The Platform Abstraction Library provides a unified send/receive pattern for handling platform differences (endianness, newlines, pointer sizes).

**Key principle:** Convert at boundaries, not everywhere. Same-platform conversions are zero-cost no-ops.

### Quick Start

```simple
use std.platform.{host_config, network_config, send_u32, recv_u32}

val host = host_config()           # Auto-detect local machine
val net = network_config()         # Big-endian network byte order

val wire_val = send_u32(host, net, 0x12345678)  # Convert to network order
val local_val = recv_u32(host, net, wire_data)  # Convert from network order
```

### Configuration

- `host_config()` -- Auto-detect local machine properties
- `make_config(arch, os)` -- Create config for any target platform
- `network_config()` -- Network byte order (big-endian, LF)

### Endianness Conversion

```simple
val le_host = host_config()
val be_target = make_config(TargetArch.MCS51, TargetOS.BareMetal)
val swapped = send_u32(le_host, be_target, 0x12345678)  # byte-swapped
val original = recv_u32(le_host, be_target, swapped)     # restored
```

### Newline Translation

```simple
val unix = make_config(TargetArch.X86_64, TargetOS.Linux)
val win = make_config(TargetArch.X86_64, TargetOS.Windows)
val crlf_text = send_text(unix, win, "line1\nline2\n")  # LF -> CRLF
val lf_text = recv_text(unix, win, crlf_text)            # CRLF -> LF
```

### Wire Format (Binary Protocols)

```simple
# Serialize
var writer = wire_writer_network()
writer.write_u32(42)
writer.write_text("Hello")
val bytes = writer.to_bytes()

# Deserialize
var reader = wire_reader_new(bytes, network_config())
val value = reader.read_u32()
val text = reader.read_text()
```

### Cross-Platform File I/O

```simple
# Write with host platform newlines
text_file_write_local("output.txt", "line1\nline2\n")

# Read and normalize newlines to LF
val content = text_file_read_local("input.txt")

# Write with specific platform newlines
val win_cfg = make_config(TargetArch.X86_64, TargetOS.Windows)
text_file_write("output.txt", "line1\nline2\n", win_cfg)  # Forces CRLF
```

### Performance

- **Same-platform operations:** Zero overhead (identity function)
- **Cross-platform operations:** Minimal cost (byte swaps, newline replace)

---

## FreeBSD Development with QEMU

### Quick Setup (from Linux Host)

```bash
# 1. Install QEMU
sudo apt install qemu-system-x86 qemu-utils rsync openssh-client wget xz-utils

# 2. Set up FreeBSD VM
bin/simple run scripts/setup_freebsd_vm.spl

# 3. Start VM
~/vms/freebsd/start-freebsd-daemon.sh

# 4. SSH access
ssh -p 2222 root@localhost
```

### Native Bootstrap on FreeBSD

Inside the FreeBSD VM:

```bash
# Install prerequisites
pkg install cmake llvm gmake git

# Clone and bootstrap
git clone https://github.com/simple-lang/simple.git && cd simple
./scripts/bootstrap/bootstrap-from-scratch.sh

# Verify
bin/simple --version && bin/simple test
```

### Cross-Compilation (Linux -> FreeBSD)

```bash
# Install cross-compiler on Linux
sudo apt-get install clang lld

# Extract sysroot from FreeBSD VM
ssh -p 2222 root@localhost 'tar -czf /tmp/freebsd-sysroot.tar.gz /usr/include /usr/lib /lib'
scp -P 2222 root@localhost:/tmp/freebsd-sysroot.tar.gz ~/

# Build with FreeBSD toolchain
cmake ../seed -DCMAKE_TOOLCHAIN_FILE=../src/compiler_seed/cmake/toolchains/freebsd-x86_64.cmake
```

### FreeBSD Testing from Linux

```bash
bin/simple run scripts/test_freebsd_qemu.spl
```

This starts the VM, copies bootstrap binary and test sources, runs native compilation inside the VM, and verifies output.

### FreeBSD-Specific Notes

- **Package manager:** `pkg install` (not apt/dnf)
- **Make:** Use `gmake` for GNU Make (FreeBSD `make` is BSD Make)
- **Default compiler:** `clang++` (LLVM in base system)
- **SHA256:** `sha256` (not `sha256sum`)
- **Linuxulator:** FreeBSD can run Linux binaries via `kldload linux64`

### VM Management

```bash
# Start background VM
~/vms/freebsd/start-freebsd-daemon.sh

# Check status
ps aux | grep qemu-system-x86_64

# Stop VM
kill $(cat /tmp/freebsd-qemu.pid)
```

### Build Performance

| Stage | Time (KVM) | Time (TCG) |
|-------|------------|------------|
| Seed build | ~10s | ~30s |
| Core compilation | ~20s | ~60s |
| Full build | ~30s | ~120s |
| **Total** | **~60s** | **~210s** |

Use `--skip-verify` for faster dev builds (~40% faster). Use `--jobs=N` to match CPU cores.

---

## Troubleshooting

### Binary Not Found

```
Error: No Simple runtime found for platform: linux-x86_64
```

Check that `bin/release/linux-x86_64/simple` exists and is executable (`chmod +x`).

### Dynamic Linking Errors (Linux)

Update GLIBC or build from source with musl target.

### macOS Security Warning

```bash
xattr -d com.apple.quarantine bin/release/macos-*/simple
```

### Windows SmartScreen

Click "More info" then "Run anyway", or download from the official release page.

---

## Related Files

- Platform library: `src/lib/platform/`
- Target types: `src/lib/common/target.spl`
- VM setup script: `scripts/setup_freebsd_vm.spl`
- FreeBSD test: `scripts/test_freebsd_qemu.spl`
- Bootstrap script: `scripts/bootstrap/bootstrap-from-scratch.sh` (Linux path verified; FreeBSD-specific wrapper restoration still pending)
