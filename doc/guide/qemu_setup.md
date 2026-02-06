# QEMU Setup Guide for Simple Language Development

This guide covers installing QEMU with support for all architectures used by Simple's bare-metal and boot testing infrastructure.

---

## Overview

Simple's boot testing and bare-metal development requires QEMU emulators for:
- **x86** (i386) - 32-bit x86 systems
- **x86_64** - 64-bit x86 systems
- **ARM** (armv7) - 32-bit ARM Cortex-M
- **AArch64** - 64-bit ARM
- **RISC-V 32** - 32-bit RISC-V
- **RISC-V 64** - 64-bit RISC-V

---

## Quick Install

### Linux (Ubuntu/Debian)

```bash
# Install QEMU system emulators
sudo apt-get update
sudo apt-get install -y \
    qemu-system-x86 \
    qemu-system-arm \
    qemu-system-misc

# Verify installation
qemu-system-i386 --version      # x86 32-bit
qemu-system-x86_64 --version    # x86 64-bit
qemu-system-arm --version       # ARM 32-bit
qemu-system-aarch64 --version   # ARM 64-bit
qemu-system-riscv32 --version   # RISC-V 32-bit
qemu-system-riscv64 --version   # RISC-V 64-bit
```

### Linux (Fedora/RHEL)

```bash
# Install QEMU system emulators
sudo dnf install -y \
    qemu-system-x86 \
    qemu-system-arm \
    qemu-system-riscv

# Verify (same as Ubuntu)
qemu-system-i386 --version
qemu-system-riscv32 --version
```

### Linux (Arch)

```bash
# Install QEMU (includes all system emulators)
sudo pacman -S qemu-full

# Verify
qemu-system-i386 --version
qemu-system-riscv32 --version
```

### macOS (Homebrew)

```bash
# Install QEMU
brew install qemu

# Verify installation (all architectures included)
qemu-system-i386 --version
qemu-system-x86_64 --version
qemu-system-arm --version
qemu-system-aarch64 --version
qemu-system-riscv32 --version
qemu-system-riscv64 --version
```

### Windows (Chocolatey)

```powershell
# Install QEMU
choco install qemu

# Verify installation
qemu-system-i386 --version
qemu-system-riscv32 --version
```

### Windows (Official Installer)

1. Download from https://qemu.weilnetz.de/w64/
2. Run the installer (e.g., `qemu-w64-setup-20240117.exe`)
3. Add to PATH: `C:\Program Files\qemu`
4. Verify in PowerShell:
   ```powershell
   qemu-system-i386 --version
   ```

---

## Building from Source (Advanced)

### Linux (All Distributions)

**Install dependencies:**

```bash
# Ubuntu/Debian
sudo apt-get install -y \
    build-essential \
    pkg-config \
    ninja-build \
    libglib2.0-dev \
    libpixman-1-dev \
    libfdt-dev \
    zlib1g-dev

# Fedora/RHEL
sudo dnf install -y \
    gcc make ninja-build \
    glib2-devel pixman-devel \
    libfdt-devel zlib-devel

# Arch
sudo pacman -S base-devel ninja glib2 pixman dtc zlib
```

**Build QEMU:**

```bash
# Download QEMU source
wget https://download.qemu.org/qemu-8.2.0.tar.xz
tar xJf qemu-8.2.0.tar.xz
cd qemu-8.2.0

# Configure with all Simple-required targets
./configure \
    --target-list=i386-softmmu,x86_64-softmmu,arm-softmmu,aarch64-softmmu,riscv32-softmmu,riscv64-softmmu \
    --prefix=/usr/local \
    --enable-debug \
    --enable-gdb

# Build (use -j$(nproc) for parallel build)
make -j$(nproc)

# Install (requires sudo)
sudo make install

# Verify
qemu-system-i386 --version
# Output: QEMU emulator version 8.2.0
```

### macOS (Homebrew-based)

```bash
# Install build dependencies
brew install ninja pkg-config glib pixman

# Download and build (same as Linux)
wget https://download.qemu.org/qemu-8.2.0.tar.xz
tar xJf qemu-8.2.0.tar.xz
cd qemu-8.2.0

./configure \
    --target-list=i386-softmmu,x86_64-softmmu,arm-softmmu,aarch64-softmmu,riscv32-softmmu,riscv64-softmmu \
    --prefix=/usr/local

make -j$(sysctl -n hw.ncpu)
sudo make install
```

### Windows (MSYS2)

**Install MSYS2:**
1. Download from https://www.msys2.org/
2. Run installer
3. Open MSYS2 MINGW64 terminal

**Install dependencies:**

```bash
pacman -S --needed \
    base-devel \
    mingw-w64-x86_64-toolchain \
    mingw-w64-x86_64-glib2 \
    mingw-w64-x86_64-pixman \
    mingw-w64-x86_64-gtk3 \
    ninja
```

**Build QEMU:**

```bash
wget https://download.qemu.org/qemu-8.2.0.tar.xz
tar xJf qemu-8.2.0.tar.xz
cd qemu-8.2.0

./configure \
    --target-list=i386-softmmu,x86_64-softmmu,arm-softmmu,aarch64-softmmu,riscv32-softmmu,riscv64-softmmu \
    --enable-gtk \
    --enable-sdl

make -j$(nproc)
make install
```

---

## Feature Requirements

Simple's boot testing requires these QEMU features:

### GDB Stub Support
- **Requirement:** Built-in GDB server for remote debugging
- **Verification:** `qemu-system-i386 -gdb tcp::1234 -S` (should start and wait for GDB)
- **Build flag:** `--enable-gdb` (usually enabled by default)

### Serial Output Capture
- **Requirement:** Serial port redirection to file
- **Verification:**
  ```bash
  qemu-system-i386 -serial file:/tmp/test.log
  # Check that /tmp/test.log can be created
  ```
- **Usage:** `-serial stdio` or `-serial file:path`

### Machine Types
- **x86:** `pc` (default), `q35` (modern)
- **ARM:** `lm3s6965evb` (Cortex-M3), `virt` (generic)
- **RISC-V:** `virt` (generic, supports SiFive UART)

**Verify supported machines:**

```bash
qemu-system-i386 -machine help
qemu-system-arm -machine help
qemu-system-riscv32 -machine help
```

### Debug Exit Device (x86 only)
- **Requirement:** ISA debug-exit device for clean shutdown in tests
- **Verification:** Check if available:
  ```bash
  qemu-system-i386 -device help | grep isa-debug-exit
  ```
- **Usage:** `-device isa-debug-exit,iobase=0xf4,iosize=0x04`

---

## Verification Tests

### Test x86 Boot

```bash
# Create minimal kernel
echo -e "\xb8\x00\x00\x00\x00\xcd\x10" > /tmp/test.bin

# Run in QEMU (should start and halt)
qemu-system-i386 -kernel /tmp/test.bin -serial stdio -nographic

# Press Ctrl+A then X to exit
```

### Test RISC-V 32 Boot

```bash
# Simple RISC-V kernel (just WFI loop)
echo -e "\x73\x00\x50\x10" > /tmp/riscv_test.bin

# Run in QEMU
qemu-system-riscv32 -machine virt -kernel /tmp/riscv_test.bin -serial stdio -nographic
```

### Test GDB Integration

**Terminal 1:**
```bash
# Start QEMU with GDB stub (will wait)
qemu-system-i386 -kernel /tmp/test.bin -s -S -nographic
```

**Terminal 2:**
```bash
# Connect GDB
gdb
(gdb) target remote localhost:1234
(gdb) info registers
(gdb) quit
```

### Test Serial Capture

```bash
# Run with serial output to file
qemu-system-i386 -kernel /tmp/test.bin -serial file:/tmp/serial.log -nographic &
QEMU_PID=$!

# Wait and check output
sleep 1
cat /tmp/serial.log

# Kill QEMU
kill $QEMU_PID
```

---

## Integration with Simple

### Running Simple Boot Tests

Once QEMU is installed, Simple's boot tests work automatically:

```bash
# Run all boot tests
simple test test/baremetal/boot_test_spec.spl

# Run specific architecture
simple test test/baremetal/boot_test_spec.spl --tag=x86
simple test test/baremetal/boot_test_spec.spl --tag=riscv32
simple test test/baremetal/boot_test_spec.spl --tag=arm

# Run with debug output
simple test test/baremetal/debug_boot_spec.spl
```

### Boot Test Infrastructure

**Files:**
- `src/lib/qemu/mod.spl` - QEMU process management
- `src/lib/qemu/boot_runner.spl` - Boot testing framework
- `src/lib/qemu/debug_boot_runner.spl` - Debug integration
- `test/baremetal/boot_test_spec.spl` - Boot tests
- `test/baremetal/debug_boot_spec.spl` - Debug tests

### Example: Manual QEMU Usage

```bash
# Build Simple bare-metal kernel
simple build test/fixtures/boot/x86_minimal.spl --bare-metal -o x86_kernel.elf

# Run in QEMU with serial output
qemu-system-i386 \
    -kernel x86_kernel.elf \
    -serial stdio \
    -display none

# With GDB debugging
qemu-system-i386 \
    -kernel x86_kernel.elf \
    -serial stdio \
    -s -S \
    -display none
```

---

## Troubleshooting

### "qemu-system-riscv32: command not found"

**Cause:** RISC-V emulators not installed

**Fix (Ubuntu/Debian):**
```bash
sudo apt-get install qemu-system-misc
```

**Fix (Fedora):**
```bash
sudo dnf install qemu-system-riscv
```

### "Failed to allocate KVM memory"

**Cause:** KVM acceleration not available (common in VMs)

**Fix:** Disable KVM acceleration
```bash
qemu-system-x86_64 -no-kvm ...
```

Or in Simple tests:
```simple
val config = QemuConfig(
    # ... other settings
    accel: QemuAccel.Tcg  # Use TCG instead of KVM
)
```

### "Could not initialize SDL"

**Cause:** No display available (headless system)

**Fix:** Use `-nographic` or `-display none`
```bash
qemu-system-i386 -kernel test.bin -nographic
```

### "Serial output not captured"

**Cause:** Wrong serial configuration

**Fix:** Use `-serial file:path` instead of `-serial stdio`
```bash
qemu-system-i386 -kernel test.bin -serial file:/tmp/output.log
```

### "GDB connection refused"

**Cause:** QEMU not started with GDB stub

**Fix:** Use `-s` (shorthand for `-gdb tcp::1234`) or `-gdb tcp::PORT`
```bash
qemu-system-i386 -kernel test.bin -s -S  # -S = wait for GDB
```

### "Machine 'virt' not supported"

**Cause:** Architecture mismatch or old QEMU version

**Fix:** Check available machines
```bash
qemu-system-riscv32 -machine help
```

Use correct machine type (e.g., `virt` for RISC-V, `lm3s6965evb` for ARM Cortex-M)

---

## Version Requirements

**Minimum QEMU version:** 6.0.0

**Recommended version:** 8.0.0 or later

**Check version:**
```bash
qemu-system-i386 --version
```

**Why newer is better:**
- Improved RISC-V support (QEMU 7.0+)
- Better GDB integration (QEMU 7.2+)
- Faster emulation (QEMU 8.0+)
- Bug fixes for serial capture (QEMU 8.0+)

---

## Performance Tips

### Faster Emulation

**Enable KVM (Linux only, native x86/ARM only):**
```bash
# Check KVM availability
ls /dev/kvm

# Enable in Simple tests
val config = QemuConfig(
    accel: QemuAccel.Kvm  # 10-50x faster
)
```

**Use TCG JIT (all platforms):**
```bash
# Default, no flag needed (automatically enabled)
qemu-system-i386 -kernel test.bin
```

### Faster Boot Tests

**Reduce timeout for passing tests:**
```simple
val config = BootTestConfig(
    timeout_ms: 1000  # 1 second (default: 5000)
)
```

**Run tests in parallel:**
```bash
# Simple automatically runs slow tests in parallel
simple test test/baremetal/boot_test_spec.spl --parallel
```

---

## Platform-Specific Notes

### Linux

- **KVM:** Available on native x86_64/aarch64, 10-50x speedup
- **Install:** Single command via package manager
- **Permissions:** Add user to `kvm` group for KVM access
  ```bash
  sudo usermod -aG kvm $USER
  # Re-login for changes to take effect
  ```

### macOS

- **Hypervisor.framework:** Not used by default (TCG works well)
- **Homebrew:** Easiest installation method
- **Performance:** TCG emulation ~0.5-2x native speed

### Windows

- **HAXM:** Intel HAXM for acceleration (optional)
- **Installation:** Chocolatey or official installer
- **Path:** Must add `C:\Program Files\qemu` to PATH
- **Performance:** TCG works, HAXM accelerates x86 (not ARM/RISC-V)

---

## CI/CD Integration

### GitHub Actions

```yaml
jobs:
  qemu-tests:
    runs-on: ubuntu-latest

    steps:
      - name: Install QEMU
        run: |
          sudo apt-get update
          sudo apt-get install -y qemu-system-x86 qemu-system-arm qemu-system-misc

      - name: Verify QEMU
        run: |
          qemu-system-i386 --version
          qemu-system-riscv32 --version

      - name: Run boot tests
        run: simple test test/baremetal/boot_test_spec.spl
```

### GitLab CI

```yaml
qemu_tests:
  image: ubuntu:latest
  before_script:
    - apt-get update && apt-get install -y qemu-system-x86 qemu-system-arm qemu-system-misc
  script:
    - qemu-system-i386 --version
    - simple test test/baremetal/boot_test_spec.spl
```

---

## Additional Resources

- **QEMU Documentation:** https://qemu.readthedocs.io/
- **QEMU Wiki:** https://wiki.qemu.org/
- **Download:** https://www.qemu.org/download/
- **Simple Boot Tests:** `test/baremetal/boot_test_spec.spl`
- **Simple QEMU Library:** `src/lib/qemu/mod.spl`

---

## Summary

**Quick setup:**
```bash
# Linux (Ubuntu/Debian)
sudo apt-get install qemu-system-x86 qemu-system-arm qemu-system-misc

# macOS
brew install qemu

# Windows
choco install qemu
```

**Verify:**
```bash
qemu-system-i386 --version
qemu-system-riscv32 --version
```

**Test with Simple:**
```bash
simple test test/baremetal/boot_test_spec.spl
```

All done! QEMU is now ready for Simple bare-metal development.
