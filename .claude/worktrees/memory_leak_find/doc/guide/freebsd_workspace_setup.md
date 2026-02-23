# FreeBSD Workspace Setup Guide

Complete guide for setting up a FreeBSD workspace for Simple compiler development and testing via QEMU.

---

## Overview

This guide covers:
1. **FreeBSD VM setup** - QEMU-based FreeBSD development environment
2. **Native bootstrap** - Building Simple compiler on FreeBSD from scratch
3. **Cross-compilation** - Building FreeBSD binaries from Linux
4. **Testing infrastructure** - Running Simple tests on FreeBSD

---

## Quick Start

### 1. Setup FreeBSD VM (from Linux host)

```bash
# Download and configure FreeBSD VM image
bin/release/simple scripts/setup_freebsd_vm.spl

# Start FreeBSD VM (interactive)
~/vms/freebsd/start-freebsd.sh

# Or start in background
~/vms/freebsd/start-freebsd-daemon.sh
```

### 2. Bootstrap Simple on FreeBSD (native)

**Inside FreeBSD VM:**

```bash
# Install prerequisites
pkg install cmake llvm gmake git

# Clone Simple repository
git clone https://github.com/yourorg/simple.git
cd simple

# Bootstrap from scratch (native FreeBSD build)
./scripts/bootstrap/bootstrap-from-scratch.sh --target=freebsd-x86_64

# Verify
bin/simple --version
bin/simple build
bin/simple test
```

### 3. Test FreeBSD from Linux (via QEMU)

**On Linux host:**

```bash
# Run FreeBSD multi-file compilation test
bin/release/simple scripts/test_freebsd_qemu.spl
```

---

## FreeBSD VM Setup (Detailed)

### Prerequisites

**Linux host requirements:**
- QEMU x86_64 emulator (`qemu-system-x86_64`)
- At least 10GB free disk space
- 4GB+ RAM available for VM
- Network access (for downloading FreeBSD image)

**Install QEMU:**

```bash
# Ubuntu/Debian
sudo apt-get install qemu-system-x86 qemu-utils

# Fedora/RHEL
sudo dnf install qemu-system-x86

# Arch
sudo pacman -S qemu-full

# macOS
brew install qemu
```

### Automated Setup

**Run the setup script:**

```bash
bin/release/simple scripts/setup_freebsd_vm.spl
```

**What it does:**
1. Creates `~/vms/freebsd/` directory
2. Downloads FreeBSD 14.3-RELEASE VM image (~600MB compressed)
3. Extracts qcow2 disk image
4. Creates VM start scripts (interactive + daemon)

**Location:** `~/vms/freebsd/`

**Files created:**
- `FreeBSD-14.3-RELEASE-amd64.qcow2` - VM disk image
- `start-freebsd.sh` - Interactive VM (serial console)
- `start-freebsd-daemon.sh` - Background VM (SSH only)

### Manual Setup

**Download FreeBSD VM image manually:**

```bash
mkdir -p ~/vms/freebsd
cd ~/vms/freebsd

# Download FreeBSD 14.3 VM image
wget https://download.freebsd.org/releases/VM-IMAGES/14.3-RELEASE/amd64/Latest/FreeBSD-14.3-RELEASE-amd64.qcow2.xz

# Extract
unxz FreeBSD-14.3-RELEASE-amd64.qcow2.xz
```

**Start VM manually:**

```bash
# Start with SSH forwarding (port 2222 → VM port 22)
qemu-system-x86_64 \
  -machine type=q35,accel=kvm:tcg \
  -cpu host -smp 4 -m 4G \
  -drive file=FreeBSD-14.3-RELEASE-amd64.qcow2,if=virtio,format=qcow2 \
  -netdev user,id=net0,hostfwd=tcp::2222-:22 \
  -device virtio-net-pci,netdev=net0 \
  -display none -serial mon:stdio
```

### First-Time VM Configuration

**Login to FreeBSD:**

```bash
# SSH from host
ssh -p 2222 root@localhost

# Or use serial console (if started interactively)
# Default login: root (no password or password: root)
```

**Inside FreeBSD, configure:**

```bash
# 1. Set root password
passwd

# 2. Enable SSH
echo 'sshd_enable="YES"' >> /etc/rc.conf
service sshd start

# 3. Enable Linuxulator (for running Linux Simple binary)
kldload linux64
sysrc linux_enable="YES"
pkg install linux-c7

# 4. Install development tools
pkg install cmake llvm gmake git wget

# 5. Configure package manager for faster downloads (optional)
mkdir -p /usr/local/etc/pkg/repos
echo 'FreeBSD: { url: "pkg+http://pkg.FreeBSD.org/${ABI}/latest" }' > /usr/local/etc/pkg/repos/FreeBSD.conf
```

**Verify SSH access:**

```bash
# From Linux host
ssh -p 2222 root@localhost 'uname -a'
# Output: FreeBSD freebsd 14.3-RELEASE FreeBSD 14.3-RELEASE releng/14.3-n256807-cb76ae9e1e21 GENERIC amd64
```

---

## Native FreeBSD Bootstrap

Build Simple compiler **natively on FreeBSD** (no cross-compilation).

### Prerequisites

**Inside FreeBSD VM:**

```bash
# Install build tools
pkg install cmake llvm gmake git

# Verify versions
clang++ --version  # Should be 17.0+
cmake --version    # Should be 3.20+
gmake --version    # GNU Make 4.0+
```

### Bootstrap Process

**Clone and build:**

```bash
# Clone repository
git clone https://github.com/yourorg/simple.git
cd simple

# Run FreeBSD-specific bootstrap
./scripts/bootstrap/bootstrap-from-scratch.sh --target=freebsd-x86_64
```

**Bootstrap steps:**
1. **Build seed compiler** - cmake compiles `src/compiler_seed/seed.cpp` → `seed_cpp`
2. **Transpile compiler** - `seed_cpp` transpiles `.spl` → `.cpp`
3. **Compile Core1** - clang++ compiles C++ + runtime → minimal compiler
4. **Self-host Core2** - Core1 recompiles itself (verification)
5. **Build Full1** - Core2 compiles full Simple compiler
6. **Verify reproducibility** - Full1 recompiles itself → Full2 (should match)
7. **Install** - Copy binary to `bin/simple`

**Options:**

```bash
# Skip verification (faster)
./scripts/bootstrap/bootstrap-from-scratch.sh --target=freebsd-x86_64 --skip-verify

# Use specific compiler
./scripts/bootstrap/bootstrap-from-scratch.sh --target=freebsd-x86_64 --cc=clang++

# Custom output location
./scripts/bootstrap/bootstrap-from-scratch.sh --target=freebsd-x86_64 --output=/usr/local/bin/simple

# Parallel jobs
./scripts/bootstrap/bootstrap-from-scratch.sh --target=freebsd-x86_64 --jobs=8

# Keep build artifacts
./scripts/bootstrap/bootstrap-from-scratch.sh --target=freebsd-x86_64 --keep-artifacts

# Verbose output
./scripts/bootstrap/bootstrap-from-scratch.sh --target=freebsd-x86_64 --verbose
```

### Verify Installation

```bash
# Check version
bin/simple --version

# Build compiler
bin/simple build

# Run tests
bin/simple test

# Run specific test
bin/simple test test/std/string_spec.spl
```

### Troubleshooting

**"clang++ not found"**

```bash
# FreeBSD base system includes clang
pkg install llvm
```

**"gmake not found"**

```bash
# FreeBSD uses BSD make by default, need GNU make
pkg install gmake
```

**"cmake not found"**

```bash
pkg install cmake
```

**"Hash mismatch in verification"**

This is expected if:
- Compiler optimizations differ between stages
- Non-deterministic code generation

Skip verification if acceptable:
```bash
./scripts/bootstrap/bootstrap-from-scratch.sh --target=freebsd-x86_64 --skip-verify
```

---

## Cross-Compilation (Linux → FreeBSD)

Build FreeBSD binaries **from Linux host** using cross-compilation.

### Prerequisites

**On Linux:**

```bash
# Install cross-compilation tools
sudo apt-get install clang lld

# Verify
clang++ --version  # Should support --target=x86_64-unknown-freebsd
```

### FreeBSD Sysroot Setup

**Extract sysroot from FreeBSD VM:**

```bash
# On FreeBSD VM, create sysroot tarball
tar -czf /tmp/freebsd-sysroot.tar.gz \
    /usr/include \
    /usr/lib \
    /lib

# Copy to Linux host
scp -P 2222 root@localhost:/tmp/freebsd-sysroot.tar.gz ~/

# On Linux, extract sysroot
sudo mkdir -p /opt/sysroots/freebsd-x86_64
cd /opt/sysroots/freebsd-x86_64
sudo tar -xzf ~/freebsd-sysroot.tar.gz --strip-components=1
```

**Or use minimal sysroot (for CI):**

```bash
# Create minimal sysroot
mkdir -p /tmp/freebsd-sysroot/usr/include
mkdir -p /tmp/freebsd-sysroot/usr/lib

# Copy essential headers/libs from FreeBSD base
# (Manual process - copy from FreeBSD installation)
```

### Cross-Compile Simple

**Using CMake toolchain:**

```bash
# Build seed compiler with FreeBSD toolchain
cd build
cmake ../seed \
    -DCMAKE_TOOLCHAIN_FILE=../src/compiler_seed/cmake/toolchains/freebsd-x86_64.cmake \
    -DCMAKE_BUILD_TYPE=Release

make -j$(nproc)
```

**Verify binary:**

```bash
# Check binary format
file build/seed_cpp
# Output: build/seed_cpp: ELF 64-bit LSB executable, x86-64, FreeBSD

# Copy to FreeBSD VM and test
scp -P 2222 build/seed_cpp root@localhost:/tmp/
ssh -p 2222 root@localhost '/tmp/seed_cpp --version'
```

---

## Testing Infrastructure

### Automated FreeBSD Testing

**Run from Linux host:**

```bash
# Full multi-file compilation test
bin/release/simple scripts/test_freebsd_qemu.spl
```

**What it does:**
1. Starts FreeBSD VM (if not running)
2. Waits for SSH availability
3. Copies Simple bootstrap binary to VM
4. Copies test sources (3-file dependency chain)
5. Runs native compilation inside VM
6. Executes binary and verifies output
7. Reports results

**Test structure:**

```simple
base.spl:
  fn square(x: i64) -> i64: x * x
  export square

mid.spl:
  use base.{square}
  fn sum_of_squares(a, b): square(a) + square(b)
  export sum_of_squares

main.spl:
  use mid.{sum_of_squares}
  fn main(): print "{sum_of_squares(3, 4)}"  # Outputs: 25
```

**Expected output:** `25` (3² + 4² = 9 + 16)

### Manual Testing

**SSH into FreeBSD VM:**

```bash
# Start VM
~/vms/freebsd/start-freebsd-daemon.sh

# SSH
ssh -p 2222 root@localhost

# Inside VM, run tests
cd /path/to/simple
bin/simple test
```

### CI/CD Integration

**GitHub Actions example:**

```yaml
jobs:
  test-freebsd:
    runs-on: ubuntu-latest
    steps:
      - name: Install QEMU
        run: sudo apt-get install -y qemu-system-x86

      - name: Setup FreeBSD VM
        run: bin/release/simple scripts/setup_freebsd_vm.spl

      - name: Test FreeBSD
        run: bin/release/simple scripts/test_freebsd_qemu.spl
        timeout-minutes: 10
```

---

## VM Management

### Start/Stop VM

**Start VM (background):**

```bash
~/vms/freebsd/start-freebsd-daemon.sh
```

**Check if running:**

```bash
# Check PID file
cat /tmp/freebsd-qemu.pid

# Or check process
ps aux | grep qemu-system-x86_64
```

**Stop VM:**

```bash
# Kill gracefully
kill $(cat /tmp/freebsd-qemu.pid)

# Or force stop
pkill -f "qemu-system-x86_64.*freebsd"
```

### Programmatic VM Control

**Using qemu_manager.spl:**

```simple
use app.vm.qemu_manager.{freebsd_config, vm_start, vm_stop, vm_is_running, vm_exec}

fn main():
    val config = freebsd_config()

    # Start VM
    if not vm_start(config):
        print "Failed to start VM"
        return

    # Check status
    if vm_is_running(config):
        print "VM is running"

    # Execute command
    val (out, err, exit) = vm_exec(config, "uname -a")
    print out

    # Stop VM
    vm_stop(config)
```

### SSH Without Password

**Generate SSH key on Linux host:**

```bash
ssh-keygen -t ed25519 -f ~/.ssh/freebsd_vm -N ""
```

**Copy to FreeBSD VM:**

```bash
ssh-copy-id -i ~/.ssh/freebsd_vm -p 2222 root@localhost
```

**Configure SSH config:**

```bash
# Add to ~/.ssh/config
cat >> ~/.ssh/config <<EOF
Host freebsd-vm
    HostName localhost
    Port 2222
    User root
    IdentityFile ~/.ssh/freebsd_vm
    StrictHostKeyChecking no
    UserKnownHostsFile /dev/null
EOF
```

**Use:**

```bash
ssh freebsd-vm uname -a
scp file.txt freebsd-vm:/tmp/
```

---

## FreeBSD-Specific Notes

### Differences from Linux

**Package manager:**
- Linux: `apt`/`dnf`/`pacman`
- FreeBSD: `pkg install`

**Make:**
- Linux: `make` (GNU Make)
- FreeBSD: `make` (BSD Make) - use `gmake` for GNU Make

**Linuxulator:**
- FreeBSD can run Linux binaries via compatibility layer
- Enable: `kldload linux64`
- Use case: Run pre-built Linux Simple binary on FreeBSD

**File paths:**
- Linux: `/usr/bin`, `/usr/lib`
- FreeBSD: Same, but also `/usr/local/bin`, `/usr/local/lib`

**SHA256:**
- Linux: `sha256sum file`
- FreeBSD: `sha256 file` or `sha256 -q file` (quiet)

### Compiler Differences

**Default compiler:**
- Linux: usually `gcc`
- FreeBSD: `clang++` (LLVM in base system)

**System headers:**
- FreeBSD requires `#define __BSD_VISIBLE 1` for POSIX extensions
- Handled by `src/compiler_seed/platform/platform_freebsd.h`

**Linking:**
- FreeBSD uses `lld` (LLVM linker) by default
- Compatible with Linux linking, minor ABI differences

---

## Performance

### VM Performance

**KVM acceleration (Linux host only):**

```bash
# Check KVM availability
ls /dev/kvm

# VM automatically uses KVM if available
# Fallback to TCG (software emulation) if not
```

**Performance tiers:**
1. **Native FreeBSD** - 1.0x (baseline)
2. **FreeBSD in QEMU + KVM** - 0.7-0.9x (10-30% slower)
3. **FreeBSD in QEMU + TCG** - 0.1-0.3x (3-10x slower)

**Optimization tips:**
- Use KVM if available (requires `/dev/kvm`)
- Allocate more CPU cores: `-smp 8`
- Increase RAM: `-m 8G`
- Use virtio drivers (already configured)

### Build Performance

**Bootstrap times (FreeBSD x86_64, 4 cores, 4GB RAM):**

| Stage | Time (KVM) | Time (TCG) |
|-------|------------|------------|
| Seed build | ~10s | ~30s |
| Core compilation | ~20s | ~60s |
| Full build | ~30s | ~120s |
| **Total** | **~60s** | **~210s** |

**Recommendations:**
- Use `--skip-verify` for faster dev builds (~40% faster)
- Use `--jobs=N` to match CPU cores
- Run on native FreeBSD for max speed

---

## Troubleshooting

### VM Won't Start

**Symptom:** `start-freebsd-daemon.sh` exits without creating PID file

**Checks:**

```bash
# 1. Check QEMU is installed
which qemu-system-x86_64

# 2. Check image exists
ls ~/vms/freebsd/FreeBSD-14.3-RELEASE-amd64.qcow2

# 3. Check port 2222 is free
netstat -tuln | grep 2222

# 4. Try interactive mode
~/vms/freebsd/start-freebsd.sh
```

**Fix:**

```bash
# Kill any stale QEMU processes
pkill -f "qemu-system.*freebsd"
rm -f /tmp/freebsd-qemu.pid

# Retry
~/vms/freebsd/start-freebsd-daemon.sh
```

### SSH Timeout

**Symptom:** `vm_wait_ssh` times out

**Checks:**

```bash
# 1. VM is running
ps aux | grep qemu-system-x86_64

# 2. SSH port is forwarded
netstat -tuln | grep 2222

# 3. sshd is running in VM (use serial console)
service sshd status
```

**Fix:**

```bash
# Inside VM (via serial console)
echo 'sshd_enable="YES"' >> /etc/rc.conf
service sshd start
```

### Bootstrap Fails on FreeBSD

**Symptom:** `bootstrap-from-scratch.sh --target=freebsd-x86_64` fails at Step 1/3

**Checks:**

```bash
# 1. Prerequisites
pkg install cmake llvm gmake

# 2. Verify tools
clang++ --version
cmake --version
gmake --version

# 3. Check disk space
df -h

# 4. Re-run with verbose
./scripts/bootstrap/bootstrap-from-scratch.sh --target=freebsd-x86_64 --verbose
```

**Common errors:**

- **"gmake: command not found"** → `pkg install gmake`
- **"sha256: command not found"** → FreeBSD should have this by default
- **"seed.cpp: No such file"** → Run from project root directory

### Linuxulator Not Working

**Symptom:** Linux Simple binary fails in FreeBSD

**Check:**

```bash
# Inside FreeBSD VM
kldstat | grep linux

# If not loaded:
kldload linux64
pkg install linux-c7
```

**Test:**

```bash
# Try running Linux binary
/tmp/simple-bootstrap --version
```

---

## References

### Project Files

- **VM Setup:** `scripts/setup_freebsd_vm.spl`
- **FreeBSD Test:** `scripts/test_freebsd_qemu.spl`
- **Bootstrap:** `scripts/bootstrap/bootstrap-from-scratch.sh --target=freebsd-x86_64`
- **VM Manager:** `src/app/vm/qemu_manager.spl`
- **Toolchain:** `src/compiler_seed/cmake/toolchains/freebsd-x86_64.cmake`
- **Platform Header:** `src/compiler_seed/platform/platform_freebsd.h`

### External Documentation

- **FreeBSD Handbook:** https://docs.freebsd.org/en/books/handbook/
- **FreeBSD VM Images:** https://download.freebsd.org/releases/VM-IMAGES/
- **QEMU Documentation:** https://qemu.readthedocs.io/
- **Linuxulator Guide:** https://docs.freebsd.org/en/books/handbook/linuxemu/

---

## Summary

**Quick setup:**

```bash
# 1. Setup FreeBSD VM
bin/release/simple scripts/setup_freebsd_vm.spl

# 2. Test FreeBSD
bin/release/simple scripts/test_freebsd_qemu.spl
```

**Inside FreeBSD VM:**

```bash
# 1. Install tools
pkg install cmake llvm gmake git

# 2. Bootstrap
./scripts/bootstrap/bootstrap-from-scratch.sh --target=freebsd-x86_64

# 3. Verify
bin/simple --version
bin/simple test
```

**VM management:**

```bash
# Start
~/vms/freebsd/start-freebsd-daemon.sh

# SSH
ssh -p 2222 root@localhost

# Stop
kill $(cat /tmp/freebsd-qemu.pid)
```

FreeBSD workspace ready! 🎉
