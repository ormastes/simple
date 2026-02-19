# FreeBSD Bootstrap with QEMU — Quick Reference

Complete FreeBSD bootstrap setup using QEMU virtualization from Linux hosts.

## Quick Start (5 Steps)

```bash
# 1. Install QEMU and dependencies (Ubuntu/Debian)
sudo apt install qemu-system-x86 qemu-utils rsync openssh-client wget xz-utils

# 2. Download FreeBSD 14.3 VM image (~5 GB download)
mkdir -p build/freebsd/vm && cd build/freebsd/vm
wget https://download.freebsd.org/releases/amd64/14.3-RELEASE/FreeBSD-14.3-RELEASE-amd64.qcow2.xz
xz -d FreeBSD-14.3-RELEASE-amd64.qcow2.xz
cd ../../..

# 3. Test QEMU setup (recommended)
./scripts/test-freebsd-qemu-setup.sh

# 4. Run full bootstrap in QEMU VM
./scripts/bootstrap/bootstrap-from-scratch.sh --platform=freebsd

# 5. Verify FreeBSD binary
file bin/simple
# Expected: ELF 64-bit LSB executable, x86-64, version 1 (FreeBSD)
```

## What Gets Built

The FreeBSD bootstrap process creates:

1. **seed_cpp** - C++ seed transpiler (FreeBSD ELF)
2. **core1** - Minimal native compiler (~326K FreeBSD ELF)
3. **core2** - Self-hosted compiler (reproducibility check)
4. **full1** - Complete compiler (~33 MB FreeBSD ELF)
5. **full2** - Rebuilt compiler (must match full1 hash)
6. **bin/simple** - Final verified FreeBSD binary

**Total build time:** 3-6 minutes on modern hardware with KVM

## System Requirements

**Linux Host:**
- Ubuntu 22.04 LTS, Fedora 38+, or similar
- 8GB+ RAM (4GB for VM, 4GB for host)
- 20GB+ disk space (5GB VM + 10GB build artifacts + 5GB safety margin)
- Intel VT-x or AMD-V for KVM acceleration (optional but recommended)

**FreeBSD VM:**
- FreeBSD 14.3-RELEASE (auto-downloaded)
- Clang 19+ (included in base system)
- CMake 3.20+, Ninja or GNU Make
- C++20 support (enforced in CMakeLists.txt)

## File Structure

```
build/freebsd/vm/
  FreeBSD-14.3-RELEASE-amd64.qcow2  # QEMU VM image (~5-8 GB)
  qemu.pid                           # VM process ID (when running)

scripts/
  bootstrap-from-scratch.sh --target=freebsd-x86_64  # FreeBSD-native bootstrap (521 lines)
  test-freebsd-qemu-setup.sh         # QEMU setup verification
  configure_freebsd_vm_ssh.sh        # SSH configuration helper

doc/
  build/bootstrap_pipeline.md        # Complete bootstrap documentation
  guide/freebsd_qemu_bootstrap.md    # Step-by-step QEMU guide
```

## Common Commands

```bash
# Quick test (VM start + SSH connectivity only)
./scripts/test-freebsd-qemu-setup.sh --quick

# Full test (includes compilation verification)
./scripts/test-freebsd-qemu-setup.sh --full

# Download FreeBSD VM if missing
./scripts/test-freebsd-qemu-setup.sh --download

# Manual bootstrap (step-by-step)
# 1. Start VM
qemu-system-x86_64 \
    -machine accel=kvm:tcg -cpu host -m 4G -smp 4 \
    -drive file=build/freebsd/vm/FreeBSD-14.3-RELEASE-amd64.qcow2,format=qcow2,if=virtio \
    -net nic,model=virtio -net user,hostfwd=tcp::2222-:22 \
    -nographic -daemonize -pidfile build/freebsd/vm/qemu.pid

# 2. Sync project to VM
rsync -az --delete -e "ssh -p 2222 -o StrictHostKeyChecking=no" \
    --exclude='.git' --exclude='build' --exclude='.jj' . freebsd@localhost:~/simple/

# 3. Run bootstrap in VM
ssh -p 2222 freebsd@localhost "cd ~/simple && ./scripts/bootstrap/bootstrap-from-scratch.sh --target=freebsd-x86_64"

# 4. Retrieve binary
rsync -az -e "ssh -p 2222 -o StrictHostKeyChecking=no" \
    freebsd@localhost:~/simple/bin/simple bin/simple

# 5. Stop VM
kill $(cat build/freebsd/vm/qemu.pid)
```

## Toolchain Details

**CMake Configuration (seed/CMakeLists.txt):**
- C++20 standard (line 20: `set(CMAKE_CXX_STANDARD 20)`)
- Auto-detects Clang (preferred over GCC)
- Platform macro: `-DSPL_PLATFORM_FREEBSD`
- Links: `-lpthread -lm` (POSIX threads + math lib)

**FreeBSD-Specific Commands:**
- Hash: `sha256` (not `sha256sum` like Linux)
- Make: `gmake` (GNU Make, not BSD Make)
- CPU count: `sysctl -n hw.ncpu` (not `nproc`)

## Architecture Support

| Architecture | Status | Notes |
|--------------|--------|-------|
| x86-64 | **WORKING** | Primary platform, fully tested |
| arm64 | **WORKING** | Requires ARM hardware or QEMU ARM VM |
| riscv64 | **EXPERIMENTAL** | Requires RISC-V hardware |

## Troubleshooting

**VM won't start:**
```bash
# Check KVM support
ls -l /dev/kvm  # Should exist for KVM acceleration

# Enable KVM module
sudo modprobe kvm-intel  # Intel CPUs
sudo modprobe kvm-amd    # AMD CPUs

# Use TCG if KVM unavailable (slower)
qemu-system-x86_64 -machine accel=tcg ...
```

**SSH connection timeout:**
```bash
# Wait longer (VM boot can take 60-90 seconds)
sleep 60
ssh -p 2222 freebsd@localhost "echo OK"

# Check SSH service
ssh -p 2222 freebsd@localhost "service sshd status"
```

**Out of disk space:**
```bash
# Resize VM disk (+10 GB)
qemu-img resize build/freebsd/vm/FreeBSD-14.3-RELEASE-amd64.qcow2 +10G

# Grow filesystem inside VM
ssh -p 2222 freebsd@localhost "sudo growfs /dev/vtbd0s1a"
```

**Bootstrap fails:**
```bash
# Run with verbose output
ssh -p 2222 freebsd@localhost "cd ~/simple && ./scripts/bootstrap/bootstrap-from-scratch.sh --target=freebsd-x86_64 --verbose"

# Check disk space
ssh -p 2222 freebsd@localhost "df -h"

# Check memory
ssh -p 2222 freebsd@localhost "sysctl hw.physmem"
```

## Performance Tips

**KVM Acceleration (10-20x faster):**
- Requires Intel VT-x or AMD-V CPU features
- Auto-enabled with `-machine accel=kvm:tcg`
- Verify: `lscpu | grep Virtualization`

**Parallel Builds:**
```bash
# Use more CPU cores in VM
ssh -p 2222 freebsd@localhost "cd ~/simple && ./scripts/bootstrap/bootstrap-from-scratch.sh --target=freebsd-x86_64 --jobs=8"
```

**Memory Tuning:**
```bash
# Allocate more memory for faster builds
qemu-system-x86_64 -m 8G ...  # For 16GB+ host systems
```

## CI/CD Integration

Example GitHub Actions workflow:

```yaml
- name: FreeBSD Bootstrap
  run: |
    # Install QEMU
    sudo apt install -y qemu-system-x86 rsync

    # Cache FreeBSD VM
    if [ ! -f build/freebsd/vm/FreeBSD-14.3-RELEASE-amd64.qcow2 ]; then
      wget -q https://download.freebsd.org/releases/amd64/14.3-RELEASE/FreeBSD-14.3-RELEASE-amd64.qcow2.xz
      xz -d FreeBSD-14.3-RELEASE-amd64.qcow2.xz
    fi

    # Run bootstrap
    ./scripts/bootstrap/bootstrap-from-scratch.sh --platform=freebsd

    # Verify
    file bin/simple | grep FreeBSD
```

## Testing in QEMU

After building, you can run basic tests in the FreeBSD VM:

```bash
# Run basic test suite (~80-100 tests)
./scripts/test-freebsd-qemu-basic.sh

# Core tests only (~50 tests, faster)
./scripts/test-freebsd-qemu-basic.sh --core-only

# Skip rebuild if already built
./scripts/test-freebsd-qemu-basic.sh --skip-build

# See detailed output
./scripts/test-freebsd-qemu-basic.sh --verbose

# Manual testing in VM
ssh -p 2222 freebsd@localhost "cd ~/simple && bin/simple test test/unit/compiler_core/"
```

**Expected results:**
- 100% pass rate on core compiler tests
- 30-60 second runtime (excluding build)
- FreeBSD ELF binary verified

**See:** `doc/guide/freebsd_testing_qemu.md` for complete testing guide

## Documentation

- **Complete Guide:** `doc/guide/freebsd_qemu_bootstrap.md`
- **Testing Guide:** `doc/guide/freebsd_testing_qemu.md`
- **Bootstrap Pipeline:** `doc/build/bootstrap_pipeline.md`
- **Native FreeBSD Script:** `scripts/bootstrap/bootstrap-from-scratch.sh --target=freebsd-x86_64`
- **QEMU Setup Test:** `scripts/test-freebsd-qemu-setup.sh`
- **QEMU Basic Test:** `scripts/test-freebsd-qemu-basic.sh`

## Status

- ✅ **Native FreeBSD:** All stages passing on FreeBSD 14.3+
- ✅ **QEMU Integration:** Working on Ubuntu 22.04 LTS + FreeBSD 14.3 VM
- ✅ **Reproducibility:** SHA256 hash verification passing
- ✅ **Self-hosting:** Core compiler successfully recompiles itself
- ✅ **CI/CD Ready:** Can be integrated into GitHub Actions workflows

## Key Features

1. **Automated QEMU Setup** - Auto-detect, start, sync, build, retrieve
2. **Reproducible Builds** - SHA256 verification ensures consistency
3. **Self-Hosting** - Compiler can rebuild itself (core2 check)
4. **Cross-Platform** - Build FreeBSD binaries from Linux hosts
5. **Production Ready** - All stages tested and verified

## Next Steps

1. **Verify Setup:** `./scripts/test-freebsd-qemu-setup.sh`
2. **Run Bootstrap:** `./scripts/bootstrap/bootstrap-from-scratch.sh --platform=freebsd`
3. **Test Binary:** `file bin/simple` (should show "FreeBSD ELF")
4. **Read Docs:** `doc/guide/freebsd_qemu_bootstrap.md`

## Changelog

- **2026-02-15:** Initial FreeBSD QEMU bootstrap implementation
- Tested: Ubuntu 22.04 LTS + FreeBSD 14.3 QEMU VM
- Toolchain: CMake 3.20+, Ninja, Clang 19+, C++20
- Bootstrap time: 3-6 minutes with KVM acceleration
