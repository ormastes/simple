# FreeBSD Workspace for Simple Compiler

Complete FreeBSD development and testing environment for the Simple compiler.

---

## 🚀 Quick Start

### From Linux Host (Recommended)

```bash
# 1. Setup FreeBSD VM
bin/release/simple scripts/setup_freebsd_vm.spl

# 2. Start VM
~/vms/freebsd/start-freebsd-daemon.sh

# 3. Test FreeBSD compilation
bin/release/simple scripts/test_freebsd_qemu.spl
```

### Native FreeBSD

```bash
# 1. Install prerequisites
pkg install cmake llvm gmake git

# 2. Clone repository
git clone https://github.com/yourorg/simple.git
cd simple

# 3. Bootstrap from scratch
./scripts/bootstrap/bootstrap-from-scratch.sh --target=freebsd-x86_64

# 4. Verify
bin/simple --version
bin/simple test
```

---

## 📚 Documentation

| Guide | Purpose |
|-------|---------|
| **[FreeBSD Workspace Setup](doc/guide/freebsd_workspace_setup.md)** | Complete setup guide (VM, bootstrap, cross-compile, testing) |
| **[FreeBSD Quick Reference](doc/guide/freebsd_quick_reference.md)** | Command cheat sheet and tips |
| **[QEMU Setup Guide](doc/guide/qemu_setup.md)** | QEMU installation and configuration |

---

## 🛠️ Tools & Scripts

### VM Management

| Script | Purpose |
|--------|---------|
| `scripts/setup_freebsd_vm.spl` | Download and configure FreeBSD VM image |
| `~/vms/freebsd/start-freebsd.sh` | Start VM (interactive, serial console) |
| `~/vms/freebsd/start-freebsd-daemon.sh` | Start VM (background, SSH only) |

**Quick commands:**

```bash
# Setup
bin/release/simple scripts/setup_freebsd_vm.spl

# Start
~/vms/freebsd/start-freebsd-daemon.sh

# SSH
ssh -p 2222 root@localhost

# Stop
kill $(cat /tmp/freebsd-qemu.pid)
```

### Bootstrap Scripts

| Script | Platform |
|--------|----------|
| `scripts/bootstrap/bootstrap-from-scratch.sh --target=freebsd-x86_64` | **FreeBSD native** (this file!) |
| `scripts/bootstrap/bootstrap-from-scratch.sh` | Linux/macOS |
| `scripts/bootstrap/bootstrap-from-scratch.bat` | Windows |

**Usage:**

```bash
# FreeBSD (native)
./scripts/bootstrap/bootstrap-from-scratch.sh --target=freebsd-x86_64

# Options
./scripts/bootstrap/bootstrap-from-scratch.sh --target=freebsd-x86_64 --skip-verify --jobs=8
```

### Testing Scripts

| Script | Purpose |
|--------|---------|
| `scripts/test_freebsd_qemu.spl` | Test Simple compilation on FreeBSD via QEMU |
| `scripts/test_macos_qemu.spl` | Test Simple compilation on macOS via QEMU |
| `scripts/test_windows_vm.spl` | Test Simple compilation on Windows via QEMU |

**Example:**

```bash
# Test FreeBSD multi-file compilation
bin/release/simple scripts/test_freebsd_qemu.spl
```

---

## 🔧 VM Configuration

### Default Settings

| Setting | Value |
|---------|-------|
| Image | FreeBSD 14.3-RELEASE (amd64) |
| Location | `~/vms/freebsd/FreeBSD-14.3-RELEASE-amd64.qcow2` |
| SSH Port | 2222 (host) → 22 (VM) |
| RAM | 4GB (interactive), 2GB (daemon) |
| CPUs | 4 (interactive), 2 (daemon) |
| Acceleration | KVM (if available), TCG (fallback) |

### Customization

Edit VM start scripts:

```bash
# Interactive
nano ~/vms/freebsd/start-freebsd.sh

# Daemon
nano ~/vms/freebsd/start-freebsd-daemon.sh
```

**Example: Increase RAM to 8GB:**

```bash
# Change: -m 4G
# To:     -m 8G
```

**Example: Add port forwarding (HTTP 8080):**

```bash
# Add to -netdev line:
-netdev user,id=net0,hostfwd=tcp::2222-:22,hostfwd=tcp::8080-:80
```

---

## 🧪 Testing Workflow

### Automated Testing (Recommended)

```bash
# From Linux host
bin/release/simple scripts/test_freebsd_qemu.spl
```

**What it does:**
1. Starts FreeBSD VM (if not running)
2. Waits for SSH
3. Copies Simple binary + test sources
4. Compiles multi-file project inside VM
5. Executes and verifies output
6. Reports results

**Test case:** 3-file dependency chain
- `base.spl`: `square(x) = x * x`
- `mid.spl`: `sum_of_squares(a, b) = square(a) + square(b)`
- `main.spl`: `print sum_of_squares(3, 4)` → Expected: `25`

### Manual Testing

```bash
# 1. SSH into VM
ssh -p 2222 root@localhost

# 2. Inside VM
cd /path/to/simple

# 3. Build
bin/simple build

# 4. Test
bin/simple test

# 5. Specific test
bin/simple test test/std/array_spec.spl
```

---

## 🏗️ Bootstrap Process

### Native FreeBSD Bootstrap

**Script:** `scripts/bootstrap/bootstrap-from-scratch.sh --target=freebsd-x86_64`

**Steps:**

1. **Prerequisites** - Check cmake, clang++, gmake
2. **Build seed** - Compile C++ seed transpiler
3. **Transpile core** - Generate C++ from `.spl`
4. **Compile Core1** - Build minimal compiler
5. **Self-host Core2** - Verify Core1 works
6. **Build Full1** - Compile complete compiler
7. **Verify reproducible** - Full1 recompiles itself (should match)
8. **Install** - Copy to `bin/simple`

**Typical time:** ~60 seconds (KVM), ~210 seconds (TCG)

**Options:**

```bash
--skip-verify     # Skip Core2 + Full2 verification (~40% faster)
--jobs=N          # Parallel jobs (default: auto-detect CPU count)
--cc=PATH         # Use specific C++ compiler (default: clang++)
--output=PATH     # Install location (default: bin/simple)
--keep-artifacts  # Keep build/ directory
--verbose         # Show all command output
```

### Cross-Compilation (Linux → FreeBSD)

**Setup sysroot:**

```bash
# On FreeBSD VM
tar -czf /tmp/freebsd-sysroot.tar.gz /usr/include /usr/lib /lib

# On Linux host
scp -P 2222 root@localhost:/tmp/freebsd-sysroot.tar.gz ~/
sudo mkdir -p /opt/sysroots/freebsd-x86_64
cd /opt/sysroots/freebsd-x86_64
sudo tar -xzf ~/freebsd-sysroot.tar.gz --strip-components=1
```

**Build:**

```bash
cmake seed/ \
    -DCMAKE_TOOLCHAIN_FILE=src/compiler_seed/cmake/toolchains/freebsd-x86_64.cmake \
    -DCMAKE_BUILD_TYPE=Release

make -j$(nproc)
```

---

## 📦 Prerequisites

### Linux Host (for VM)

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

### FreeBSD Native

```bash
# Development tools
pkg install cmake llvm gmake git

# Verify versions
clang++ --version  # 17.0+
cmake --version    # 3.20+
gmake --version    # 4.0+
```

---

## 🔍 Troubleshooting

### VM Issues

**VM won't start:**

```bash
# Check QEMU
which qemu-system-x86_64

# Check image exists
ls ~/vms/freebsd/FreeBSD-14.3-RELEASE-amd64.qcow2

# Kill stale processes
pkill -f "qemu-system.*freebsd"
rm -f /tmp/freebsd-qemu.pid

# Retry
~/vms/freebsd/start-freebsd-daemon.sh
```

**SSH timeout:**

```bash
# Check VM is running
ps aux | grep qemu-system-x86_64

# Check port forwarding
netstat -tuln | grep 2222

# Inside VM (serial console), enable SSH
service sshd status
echo 'sshd_enable="YES"' >> /etc/rc.conf
service sshd start
```

### Bootstrap Issues

**"gmake: command not found":**

```bash
pkg install gmake
```

**"clang++: command not found":**

```bash
pkg install llvm
```

**Hash mismatch in verification:**

This is sometimes expected. Skip verification:

```bash
./scripts/bootstrap/bootstrap-from-scratch.sh --target=freebsd-x86_64 --skip-verify
```

### Linuxulator Issues

**Linux binary fails in FreeBSD:**

```bash
# Load Linux compatibility
kldload linux64
pkg install linux-c7

# Verify
kldstat | grep linux
```

---

## 🎯 Use Cases

### Development

**Scenario:** Test Simple code on FreeBSD

```bash
# 1. Start VM
~/vms/freebsd/start-freebsd-daemon.sh

# 2. SSH and develop
ssh -p 2222 root@localhost
cd /path/to/simple

# 3. Edit, build, test
vi src/app/cli/main.spl
bin/simple build
bin/simple test
```

### CI/CD

**GitHub Actions example:**

```yaml
jobs:
  test-freebsd:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v3

      - name: Install QEMU
        run: sudo apt-get install -y qemu-system-x86

      - name: Setup FreeBSD VM
        run: bin/release/simple scripts/setup_freebsd_vm.spl

      - name: Test FreeBSD
        run: bin/release/simple scripts/test_freebsd_qemu.spl
        timeout-minutes: 10
```

### Cross-Platform Testing

**Test on all platforms:**

```bash
# Linux (native)
bin/simple test

# FreeBSD (QEMU)
bin/release/simple scripts/test_freebsd_qemu.spl

# macOS (QEMU)
bin/release/simple scripts/test_macos_qemu.spl

# Windows (QEMU)
bin/release/simple scripts/test_windows_vm.spl
```

---

## 📊 Performance

### VM Performance Tiers

| Mode | Speed vs Native | Use Case |
|------|-----------------|----------|
| **FreeBSD Native** | 1.0x | Production, development |
| **QEMU + KVM** | 0.7-0.9x | CI/CD, testing (Linux host) |
| **QEMU + TCG** | 0.1-0.3x | macOS, nested VM |

### Bootstrap Times (FreeBSD x86_64, 4 cores)

| Stage | KVM | TCG |
|-------|-----|-----|
| Seed build | ~10s | ~30s |
| Core compile | ~20s | ~60s |
| Full build | ~30s | ~120s |
| **Total** | **~60s** | **~210s** |

**Optimization:**
- Use `--skip-verify` for ~40% speedup
- Allocate more cores: edit VM scripts, increase `-smp`
- Use KVM if available (Linux host only)

---

## 🗂️ File Structure

```
simple/
├── scripts/
│   ├── bootstrap-from-scratch.sh --target=freebsd-x86_64  # FreeBSD native bootstrap (NEW!)
│   ├── setup_freebsd_vm.spl               # VM setup script
│   └── test_freebsd_qemu.spl              # FreeBSD testing script
├── seed/
│   ├── platform/
│   │   └── platform_freebsd.h             # FreeBSD platform header
│   └── cmake/toolchains/
│       ├── freebsd-x86_64.cmake           # Cross-compile toolchain
│       └── freebsd-x86.cmake              # 32-bit FreeBSD
├── src/app/vm/
│   └── qemu_manager.spl                   # VM lifecycle management
└── doc/guide/
    ├── freebsd_workspace_setup.md         # Complete setup guide (NEW!)
    ├── freebsd_quick_reference.md         # Command cheat sheet (NEW!)
    └── qemu_setup.md                      # QEMU installation guide
```

---

## 🌐 Related Documentation

- **[QEMU Setup Guide](doc/guide/qemu_setup.md)** - Install QEMU for all architectures
- **[macOS Workspace](doc/guide/macos_workspace_setup.md)** - macOS VM setup
- **[Windows Workspace](doc/guide/windows_workspace_setup.md)** - Windows VM setup
- **[FreeBSD Handbook](https://docs.freebsd.org/en/books/handbook/)** - Official FreeBSD docs

---

## 🤝 Contributing

### Report Issues

- VM won't start? → Include QEMU version, host OS
- Bootstrap fails? → Include FreeBSD version, error message
- Tests fail? → Include test output, system info

### Improvements

- Optimize bootstrap script
- Add more test cases
- Improve VM configuration
- Update documentation

---

## 📝 Notes

### FreeBSD vs Linux

**Key differences:**
- Package manager: `pkg` (not `apt`/`dnf`)
- Make: `gmake` for GNU make (BSD make is default)
- SHA256: `sha256 file` (not `sha256sum`)
- Compiler: `clang++` in base (not `gcc`)

**See:** [FreeBSD Quick Reference](doc/guide/freebsd_quick_reference.md)

### Linuxulator

FreeBSD can run Linux binaries via Linuxulator:

```bash
# Enable
kldload linux64
pkg install linux-c7

# Run Linux Simple binary
/path/to/linux-simple --version
```

**Use case:** Test pre-built Linux binaries on FreeBSD

---

## ✅ Checklist

### Initial Setup

- [ ] Install QEMU on host
- [ ] Run `scripts/setup_freebsd_vm.spl`
- [ ] Start VM: `~/vms/freebsd/start-freebsd-daemon.sh`
- [ ] Configure VM (SSH, packages)
- [ ] Test: `scripts/test_freebsd_qemu.spl`

### Native Bootstrap

- [ ] SSH into FreeBSD VM
- [ ] Install: `pkg install cmake llvm gmake git`
- [ ] Clone Simple repository
- [ ] Run: `./scripts/bootstrap/bootstrap-from-scratch.sh --target=freebsd-x86_64`
- [ ] Verify: `bin/simple --version`

### Testing

- [ ] Build: `bin/simple build`
- [ ] Test: `bin/simple test`
- [ ] Lint: `bin/simple build lint`

---

## 🎉 Summary

**FreeBSD workspace provides:**
- ✅ QEMU-based FreeBSD VM for testing
- ✅ Native FreeBSD bootstrap script
- ✅ Automated testing infrastructure
- ✅ Cross-compilation support
- ✅ Complete documentation

**Get started now:**

```bash
bin/release/simple scripts/setup_freebsd_vm.spl
bin/release/simple scripts/test_freebsd_qemu.spl
```

Happy FreeBSD development! 🐡
