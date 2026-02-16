# QEMU Bootstrap Scripts

All three bootstrap scripts now support automated FreeBSD builds via QEMU VMs.

## Quick Start

**Linux/macOS:**
```bash
./scripts/bootstrap-from-scratch.sh --qemu-freebsd
```

**Windows:**
```batch
script\bootstrap-from-scratch.bat --qemu-freebsd
```

**Simple:**
```bash
bin/release/simple scripts/bootstrap-multiphase.spl --qemu-freebsd
```

## What Changed

### bootstrap-from-scratch.sh (Linux/macOS)
- ✅ Added `--qemu-freebsd` flag
- ✅ Added `--qemu-vm=PATH` for VM path
- ✅ Added `--qemu-port=N` for SSH port
- ✅ Auto-detects FreeBSD VM in standard locations
- ✅ Starts QEMU with KVM/TCG acceleration
- ✅ Syncs project via rsync
- ✅ Runs FreeBSD bootstrap remotely
- ✅ Retrieves binary via scp

### bootstrap-from-scratch.bat (Windows)
- ✅ Added `--qemu-freebsd` flag
- ✅ Added `--qemu-vm=PATH` for VM path
- ✅ Added `--qemu-port=N` for SSH port
- ✅ Auto-detects FreeBSD VM (Windows paths)
- ✅ Starts QEMU with WHPX/TCG acceleration
- ✅ Runs FreeBSD bootstrap remotely
- ✅ Retrieves binary via scp
- ⚠️ Note: Requires rsync/scp (Cygwin or WinSCP)

### bootstrap-multiphase.spl (Simple Language)
- ✅ Added `--qemu-freebsd` flag
- ✅ Added `--qemu-vm=PATH` for VM path
- ✅ Added `--qemu-port=N` for SSH port
- ✅ New function: `run_qemu_freebsd_bootstrap()`
- ✅ Full VM lifecycle management
- ✅ Project sync with rsync
- ✅ Remote execution and retrieval

## Prerequisites

**Install QEMU:**
- Linux: `sudo apt install qemu-system-x86`
- macOS: `brew install qemu`
- Windows: https://www.qemu.org/download/#windows

**FreeBSD VM Image:**
```bash
# Auto-detected in:
# - build/freebsd/vm/FreeBSD-14.3-RELEASE-amd64.qcow2
# - ~/.qemu/freebsd.qcow2
# - /opt/qemu/freebsd.qcow2

# Download with Simple:
bin/simple scripts/download_qemu.spl freebsd

# Or manually:
wget https://download.freebsd.org/releases/VM-IMAGES/14.3-RELEASE/amd64/Latest/FreeBSD-14.3-RELEASE-amd64.qcow2.xz
unxz FreeBSD-14.3-RELEASE-amd64.qcow2.xz
mkdir -p build/freebsd/vm
mv FreeBSD-14.3-RELEASE-amd64.qcow2 build/freebsd/vm/
```

**SSH Setup (first time):**
```bash
# Start VM manually
qemu-system-x86_64 -m 4G -smp 4 \
  -drive file=build/freebsd/vm/FreeBSD-14.3-RELEASE-amd64.qcow2,format=qcow2 \
  -net nic -net user,hostfwd=tcp::10022-:22 -nographic

# Login as root, then:
pkg install sudo openssh-portable
echo 'sshd_enable="YES"' >> /etc/rc.conf
service sshd start
pw useradd -n freebsd -m -s /bin/sh -G wheel
passwd freebsd
echo '%wheel ALL=(ALL) NOPASSWD: ALL' >> /usr/local/etc/sudoers
# Exit with Ctrl+A then X
```

## Usage Examples

### Basic QEMU Build
```bash
# Auto-detect VM
./scripts/bootstrap-from-scratch.sh --qemu-freebsd
```

### Custom VM Path
```bash
# Linux
./scripts/bootstrap-from-scratch.sh --qemu-freebsd --qemu-vm=/data/vms/freebsd.qcow2

# Windows
script\bootstrap-from-scratch.bat --qemu-freebsd --qemu-vm=D:\VMs\freebsd.qcow2
```

### Custom Port
```bash
# Run on different port (e.g., if 10022 is in use)
./scripts/bootstrap-from-scratch.sh --qemu-freebsd --qemu-port=10023
```

### Combined Options
```bash
# Fast build: skip verification, custom VM, custom port
./scripts/bootstrap-from-scratch.sh \
  --qemu-freebsd \
  --qemu-vm=/opt/vms/freebsd14.qcow2 \
  --qemu-port=10024 \
  --skip-verify \
  --keep-artifacts \
  --verbose
```

### Simple Script
```bash
# Using the .spl version
bin/release/simple scripts/bootstrap-multiphase.spl \
  --qemu-freebsd \
  --no-verify \
  --qemu-port=10022
```

## How It Works

1. **VM Detection**: Checks standard locations or uses `--qemu-vm` path
2. **VM Startup**: Launches QEMU with KVM (or TCG fallback)
3. **SSH Wait**: Waits up to 60 seconds for SSH to be ready
4. **Project Sync**: Uses rsync to copy project to VM (excludes .git, build, etc.)
5. **Remote Build**: Executes `scripts/bootstrap-from-scratch-freebsd.sh` in VM
6. **Binary Retrieval**: Copies built binary back via scp
7. **Complete**: Binary available at `bin/simple` (or `bin/simple.exe` on Windows)

## Options Reference

| Option | Description | Default |
|--------|-------------|---------|
| `--qemu-freebsd` | Enable QEMU FreeBSD build mode | Off |
| `--qemu-vm=PATH` | Path to FreeBSD qcow2 image | Auto-detect |
| `--qemu-port=N` | SSH port for VM access | 10022 |
| `--skip-verify` | Skip reproducibility checks | Verify |
| `--keep-artifacts` | Keep intermediate build files | Clean |
| `--verbose` | Show detailed command output | Quiet |
| `--jobs=N` | Build parallelism (sh/bat only) | Auto |
| `--cc=PATH` | C++ compiler (sh/bat only) | clang++ |
| `--output=PATH` | Output binary path (sh/bat only) | bin/simple |

## Files Modified

```
scripts/
├── bootstrap-from-scratch.sh      # ✅ QEMU support added (Linux/macOS)
├── bootstrap-from-scratch.bat     # ✅ QEMU support added (Windows)
├── bootstrap-multiphase.spl       # ✅ QEMU support added (Simple)
├── bootstrap-from-scratch-freebsd.sh  # Existing (executed in VM)
└── QEMU_BOOTSTRAP_README.md       # ✨ New (this file)

doc/guide/
└── qemu_bootstrap.md              # ✨ New (comprehensive guide)
```

## Troubleshooting

**"No FreeBSD VM found"**
- Download VM image or specify with `--qemu-vm=PATH`

**"qemu-system-x86_64 not found"**
- Install QEMU (see Prerequisites)

**"Timeout waiting for SSH"**
- Ensure VM has SSH configured (see SSH Setup)
- Check port isn't in use: `lsof -i :10022` (Linux/macOS) or `netstat -an | findstr 10022` (Windows)

**"rsync: command not found" (Windows)**
- Install Cygwin with rsync package
- Or use WinSCP for manual sync

**Build fails in VM**
- Check FreeBSD script exists: `scripts/bootstrap-from-scratch-freebsd.sh`
- Ensure VM has dependencies: `cmake`, `gmake`, `clang`

## Performance

| Mode | Build Time | Notes |
|------|------------|-------|
| Native Linux | ~60s | Fastest |
| Native FreeBSD | ~65s | Fastest on FreeBSD |
| QEMU (KVM) | ~90s | 1.5x slower, good for CI |
| QEMU (TCG) | 5-10min | 5-10x slower, no hardware virt |

**Tips:**
- Use KVM on Linux for best QEMU performance
- Keep VM running between builds (saves ~30s startup)
- Use `--skip-verify` during development (~20s faster)

## CI/CD Example

```yaml
# .github/workflows/freebsd.yml
name: FreeBSD Build
on: [push]
jobs:
  build:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4

      - name: Install QEMU
        run: sudo apt-get install -y qemu-system-x86 rsync

      - name: Download FreeBSD VM
        run: |
          wget -q https://download.freebsd.org/releases/VM-IMAGES/14.3-RELEASE/amd64/Latest/FreeBSD-14.3-RELEASE-amd64.qcow2.xz
          unxz FreeBSD-14.3-RELEASE-amd64.qcow2.xz
          mkdir -p build/freebsd/vm
          mv FreeBSD-14.3-RELEASE-amd64.qcow2 build/freebsd/vm/

      - name: Bootstrap FreeBSD Build
        run: ./scripts/bootstrap-from-scratch.sh --qemu-freebsd --skip-verify

      - name: Upload Binary
        uses: actions/upload-artifact@v4
        with:
          name: simple-freebsd
          path: bin/simple
```

## Documentation

Full documentation: [doc/guide/qemu_bootstrap.md](../doc/guide/qemu_bootstrap.md)

Related docs:
- [FreeBSD Workspace Setup](../doc/guide/freebsd_workspace_setup.md)
- [FreeBSD Quick Reference](../doc/guide/freebsd_quick_reference.md)
- [Bootstrap Process](../doc/design/bootstrap.md)

## Support

For issues or questions:
1. Check [doc/guide/qemu_bootstrap.md](../doc/guide/qemu_bootstrap.md) troubleshooting section
2. Verify prerequisites are installed
3. Test VM manually: `ssh -p 10022 freebsd@localhost`
4. Report bugs with full error output and `--verbose` flag enabled
