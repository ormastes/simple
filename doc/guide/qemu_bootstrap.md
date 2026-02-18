# QEMU Bootstrap Guide

## Overview

All three bootstrap scripts now support building the Simple compiler in a QEMU FreeBSD VM. This enables:
- Cross-platform FreeBSD builds from Linux/Windows
- Automated VM management
- Remote build execution with result retrieval

## Quick Start

### Linux/macOS
```bash
# Auto-detect and use FreeBSD VM
./scripts/bootstrap/bootstrap-from-scratch.sh --qemu-freebsd

# Specify VM path
./scripts/bootstrap/bootstrap-from-scratch.sh --qemu-freebsd --qemu-vm=/path/to/freebsd.qcow2

# Custom SSH port
./scripts/bootstrap/bootstrap-from-scratch.sh --qemu-freebsd --qemu-port=10023
```

### Windows
```batch
REM Auto-detect and use FreeBSD VM
scripts\bootstrap\bootstrap-from-scratch.bat --qemu-freebsd

REM Specify VM path
scripts\bootstrap\bootstrap-from-scratch.bat --qemu-freebsd --qemu-vm=C:\VMs\freebsd.qcow2
```

### Simple Language
```bash
# Using the Simple script
bin/release/simple scripts/bootstrap/bootstrap-multiphase.spl --qemu-freebsd

# With custom settings
bin/release/simple scripts/bootstrap/bootstrap-multiphase.spl --qemu-freebsd --qemu-vm=/path/to/vm --qemu-port=10022
```

## Prerequisites

### QEMU Installation

**Linux (Debian/Ubuntu):**
```bash
sudo apt install qemu-system-x86 qemu-utils
```

**Linux (Fedora/RHEL):**
```bash
sudo dnf install qemu-system-x86 qemu-img
```

**macOS:**
```bash
brew install qemu
```

**Windows:**
Download from https://www.qemu.org/download/#windows

### FreeBSD VM Image

The scripts auto-detect VM images in these locations:
1. `build/freebsd/vm/FreeBSD-14.3-RELEASE-amd64.qcow2`
2. `~/.qemu/freebsd.qcow2` (Linux/macOS)
3. `%USERPROFILE%\.qemu\freebsd.qcow2` (Windows)
4. `/opt/qemu/freebsd.qcow2` (Linux)

Download FreeBSD VM:
```bash
# Using Simple's download script
bin/simple scripts/download_qemu.spl freebsd

# Or manually from FreeBSD.org
wget https://download.freebsd.org/releases/VM-IMAGES/14.3-RELEASE/amd64/Latest/FreeBSD-14.3-RELEASE-amd64.qcow2.xz
unxz FreeBSD-14.3-RELEASE-amd64.qcow2.xz
mkdir -p build/freebsd/vm
mv FreeBSD-14.3-RELEASE-amd64.qcow2 build/freebsd/vm/
```

### SSH Setup (First Time Only)

FreeBSD VMs require SSH to be configured:

```bash
# Start VM manually first time
qemu-system-x86_64 \
  -machine accel=kvm:tcg \
  -cpu host \
  -m 4G \
  -smp 4 \
  -drive file=build/freebsd/vm/FreeBSD-14.3-RELEASE-amd64.qcow2,format=qcow2,if=virtio \
  -net nic,model=virtio \
  -net user,hostfwd=tcp::10022-:22 \
  -nographic

# Login (default: root, no password)
# Then configure SSH:
pkg install sudo openssh-portable
echo 'sshd_enable="YES"' >> /etc/rc.conf
service sshd start

# Create user
pw useradd -n freebsd -m -s /bin/sh -G wheel
passwd freebsd

# Enable sudo
echo '%wheel ALL=(ALL) NOPASSWD: ALL' >> /usr/local/etc/sudoers

# Exit VM (Ctrl+A, then X)
```

## How It Works

### Workflow

1. **VM Detection**: Scripts check for FreeBSD VM in standard locations
2. **VM Startup**: If not running, starts QEMU with KVM acceleration (or TCG fallback)
3. **SSH Wait**: Waits up to 60 seconds for SSH to become available
4. **Project Sync**: Uses `rsync` to sync project files to VM (excludes `.git`, `build`, etc.)
5. **Remote Build**: Executes FreeBSD-specific bootstrap script in VM
6. **Result Retrieval**: Uses `scp` to copy built binary back to host
7. **Cleanup**: VM keeps running for subsequent builds (faster)

### Port Forwarding

Default SSH port: `10022` (host) → `22` (guest)

Change with `--qemu-port=N`:
```bash
./scripts/bootstrap/bootstrap-from-scratch.sh --qemu-freebsd --qemu-port=10023
```

### VM Resources

Default QEMU settings:
- **CPU**: Host passthrough with KVM acceleration (4 cores)
- **RAM**: 4GB
- **Disk**: Virtio (best performance)
- **Network**: Virtio with user networking (no root required)

## Options Reference

### Common Options

| Option | Description | Default |
|--------|-------------|---------|
| `--qemu-freebsd` | Enable QEMU FreeBSD mode | Off |
| `--qemu-vm=PATH` | Path to FreeBSD qcow2 image | Auto-detect |
| `--qemu-port=N` | SSH port for VM | 10022 |
| `--skip-verify` | Skip reproducibility checks | Verify enabled |
| `--keep-artifacts` | Keep build artifacts | Clean up |
| `--verbose` | Show detailed output | Quiet |

### Script-Specific Options

**bootstrap-from-scratch.sh / .bat:**
- `--jobs=N`: Parallel build jobs (default: auto-detect)
- `--cc=PATH`: C++ compiler path (default: clang++)
- `--output=PATH`: Final binary location (default: `bin/simple` or `bin/simple.exe`)

**bootstrap-multiphase.spl:**
- `--seed-cpp=PATH`: Path to seed_cpp binary
- `--clang=PATH`: Path to clang++ compiler
- `--no-verify`: Skip reproducibility checks (same as `--skip-verify`)

## Troubleshooting

### VM Not Starting

**Error**: `qemu-system-x86_64 not found`
- **Fix**: Install QEMU (see Prerequisites)

**Error**: `No FreeBSD VM found`
- **Fix**: Specify path with `--qemu-vm=PATH` or download VM image

**Error**: `Could not access KVM kernel module`
- **Fix**: Use TCG (software emulation, slower):
  ```bash
  # Already handled automatically by scripts (-machine accel=kvm:tcg)
  ```

### SSH Connection Failed

**Error**: `Timeout waiting for SSH connection`
- **Fix**: Ensure VM has SSH configured (see SSH Setup section)
- **Fix**: Check port not in use: `lsof -i :10022` (Linux/macOS) or `netstat -an | findstr 10022` (Windows)

**Error**: `Connection refused`
- **Fix**: VM may not have started. Check manually:
  ```bash
  ssh -p 10022 freebsd@localhost
  ```

### Sync Errors

**Error**: `rsync: command not found`
- **Linux**: `sudo apt install rsync`
- **Windows**: Install Cygwin with rsync, or use WinSCP
- **macOS**: rsync is pre-installed

**Error**: `Permission denied`
- **Fix**: Check SSH keys or password authentication is set up

### Build Failures

**Error**: `FreeBSD VM bootstrap failed`
- **Fix**: Check FreeBSD script exists: `scripts/bootstrap/bootstrap-from-scratch-freebsd.sh`
- **Fix**: Ensure dependencies installed in VM: `cmake`, `gmake`, `clang`

## Performance

### Build Times

| Mode | Time (Core2+Full1+Full2) |
|------|--------------------------|
| Native Linux | ~60s |
| Native FreeBSD | ~65s |
| QEMU FreeBSD (KVM) | ~90s |
| QEMU FreeBSD (TCG) | ~5-10min |

### Optimization Tips

1. **Use KVM**: Ensure KVM is available on Linux for near-native performance
2. **Keep VM Running**: Don't shut down VM between builds (save ~30s startup)
3. **Use SSD**: VM disk I/O is critical
4. **Skip Verification**: Use `--skip-verify` for faster builds during development

## Advanced Usage

### Multiple VMs

Run multiple FreeBSD versions:
```bash
# FreeBSD 14
./scripts/bootstrap/bootstrap-from-scratch.sh --qemu-freebsd --qemu-vm=freebsd14.qcow2 --qemu-port=10022

# FreeBSD 13
./scripts/bootstrap/bootstrap-from-scratch.sh --qemu-freebsd --qemu-vm=freebsd13.qcow2 --qemu-port=10023
```

### Headless Server

The scripts use QEMU's `-nographic` mode, suitable for headless servers:
```bash
# Works over SSH
ssh build-server
./scripts/bootstrap/bootstrap-from-scratch.sh --qemu-freebsd
```

### CI/CD Integration

Example GitHub Actions:
```yaml
- name: Setup QEMU
  run: sudo apt-get install -y qemu-system-x86

- name: Download FreeBSD VM
  run: |
    wget https://download.freebsd.org/releases/VM-IMAGES/14.3-RELEASE/amd64/Latest/FreeBSD-14.3-RELEASE-amd64.qcow2.xz
    unxz FreeBSD-14.3-RELEASE-amd64.qcow2.xz
    mkdir -p build/freebsd/vm
    mv FreeBSD-14.3-RELEASE-amd64.qcow2 build/freebsd/vm/

- name: Bootstrap FreeBSD Build
  run: ./scripts/bootstrap/bootstrap-from-scratch.sh --qemu-freebsd --skip-verify
```

## Architecture

### Script Structure

```
bootstrap-from-scratch.sh/bat/spl
├── Argument Parsing
│   └── --qemu-freebsd detection
├── QEMU Mode Branch
│   ├── VM Detection/Auto-locate
│   ├── VM Startup (if not running)
│   ├── SSH Wait Loop
│   ├── Project Sync (rsync)
│   ├── Remote Bootstrap Execution
│   └── Binary Retrieval (scp)
└── Normal Mode (local build)
    └── Steps 0-6 (seed → core → full)
```

### File Sync

Excluded directories (not synced to VM):
- `.git` (version control, too large)
- `build` (will be created in VM)
- `target` (temporary)
- `.jj` (local VCS state)
- `.github` (CI config)

Included:
- `src/` (all source code)
- `seed/` (seed compiler sources)
- `scripts/` (bootstrap scripts)
- `test/` (test suite)
- `doc/` (documentation)

## See Also

- [FreeBSD Workspace Setup](freebsd_workspace_setup.md) - Full FreeBSD development environment
- [FreeBSD Quick Reference](freebsd_quick_reference.md) - FreeBSD commands cheat sheet
- [Bootstrap Process](../design/bootstrap.md) - Technical details of bootstrap pipeline
- [QEMU Documentation](https://www.qemu.org/docs/master/) - Official QEMU docs
