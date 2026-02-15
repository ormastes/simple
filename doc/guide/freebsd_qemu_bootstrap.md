# FreeBSD Bootstrap with QEMU — Quick Start Guide

Complete guide for bootstrapping Simple compiler on FreeBSD using QEMU virtualization.

## Prerequisites (Linux Host)

**System Requirements:**
- Linux host (Ubuntu 22.04 LTS, Fedora 38+, or similar)
- 8GB+ RAM (4GB for VM, 4GB for host)
- 20GB+ free disk space
- QEMU with KVM support (or TCG fallback)
- Rsync for file synchronization
- SSH client

**Install Dependencies:**

```bash
# Ubuntu/Debian
sudo apt update
sudo apt install qemu-system-x86 qemu-utils rsync openssh-client wget xz-utils

# Fedora/RHEL
sudo dnf install qemu-system-x86 rsync openssh-clients wget xz

# Arch Linux
sudo pacman -S qemu-system-x86 rsync openssh wget xz

# Verify installation
qemu-system-x86_64 --version  # Should show QEMU 7.0+
```

## Step 1: Download FreeBSD VM Image

```bash
# Create VM directory
mkdir -p build/freebsd/vm
cd build/freebsd/vm

# Download FreeBSD 14.3 QEMU image (amd64)
wget https://download.freebsd.org/releases/amd64/14.3-RELEASE/FreeBSD-14.3-RELEASE-amd64.qcow2.xz

# Extract (this may take 5-10 minutes)
xz -d FreeBSD-14.3-RELEASE-amd64.qcow2.xz

# Verify download (optional)
ls -lh FreeBSD-14.3-RELEASE-amd64.qcow2
# Expected: ~5-8 GB qcow2 image

cd ../../..
```

**Alternative ARM64 (if on Apple Silicon or ARM Linux):**
```bash
# For ARM64 hosts
wget https://download.freebsd.org/releases/arm64/aarch64/14.3-RELEASE/FreeBSD-14.3-RELEASE-arm64-aarch64.qcow2.xz
xz -d FreeBSD-14.3-RELEASE-arm64-aarch64.qcow2.xz
```

## Step 2: Configure VM SSH Access

**Option A: Use pre-configured image (recommended)**

The downloaded FreeBSD VM image should have SSH enabled by default. You may need to set up SSH keys:

```bash
# Generate SSH key if you don't have one
if [ ! -f ~/.ssh/id_rsa ]; then
    ssh-keygen -t rsa -b 4096 -f ~/.ssh/id_rsa -N ""
fi

# The bootstrap script will handle SSH key setup automatically
```

**Option B: Manual SSH configuration (if needed)**

If the VM doesn't accept SSH connections, use the provided helper script:

```bash
./script/configure_freebsd_vm_ssh.sh
```

This script will:
1. Start the VM with console access
2. Configure SSH daemon
3. Set up authorized_keys
4. Enable SSH on boot

## Step 3: Test QEMU VM Connection

**Start the VM manually (optional test):**

```bash
# Start VM in background
qemu-system-x86_64 \
    -machine accel=kvm:tcg \
    -cpu host \
    -m 4G \
    -smp 4 \
    -drive file=build/freebsd/vm/FreeBSD-14.3-RELEASE-amd64.qcow2,format=qcow2,if=virtio \
    -net nic,model=virtio \
    -net user,hostfwd=tcp::2222-:22 \
    -nographic \
    -daemonize \
    -pidfile build/freebsd/vm/qemu.pid

# Wait for boot (30-60 seconds)
sleep 30

# Test SSH connection
ssh -o ConnectTimeout=5 -o StrictHostKeyChecking=no -p 2222 freebsd@localhost "uname -a"
# Expected: FreeBSD 14.3-RELEASE FreeBSD 14.3-RELEASE releng/14.3-n257583-cd6dc54a4dd8 ...

# Stop VM
kill $(cat build/freebsd/vm/qemu.pid)
rm -f build/freebsd/vm/qemu.pid
```

**Troubleshooting SSH connection:**

If SSH connection fails:

```bash
# Check if VM is running
ps aux | grep qemu-system-x86_64

# Check if port is listening
netstat -tln | grep 2222

# Try different SSH options
ssh -v -o ConnectTimeout=10 -o StrictHostKeyChecking=no -p 2222 freebsd@localhost

# If still failing, check VM console logs
tail -f build/freebsd/vm/qemu.log  # (if redirected to log file)
```

## Step 4: Run Bootstrap in QEMU VM

**Automated bootstrap (recommended):**

```bash
# From project root directory
export QEMU_VM_PATH="build/freebsd/vm/FreeBSD-14.3-RELEASE-amd64.qcow2"
export QEMU_PORT=2222
export QEMU_USER=freebsd

# Run full QEMU bootstrap
./script/bootstrap-from-scratch.sh --platform=freebsd
```

This will:
1. Auto-detect FreeBSD VM image
2. Start QEMU VM with KVM acceleration
3. Wait for SSH connection
4. Sync project files to VM (via rsync)
5. Execute `bootstrap-from-scratch-freebsd.sh` inside VM
6. Retrieve compiled `bin/simple` binary from VM
7. Verify binary is FreeBSD ELF

**Manual bootstrap (for debugging):**

```bash
# 1. Start VM
qemu-system-x86_64 \
    -machine accel=kvm:tcg -cpu host -m 4G -smp 4 \
    -drive file=build/freebsd/vm/FreeBSD-14.3-RELEASE-amd64.qcow2,format=qcow2,if=virtio \
    -net nic,model=virtio -net user,hostfwd=tcp::2222-:22 \
    -nographic -daemonize -pidfile build/freebsd/vm/qemu.pid

# 2. Sync project to VM
rsync -az --delete -e "ssh -p 2222 -o StrictHostKeyChecking=no" \
    --exclude='.git' --exclude='build' --exclude='.jj' \
    . freebsd@localhost:~/simple/

# 3. Run bootstrap inside VM
ssh -p 2222 freebsd@localhost "cd ~/simple && ./script/bootstrap-from-scratch-freebsd.sh"

# 4. Retrieve binary
mkdir -p bin
rsync -az -e "ssh -p 2222 -o StrictHostKeyChecking=no" \
    freebsd@localhost:~/simple/bin/simple bin/simple

# 5. Verify binary
file bin/simple
# Expected: bin/simple: ELF 64-bit LSB executable, x86-64, version 1 (FreeBSD), ...

# 6. Stop VM
kill $(cat build/freebsd/vm/qemu.pid)
```

## Step 5: Verify Bootstrap Results

```bash
# Check binary type
file bin/simple
# Expected: ELF 64-bit LSB executable, x86-64, version 1 (FreeBSD), ...

# Check binary size
ls -lh bin/simple
# Expected: ~33 MB

# Verify it's NOT a Linux binary
readelf -h bin/simple | grep "OS/ABI"
# Expected: OS/ABI: UNIX - FreeBSD

# Test inside QEMU VM (optional)
ssh -p 2222 freebsd@localhost "~/simple/bin/simple --version"
# Expected: Simple Compiler v0.x.x
```

## Common Issues and Solutions

### Issue: QEMU VM won't start

**Symptom:** `qemu-system-x86_64: Could not access KVM kernel module`

**Solution:**
```bash
# Check if KVM is available
ls -l /dev/kvm

# If missing, enable KVM support
sudo modprobe kvm-intel  # For Intel CPUs
# OR
sudo modprobe kvm-amd    # For AMD CPUs

# If KVM not available, use TCG (slower but works)
# Edit machine type: -machine accel=tcg
```

### Issue: SSH connection timeout

**Symptom:** `ssh: connect to host localhost port 2222: Connection refused`

**Solutions:**
```bash
# 1. Wait longer (VM boot can take 60-90 seconds)
sleep 60
ssh -p 2222 freebsd@localhost "echo OK"

# 2. Check if SSH is enabled in VM
ssh -p 2222 freebsd@localhost "service sshd status"

# 3. Re-configure SSH
./script/configure_freebsd_vm_ssh.sh
```

### Issue: Rsync permission denied

**Symptom:** `rsync: failed to set permissions on "/home/freebsd/simple": Operation not permitted`

**Solution:**
```bash
# Use --no-perms flag
rsync -az --delete --no-perms -e "ssh -p 2222 -o StrictHostKeyChecking=no" \
    . freebsd@localhost:~/simple/
```

### Issue: Out of disk space in VM

**Symptom:** `No space left on device` during bootstrap

**Solution:**
```bash
# Resize qcow2 image (add 10GB)
qemu-img resize build/freebsd/vm/FreeBSD-14.3-RELEASE-amd64.qcow2 +10G

# Boot VM and grow partition (inside VM)
ssh -p 2222 freebsd@localhost "sudo growfs /dev/vtbd0s1a"
```

### Issue: Bootstrap fails inside VM

**Symptom:** `seed_cpp: command not found` or compilation errors

**Solution:**
```bash
# Check FreeBSD tools are installed
ssh -p 2222 freebsd@localhost "pkg install cmake ninja clang"

# Check disk space
ssh -p 2222 freebsd@localhost "df -h"

# Check memory
ssh -p 2222 freebsd@localhost "sysctl hw.physmem"  # Should be >= 4GB

# Run with verbose output
ssh -p 2222 freebsd@localhost "cd ~/simple && ./script/bootstrap-from-scratch-freebsd.sh --verbose"
```

## Performance Tuning

**KVM Acceleration (Linux hosts with Intel VT-x or AMD-V):**
```bash
# Verify KVM is available
lscpu | grep Virtualization
# Expected: Virtualization: VT-x (Intel) or AMD-V (AMD)

# Use KVM for 10-20x speedup
-machine accel=kvm
```

**CPU Pinning (for better performance):**
```bash
# Pin QEMU to specific CPU cores
taskset -c 0-3 qemu-system-x86_64 ...
```

**Memory Tuning:**
```bash
# For 16GB+ host, allocate 8GB to VM
-m 8G

# Enable huge pages (Linux host)
sudo sysctl vm.nr_hugepages=2048
```

**Parallel Builds:**
```bash
# Use more parallel jobs inside VM
ssh -p 2222 freebsd@localhost "cd ~/simple && ./script/bootstrap-from-scratch-freebsd.sh --jobs=8"
```

## Advanced: Native FreeBSD Bootstrap

If you have access to a physical FreeBSD machine or remote FreeBSD server:

```bash
# On FreeBSD native system
git clone https://github.com/simple-lang/simple.git
cd simple

# Install dependencies
pkg install cmake ninja

# Run bootstrap
./script/bootstrap-from-scratch-freebsd.sh

# Output: bin/simple (native FreeBSD binary)
```

**Benchmark:** Native FreeBSD bootstrap typically takes:
- **Seed (CMake + Clang):** 30-60 seconds
- **Core transpile:** 10-20 seconds
- **Core1 compile:** 20-40 seconds
- **Core2 self-host:** 15-30 seconds
- **Full1 compile:** 60-120 seconds
- **Full2 reproducibility:** 60-120 seconds
- **Total:** 3-6 minutes on modern hardware

## QEMU VM Management

**Stop VM:**
```bash
# Graceful shutdown
ssh -p 2222 freebsd@localhost "sudo shutdown -p now"

# Force kill
kill $(cat build/freebsd/vm/qemu.pid)
```

**VM Snapshots (save state for quick restarts):**
```bash
# Create snapshot
qemu-img snapshot -c bootstrap-ready build/freebsd/vm/FreeBSD-14.3-RELEASE-amd64.qcow2

# List snapshots
qemu-img snapshot -l build/freebsd/vm/FreeBSD-14.3-RELEASE-amd64.qcow2

# Restore snapshot
qemu-img snapshot -a bootstrap-ready build/freebsd/vm/FreeBSD-14.3-RELEASE-amd64.qcow2
```

**VM Console Access (for debugging):**
```bash
# Start VM with VNC console
qemu-system-x86_64 ... -vnc :0

# Connect with VNC viewer
vncviewer localhost:5900

# Or use QEMU monitor
qemu-system-x86_64 ... -monitor stdio
```

## CI/CD Integration

**Example GitHub Actions workflow:**

```yaml
name: FreeBSD Bootstrap

on: [push, pull_request]

jobs:
  freebsd-qemu:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4

      - name: Install QEMU
        run: |
          sudo apt update
          sudo apt install -y qemu-system-x86 rsync

      - name: Cache FreeBSD VM
        uses: actions/cache@v4
        with:
          path: build/freebsd/vm
          key: freebsd-14.3-vm

      - name: Download FreeBSD VM
        run: |
          if [ ! -f build/freebsd/vm/FreeBSD-14.3-RELEASE-amd64.qcow2 ]; then
            mkdir -p build/freebsd/vm
            wget -q https://download.freebsd.org/releases/amd64/14.3-RELEASE/FreeBSD-14.3-RELEASE-amd64.qcow2.xz
            xz -d FreeBSD-14.3-RELEASE-amd64.qcow2.xz
          fi

      - name: Run QEMU Bootstrap
        timeout-minutes: 30
        run: |
          export QEMU_VM_PATH="build/freebsd/vm/FreeBSD-14.3-RELEASE-amd64.qcow2"
          ./script/bootstrap-from-scratch.sh --platform=freebsd

      - name: Verify Binary
        run: |
          file bin/simple
          readelf -h bin/simple | grep FreeBSD
          ls -lh bin/simple

      - name: Upload Artifact
        uses: actions/upload-artifact@v4
        with:
          name: simple-freebsd-x86_64
          path: bin/simple
```

## References

- **FreeBSD Downloads:** https://download.freebsd.org/releases/
- **QEMU Documentation:** https://www.qemu.org/docs/master/
- **FreeBSD Handbook:** https://docs.freebsd.org/en/books/handbook/
- **Simple Bootstrap Pipeline:** `doc/build/bootstrap_pipeline.md`
- **FreeBSD Bootstrap Script:** `script/bootstrap-from-scratch-freebsd.sh`

## Changelog

- **2026-02-15:** Initial FreeBSD QEMU bootstrap guide
- Tested on Ubuntu 22.04 LTS + FreeBSD 14.3 QEMU VM
- CMake + Ninja + Clang 19+ + C++20
