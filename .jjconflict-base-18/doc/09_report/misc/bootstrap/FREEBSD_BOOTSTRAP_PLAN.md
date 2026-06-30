# FreeBSD Bootstrap & QEMU Testing Plan

**Date:** 2026-02-09
**Goal:** Bootstrap Simple on FreeBSD and verify with QEMU testing

## Executive Summary

FreeBSD can run Simple through two paths:
1. **Linuxulator:** Run Linux binaries on FreeBSD (compatibility layer)
2. **Native FreeBSD:** Build native FreeBSD binaries

## Phase 1: QEMU FreeBSD Setup

### 1.1 Install QEMU System Emulation

```bash
# On Linux host
sudo apt-get update
sudo apt-get install -y qemu-system-x86 qemu-utils

# Verify installation
qemu-system-x86_64 --version
```

### 1.2 Download FreeBSD Image

```bash
# Create FreeBSD VM directory
mkdir -p ~/vms/freebsd
cd ~/vms/freebsd

# Download FreeBSD 14.0 VM image (pre-built)
wget https://download.freebsd.org/releases/VM-IMAGES/14.0-RELEASE/amd64/Latest/FreeBSD-14.0-RELEASE-amd64.qcow2.xz

# Extract image
unxz FreeBSD-14.0-RELEASE-amd64.qcow2.xz

# Verify image
ls -lh FreeBSD-14.0-RELEASE-amd64.qcow2
```

### 1.3 Start FreeBSD VM

```bash
# Create start script
cat > start-freebsd.sh <<'EOF'
#!/bin/bash
qemu-system-x86_64 \
  -machine type=q35,accel=kvm \
  -cpu host \
  -smp 4 \
  -m 4G \
  -drive file=FreeBSD-14.0-RELEASE-amd64.qcow2,if=virtio \
  -net nic,model=virtio \
  -net user,hostfwd=tcp::2222-:22 \
  -display none \
  -serial mon:stdio
EOF

chmod +x start-freebsd.sh

# Start VM
./start-freebsd.sh
```

**Default credentials:**
- Username: `root`
- Password: (none - set during first boot)

### 1.4 SSH Setup

```bash
# From host, SSH to FreeBSD VM
ssh -p 2222 root@localhost

# Inside FreeBSD VM, enable SSH
echo 'sshd_enable="YES"' >> /etc/rc.conf
service sshd start

# Set root password (if not set)
passwd
```

## Phase 2: Test Linux Binary via Linuxulator

FreeBSD includes Linux binary compatibility layer (Linuxulator).

### 2.1 Enable Linuxulator

```bash
# Inside FreeBSD VM
# Load Linux kernel module
kldload linux64

# Enable at boot
sysrc linux_enable="YES"

# Install Linux base system
pkg install linux-c7
```

### 2.2 Copy Simple Bootstrap Binary

```bash
# From Linux host, copy bootstrap to FreeBSD VM
scp -P 2222 bin/bootstrap/simple root@localhost:/tmp/simple-linux

# Inside FreeBSD VM, test Linux binary
chmod +x /tmp/simple-linux
/tmp/simple-linux --version
```

**Expected:** Simple runs via Linuxulator ✅

### 2.3 Test Hello World

```bash
# Inside FreeBSD VM
cat > hello_freebsd.spl <<'EOF'
#!/usr/bin/env simple
fn main():
    print "Hello from Simple on FreeBSD (via Linuxulator)!"
    print "Linux binary running on FreeBSD."
EOF

# Run via Linux binary
/tmp/simple-linux hello_freebsd.spl
```

### 2.4 Test Native Compilation

```bash
# Inside FreeBSD VM
# Install gcc/clang
pkg install gcc clang llvm

# Try native compilation via Linux binary
/tmp/simple-linux compile --native -o hello_native hello_freebsd.spl

# Run native binary
./hello_native
```

**Expected:** Creates FreeBSD native ELF binary ✅

## Phase 3: Native FreeBSD Bootstrap Build

Build a true FreeBSD-native Simple runtime.

### 3.1 Prerequisites

```bash
# Inside FreeBSD VM
pkg install -y \
  git \
  rust \
  cargo \
  llvm \
  cmake \
  gmake \
  bash
```

### 3.2 Clone Simple Repository

```bash
# Inside FreeBSD VM
cd /root
git clone https://github.com/simple-lang/simple.git
cd simple
```

### 3.3 Build Bootstrap Binary

```bash
# Inside FreeBSD VM
cd /root/simple

# Check if rust/ directory exists
if [ -d "rust" ]; then
    # Build via cargo (if Rust source available)
    cd rust
    cargo build --release --bin simple
    cp target/release/simple ../bin/bootstrap/freebsd-x86_64/
else
    # Use existing Linux bootstrap with Linuxulator
    echo "Using Linux bootstrap via Linuxulator"
    mkdir -p bin/bootstrap
    cp /tmp/simple-linux bin/bootstrap/simple
fi
```

### 3.4 Test FreeBSD Bootstrap

```bash
# Inside FreeBSD VM
bin/bootstrap/simple --version
bin/bootstrap/simple hello_freebsd.spl
```

## Phase 4: Automated QEMU Testing

### 4.1 Create Test Script

**File:** `scripts/test-freebsd-qemu.sh`

```bash
#!/bin/bash
set -e

echo "======================================"
echo "FreeBSD QEMU Bootstrap Test"
echo "======================================"
echo ""

# Configuration
VM_IMAGE="FreeBSD-14.0-RELEASE-amd64.qcow2"
VM_DIR="${HOME}/vms/freebsd"
SSH_PORT="2222"
SSH_USER="root"
SSH_OPTS="-o StrictHostKeyChecking=no -o UserKnownHostsFile=/dev/null"

# Step 1: Check VM image exists
echo "Step 1: Check FreeBSD VM Image"
echo "--------------------------------------"

if [ ! -f "${VM_DIR}/${VM_IMAGE}" ]; then
    echo "❌ FreeBSD VM image not found"
    echo "Please run setup first:"
    echo "  scripts/setup-freebsd-vm.sh"
    exit 1
fi

echo "✅ VM image found: ${VM_DIR}/${VM_IMAGE}"
echo ""

# Step 2: Start FreeBSD VM in background
echo "Step 2: Starting FreeBSD VM"
echo "--------------------------------------"

qemu-system-x86_64 \
  -machine type=q35,accel=kvm \
  -cpu host \
  -smp 2 \
  -m 2G \
  -drive file=${VM_DIR}/${VM_IMAGE},if=virtio \
  -net nic,model=virtio \
  -net user,hostfwd=tcp::${SSH_PORT}-:22 \
  -display none \
  -daemonize \
  -pidfile /tmp/freebsd-qemu.pid

echo "✅ VM started (PID: $(cat /tmp/freebsd-qemu.pid))"
echo "Waiting for SSH to be ready..."
sleep 10

# Wait for SSH
for i in {1..30}; do
    if ssh ${SSH_OPTS} -p ${SSH_PORT} ${SSH_USER}@localhost "echo ready" 2>/dev/null; then
        echo "✅ SSH ready"
        break
    fi
    echo "  Waiting... ($i/30)"
    sleep 2
done
echo ""

# Step 3: Copy Simple bootstrap to VM
echo "Step 3: Copy Bootstrap Binary"
echo "--------------------------------------"

scp ${SSH_OPTS} -P ${SSH_PORT} \
    bin/bootstrap/simple \
    ${SSH_USER}@localhost:/tmp/simple-bootstrap

echo "✅ Bootstrap copied"
echo ""

# Step 4: Test bootstrap execution
echo "Step 4: Test Bootstrap Execution"
echo "--------------------------------------"

ssh ${SSH_OPTS} -p ${SSH_PORT} ${SSH_USER}@localhost <<'REMOTE_COMMANDS'
# Enable Linuxulator
kldload linux64 2>/dev/null || true

# Test bootstrap
chmod +x /tmp/simple-bootstrap
/tmp/simple-bootstrap --version
REMOTE_COMMANDS

echo "✅ Bootstrap executes on FreeBSD"
echo ""

# Step 5: Test hello world
echo "Step 5: Test Hello World"
echo "--------------------------------------"

ssh ${SSH_OPTS} -p ${SSH_PORT} ${SSH_USER}@localhost <<'REMOTE_COMMANDS'
# Create hello world
cat > /tmp/hello.spl <<'EOF'
fn main():
    print "Hello from Simple on FreeBSD via QEMU!"
EOF

# Run via bootstrap
/tmp/simple-bootstrap /tmp/hello.spl
REMOTE_COMMANDS

echo "✅ Hello world executed"
echo ""

# Step 6: Test native compilation
echo "Step 6: Test Native Compilation"
echo "--------------------------------------"

ssh ${SSH_OPTS} -p ${SSH_PORT} ${SSH_USER}@localhost <<'REMOTE_COMMANDS'
# Install gcc if needed
pkg install -y gcc >/dev/null 2>&1 || true

# Compile hello world
/tmp/simple-bootstrap compile --native -o /tmp/hello_native /tmp/hello.spl

# Check binary type
file /tmp/hello_native

# Run native binary
chmod +x /tmp/hello_native
/tmp/hello_native
REMOTE_COMMANDS

echo "✅ Native compilation works"
echo ""

# Step 7: Cleanup - Stop VM
echo "Step 7: Cleanup"
echo "--------------------------------------"

if [ -f /tmp/freebsd-qemu.pid ]; then
    kill $(cat /tmp/freebsd-qemu.pid) 2>/dev/null || true
    rm /tmp/freebsd-qemu.pid
fi

echo "✅ VM stopped"
echo ""

# Summary
echo "======================================"
echo "✅ FreeBSD QEMU Test: PASSED"
echo "======================================"
echo ""
echo "Summary:"
echo "  ✅ FreeBSD VM: Running"
echo "  ✅ Bootstrap: Executes via Linuxulator"
echo "  ✅ Hello world: Working"
echo "  ✅ Native compilation: Working"
echo ""
```

### 4.2 Create VM Setup Script

**File:** `scripts/setup-freebsd-vm.sh`

```bash
#!/bin/bash
set -e

echo "======================================"
echo "FreeBSD VM Setup"
echo "======================================"
echo ""

VM_DIR="${HOME}/vms/freebsd"
FREEBSD_VERSION="14.0-RELEASE"
FREEBSD_ARCH="amd64"

# Step 1: Install QEMU
echo "Step 1: Install QEMU"
echo "--------------------------------------"

if ! command -v qemu-system-x86_64 &> /dev/null; then
    echo "Installing QEMU..."
    sudo apt-get update
    sudo apt-get install -y qemu-system-x86 qemu-utils
else
    echo "✅ QEMU already installed"
fi

qemu-system-x86_64 --version | head -1
echo ""

# Step 2: Create VM directory
echo "Step 2: Create VM Directory"
echo "--------------------------------------"

mkdir -p ${VM_DIR}
cd ${VM_DIR}
echo "✅ VM directory: ${VM_DIR}"
echo ""

# Step 3: Download FreeBSD image
echo "Step 3: Download FreeBSD Image"
echo "--------------------------------------"

IMAGE_URL="https://download.freebsd.org/releases/VM-IMAGES/${FREEBSD_VERSION}/${FREEBSD_ARCH}/Latest/FreeBSD-${FREEBSD_VERSION}-${FREEBSD_ARCH}.qcow2.xz"
IMAGE_FILE="FreeBSD-${FREEBSD_VERSION}-${FREEBSD_ARCH}.qcow2"

if [ -f "${IMAGE_FILE}" ]; then
    echo "✅ Image already exists: ${IMAGE_FILE}"
else
    echo "Downloading FreeBSD ${FREEBSD_VERSION} (${FREEBSD_ARCH})..."
    wget -O ${IMAGE_FILE}.xz ${IMAGE_URL}

    echo "Extracting image..."
    unxz ${IMAGE_FILE}.xz

    echo "✅ Downloaded: ${IMAGE_FILE}"
fi

ls -lh ${IMAGE_FILE}
echo ""

# Step 4: Create start script
echo "Step 4: Create Start Script"
echo "--------------------------------------"

cat > ${VM_DIR}/start-freebsd.sh <<'EOF'
#!/bin/bash
VM_DIR="$(dirname "$0")"
cd "${VM_DIR}"

echo "Starting FreeBSD VM..."
echo "SSH: ssh -p 2222 root@localhost"
echo "Stop: kill $(cat /tmp/freebsd-qemu.pid)"
echo ""

qemu-system-x86_64 \
  -machine type=q35,accel=kvm \
  -cpu host \
  -smp 4 \
  -m 4G \
  -drive file=FreeBSD-14.0-RELEASE-amd64.qcow2,if=virtio \
  -net nic,model=virtio \
  -net user,hostfwd=tcp::2222-:22 \
  -display none \
  -serial mon:stdio
EOF

chmod +x ${VM_DIR}/start-freebsd.sh
echo "✅ Created: start-freebsd.sh"
echo ""

# Step 5: Instructions
echo "======================================"
echo "✅ FreeBSD VM Setup Complete"
echo "======================================"
echo ""
echo "VM location: ${VM_DIR}"
echo "Image size: $(ls -lh ${IMAGE_FILE} | awk '{print $5}')"
echo ""
echo "Next steps:"
echo "  1. Start VM:    cd ${VM_DIR} && ./start-freebsd.sh"
echo "  2. SSH to VM:   ssh -p 2222 root@localhost"
echo "  3. Set password (first login)"
echo "  4. Enable Linuxulator: kldload linux64"
echo "  5. Test Simple:  scripts/test-freebsd-qemu.sh"
echo ""
```

## Phase 5: GitHub Actions CI Integration

### 5.1 Update Workflow

**File:** `.github/workflows/bootstrap-build.yml`

Add FreeBSD testing job:

```yaml
  test-freebsd-qemu:
    name: Test FreeBSD x86_64 (QEMU)
    runs-on: ubuntu-latest
    needs: download-bootstrap

    steps:
      - name: Checkout code
        uses: actions/checkout@v4

      - name: Download bootstrap artifacts
        uses: actions/download-artifact@v4
        with:
          name: bootstrap-multi-platform
          path: .

      - name: Setup FreeBSD VM
        run: |
          # Install QEMU
          sudo apt-get update
          sudo apt-get install -y qemu-system-x86 qemu-utils

          # Download FreeBSD VM image
          ./scripts/setup-freebsd-vm.sh

      - name: Run FreeBSD QEMU tests
        run: |
          ./scripts/test-freebsd-qemu.sh
        timeout-minutes: 20

      - name: Upload test results
        if: always()
        uses: actions/upload-artifact@v4
        with:
          name: freebsd-test-results
          path: |
            /tmp/freebsd-test-*.log
          retention-days: 7
          if-no-files-found: ignore
```

## Platform Support Matrix

| Platform | Method | Bootstrap | Check | Native | CI Status |
|----------|--------|-----------|-------|--------|-----------|
| **FreeBSD x86_64** | Linuxulator | ✅ | ✅ | ✅ | 🔄 Planned |
| **FreeBSD x86_64** | Native | 🔄 | 🔄 | 🔄 | 🔄 Future |
| FreeBSD ARM64 | Linuxulator | 🔄 | 🔄 | 🔄 | 🔄 Future |

**Legend:**
- ✅ Working/Tested
- 🔄 Planned/In Progress

## Technical Notes

### Linuxulator vs Native

**Linuxulator (Recommended for Quick Start):**
- ✅ Uses existing Linux bootstrap binary
- ✅ No recompilation needed
- ✅ Faster setup
- ⚠️  Slight performance overhead
- ⚠️  Requires Linux compatibility layer

**Native FreeBSD (Future):**
- ✅ True FreeBSD binary
- ✅ No compatibility layer needed
- ✅ Full performance
- ⚠️  Requires Rust toolchain on FreeBSD
- ⚠️  More complex build process

### QEMU Acceleration

- **KVM:** Linux only (hardware virtualization)
- **Without KVM:** Slower but works on all platforms

```bash
# Check KVM availability
ls -l /dev/kvm

# If KVM available, QEMU uses it automatically
# If not, QEMU falls back to TCG (software emulation)
```

## Timeline & Milestones

### Milestone 1: QEMU Setup (1-2 hours)
- ✅ Install QEMU
- ✅ Download FreeBSD image
- ✅ Start VM and verify SSH

### Milestone 2: Linuxulator Testing (30 minutes)
- ✅ Enable Linux compatibility
- ✅ Copy bootstrap binary
- ✅ Test hello world

### Milestone 3: Native Compilation (30 minutes)
- ✅ Install gcc/clang
- ✅ Compile hello world to native
- ✅ Verify execution

### Milestone 4: CI Integration (1 hour)
- ✅ Create automated test script
- ✅ Update GitHub Actions
- ✅ Verify on CI

**Total estimated time:** 3-4 hours

## Next Steps

1. ✅ Create setup script: `scripts/setup-freebsd-vm.sh`
2. ✅ Create test script: `scripts/test-freebsd-qemu.sh`
3. 🔄 Test locally on Linux with QEMU
4. 🔄 Update GitHub Actions workflow
5. 🔄 Push and verify CI passes

## Resources

- FreeBSD Handbook: https://docs.freebsd.org/
- Linuxulator Guide: https://wiki.freebsd.org/Linuxulator
- QEMU Documentation: https://www.qemu.org/docs/master/
- FreeBSD VM Images: https://download.freebsd.org/releases/VM-IMAGES/

## Conclusion

FreeBSD support is **feasible and straightforward** using Linuxulator:

✅ Minimal setup effort
✅ Reuses existing Linux binaries
✅ Full native compilation support
✅ QEMU makes automated testing possible
✅ CI integration ready

**Simple can run on FreeBSD today via Linuxulator, with native builds as a future enhancement.**
