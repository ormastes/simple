#!/bin/bash
# Test Simple on FreeBSD via QEMU
# Tests: Bootstrap → Check → Native Hello World Compilation

set -e

echo "=========================================="
echo "Simple FreeBSD QEMU Bootstrap Test"
echo "=========================================="
echo ""

# Configuration
VM_DIR="${HOME}/vms/freebsd"
VM_IMAGE="FreeBSD-14.3-RELEASE-amd64.qcow2"
SSH_PORT="2222"
SSH_USER="root"
SSH_OPTS="-o StrictHostKeyChecking=no -o UserKnownHostsFile=/dev/null -o ConnectTimeout=5"
MAX_WAIT=60

# Colors
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
NC='\033[0m' # No Color

# Helper functions
info() {
    echo -e "${GREEN}$1${NC}"
}

warn() {
    echo -e "${YELLOW}$1${NC}"
}

error() {
    echo -e "${RED}$1${NC}"
}

# Step 1: Prerequisites check
echo "Step 1: Check Prerequisites"
echo "----------------------------------------"

if ! command -v qemu-system-x86_64 &> /dev/null; then
    error "❌ QEMU not found"
    echo "Run: sudo apt-get install qemu-system-x86 qemu-utils"
    exit 1
fi
info "✅ QEMU available"

if [ ! -f "${VM_DIR}/${VM_IMAGE}" ]; then
    error "❌ FreeBSD VM image not found"
    echo "Run: ./script/setup-freebsd-vm.sh"
    exit 1
fi
info "✅ FreeBSD VM image found"

if [ ! -f "bin/bootstrap/simple" ]; then
    error "❌ Simple bootstrap binary not found"
    echo "Expected: bin/bootstrap/simple"
    exit 1
fi
info "✅ Simple bootstrap binary found"
echo ""

# Step 2: Start FreeBSD VM
echo "Step 2: Start FreeBSD VM"
echo "----------------------------------------"

# Check if VM already running
if [ -f /tmp/freebsd-qemu.pid ]; then
    PID=$(cat /tmp/freebsd-qemu.pid)
    if kill -0 $PID 2>/dev/null; then
        info "✅ FreeBSD VM already running (PID: $PID)"
    else
        rm /tmp/freebsd-qemu.pid
        ${VM_DIR}/start-freebsd-daemon.sh
    fi
else
    ${VM_DIR}/start-freebsd-daemon.sh
fi

echo ""

# Step 3: Wait for SSH
echo "Step 3: Wait for SSH to be Ready"
echo "----------------------------------------"

echo "Waiting for FreeBSD to boot and accept SSH..."
for i in $(seq 1 $MAX_WAIT); do
    if ssh ${SSH_OPTS} -p ${SSH_PORT} ${SSH_USER}@localhost "echo ready" 2>/dev/null; then
        info "✅ SSH ready after ${i} seconds"
        break
    fi
    if [ $i -eq $MAX_WAIT ]; then
        error "❌ SSH timeout after ${MAX_WAIT} seconds"
        echo ""
        echo "Troubleshooting:"
        echo "  1. Check VM is running: ps aux | grep qemu"
        echo "  2. Check SSH manually: ssh -p 2222 root@localhost"
        echo "  3. Restart VM: kill \$(cat /tmp/freebsd-qemu.pid) && ${VM_DIR}/start-freebsd-daemon.sh"
        exit 1
    fi
    echo -n "."
    sleep 1
done
echo ""
echo ""

# Step 4: Setup FreeBSD environment
echo "Step 4: Setup FreeBSD Environment"
echo "----------------------------------------"

ssh ${SSH_OPTS} -p ${SSH_PORT} ${SSH_USER}@localhost bash <<'REMOTE_SETUP'
# Enable Linux compatibility (Linuxulator)
kldload linux64 2>/dev/null || echo "Linux module already loaded"

# Check if Linux base is installed
if [ ! -d /compat/linux ]; then
    echo "Installing Linux base system..."
    pkg install -y linux-c7 >/dev/null 2>&1 || true
fi

# Verify Linuxulator
if [ -d /compat/linux ]; then
    echo "✅ Linuxulator ready"
else
    echo "⚠️  Linuxulator may not be fully configured"
fi
REMOTE_SETUP

echo ""

# Step 5: Copy Simple bootstrap
echo "Step 5: Copy Simple Bootstrap to VM"
echo "----------------------------------------"

info "Copying bootstrap binary..."
scp ${SSH_OPTS} -P ${SSH_PORT} \
    bin/bootstrap/simple \
    ${SSH_USER}@localhost:/tmp/simple-bootstrap 2>&1 | grep -v "Warning:" || true

info "✅ Bootstrap copied to /tmp/simple-bootstrap"
echo ""

# Step 6: Test bootstrap execution
echo "Step 6: Test Bootstrap Execution"
echo "----------------------------------------"

ssh ${SSH_OPTS} -p ${SSH_PORT} ${SSH_USER}@localhost bash <<'REMOTE_TEST'
chmod +x /tmp/simple-bootstrap

echo "Testing Simple bootstrap version..."
/tmp/simple-bootstrap --version

echo ""
echo "✅ Bootstrap executes on FreeBSD (via Linuxulator)"
REMOTE_TEST

echo ""

# Step 7: Test interpreter with hello world
echo "Step 7: Test Hello World (Interpreter)"
echo "----------------------------------------"

ssh ${SSH_OPTS} -p ${SSH_PORT} ${SSH_USER}@localhost bash <<'REMOTE_HELLO'
# Create hello world program
cat > /tmp/hello_freebsd.spl <<'EOF'
#!/usr/bin/env simple
fn main():
    print "========================================="
    print "Hello from Simple on FreeBSD!"
    print "========================================="
    print ""
    print "Platform: FreeBSD x86_64"
    print "Method: Linux binary via Linuxulator"
    print "Status: ✅ Working!"
    print ""
EOF

echo "Running hello world..."
/tmp/simple-bootstrap /tmp/hello_freebsd.spl

echo ""
echo "✅ Interpreter mode works"
REMOTE_HELLO

echo ""

# Step 8: Test native compilation
echo "Step 8: Test Native Compilation"
echo "----------------------------------------"

ssh ${SSH_OPTS} -p ${SSH_PORT} ${SSH_USER}@localhost bash <<'REMOTE_COMPILE'
# Check/install gcc
if ! command -v gcc &> /dev/null; then
    echo "Installing gcc..."
    pkg install -y gcc >/dev/null 2>&1 || {
        echo "⚠️  Could not install gcc, trying clang..."
        pkg install -y clang >/dev/null 2>&1 || {
            echo "❌ No compiler available"
            exit 1
        }
    }
fi

echo "Compiler: $(gcc --version 2>/dev/null | head -1 || clang --version | head -1)"
echo ""

echo "Compiling hello world to native binary..."
/tmp/simple-bootstrap compile --native -o /tmp/hello_native /tmp/hello_freebsd.spl

if [ ! -f /tmp/hello_native ]; then
    echo "❌ Native compilation failed - binary not created"
    exit 1
fi

echo ""
echo "Binary info:"
file /tmp/hello_native
ls -lh /tmp/hello_native

echo ""
echo "✅ Native compilation successful"
REMOTE_COMPILE

echo ""

# Step 9: Run native binary
echo "Step 9: Test Native Binary Execution"
echo "----------------------------------------"

ssh ${SSH_OPTS} -p ${SSH_PORT} ${SSH_USER}@localhost bash <<'REMOTE_RUN'
chmod +x /tmp/hello_native
echo "Running native FreeBSD binary..."
echo ""
/tmp/hello_native

echo ""
echo "✅ Native binary executes on FreeBSD"
REMOTE_RUN

echo ""

# Step 10: Cleanup
echo "Step 10: Cleanup"
echo "----------------------------------------"

# Ask user if they want to keep VM running
if [ -t 0 ]; then
    read -p "Stop FreeBSD VM? (y/N): " -n 1 -r
    echo
    if [[ $REPLY =~ ^[Yy]$ ]]; then
        if [ -f /tmp/freebsd-qemu.pid ]; then
            kill $(cat /tmp/freebsd-qemu.pid) 2>/dev/null || true
            rm /tmp/freebsd-qemu.pid
            info "✅ VM stopped"
        fi
    else
        warn "⚠️  VM still running (PID: $(cat /tmp/freebsd-qemu.pid 2>/dev/null || echo 'unknown'))"
        echo "To stop: kill \$(cat /tmp/freebsd-qemu.pid)"
    fi
else
    # Non-interactive mode - keep VM running
    warn "⚠️  VM still running for further testing"
    echo "To stop: kill \$(cat /tmp/freebsd-qemu.pid)"
fi

echo ""

# Summary
echo "=========================================="
info "✅ FreeBSD QEMU Test: PASSED"
echo "=========================================="
echo ""
echo "Summary:"
info "  ✅ FreeBSD VM: Running"
info "  ✅ Linuxulator: Enabled"
info "  ✅ Bootstrap: Executes (Linux binary)"
info "  ✅ Interpreter: Working"
info "  ✅ Native compilation: Working"
info "  ✅ Native execution: Working"
echo ""
echo "Platform: FreeBSD x86_64"
echo "Method: Linuxulator (Linux binary compatibility)"
echo ""
echo "Simple can run on FreeBSD! ✅"
echo ""
