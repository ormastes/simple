#!/bin/bash
# Setup FreeBSD VM for Simple Testing
# Downloads FreeBSD VM image and prepares QEMU environment

set -e

echo "======================================"
echo "FreeBSD VM Setup for Simple Testing"
echo "======================================"
echo ""

VM_DIR="${HOME}/vms/freebsd"
FREEBSD_VERSION="14.3-RELEASE"
FREEBSD_ARCH="amd64"

# Step 1: Check/Install QEMU
echo "Step 1: Verify QEMU Installation"
echo "--------------------------------------"

if ! command -v qemu-system-x86_64 &> /dev/null; then
    echo "❌ QEMU not found"
    echo ""
    echo "Please install QEMU:"
    echo "  sudo apt-get install -y qemu-system-x86 qemu-utils"
    echo ""
    echo "Or run with sudo to auto-install:"
    echo "  sudo $0"
    exit 1
fi

echo "✅ QEMU installed: $(qemu-system-x86_64 --version | head -1)"
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
    ls -lh ${IMAGE_FILE}
else
    echo "Downloading FreeBSD ${FREEBSD_VERSION} (${FREEBSD_ARCH})..."
    echo "URL: ${IMAGE_URL}"
    echo ""

    wget --progress=bar:force -O ${IMAGE_FILE}.xz ${IMAGE_URL}

    echo ""
    echo "Extracting image..."
    unxz ${IMAGE_FILE}.xz

    echo "✅ Downloaded and extracted: ${IMAGE_FILE}"
    ls -lh ${IMAGE_FILE}
fi

echo ""

# Step 4: Create start script
echo "Step 4: Create VM Start Script"
echo "--------------------------------------"

cat > ${VM_DIR}/start-freebsd.sh <<'EOF'
#!/bin/bash
# Start FreeBSD VM with SSH forwarding
VM_DIR="$(dirname "$0")"
cd "${VM_DIR}"

echo "========================================="
echo "Starting FreeBSD VM"
echo "========================================="
echo ""
echo "Connection:"
echo "  SSH: ssh -p 2222 root@localhost"
echo ""
echo "Control:"
echo "  Stop VM: kill $(cat /tmp/freebsd-qemu.pid 2>/dev/null || echo 'PID_NOT_FOUND')"
echo "  Or press Ctrl+C in this terminal"
echo ""

qemu-system-x86_64 \
  -machine type=q35,accel=kvm:tcg \
  -cpu host \
  -smp 4 \
  -m 4G \
  -drive file=FreeBSD-14.3-RELEASE-amd64.qcow2,if=virtio,format=qcow2 \
  -netdev user,id=net0,hostfwd=tcp::2222-:22 \
  -device virtio-net-pci,netdev=net0 \
  -display none \
  -serial mon:stdio
EOF

chmod +x ${VM_DIR}/start-freebsd.sh
echo "✅ Created: ${VM_DIR}/start-freebsd.sh"
echo ""

# Step 5: Create daemon start script
cat > ${VM_DIR}/start-freebsd-daemon.sh <<'EOF'
#!/bin/bash
# Start FreeBSD VM in background (daemon mode)
VM_DIR="$(dirname "$0")"
cd "${VM_DIR}"

if [ -f /tmp/freebsd-qemu.pid ]; then
    PID=$(cat /tmp/freebsd-qemu.pid)
    if kill -0 $PID 2>/dev/null; then
        echo "FreeBSD VM already running (PID: $PID)"
        exit 0
    fi
fi

echo "Starting FreeBSD VM in background..."

qemu-system-x86_64 \
  -machine type=q35,accel=kvm:tcg \
  -cpu host \
  -smp 2 \
  -m 2G \
  -drive file=FreeBSD-14.3-RELEASE-amd64.qcow2,if=virtio,format=qcow2 \
  -netdev user,id=net0,hostfwd=tcp::2222-:22 \
  -device virtio-net-pci,netdev=net0 \
  -display none \
  -daemonize \
  -pidfile /tmp/freebsd-qemu.pid

sleep 2

if [ -f /tmp/freebsd-qemu.pid ]; then
    PID=$(cat /tmp/freebsd-qemu.pid)
    echo "✅ FreeBSD VM started (PID: $PID)"
    echo ""
    echo "SSH: ssh -p 2222 root@localhost"
    echo "Stop: kill $PID"
else
    echo "❌ Failed to start VM"
    exit 1
fi
EOF

chmod +x ${VM_DIR}/start-freebsd-daemon.sh
echo "✅ Created: ${VM_DIR}/start-freebsd-daemon.sh"
echo ""

# Summary
echo "======================================"
echo "✅ FreeBSD VM Setup Complete"
echo "======================================"
echo ""
echo "Location: ${VM_DIR}"
echo "Image:    ${IMAGE_FILE} ($(ls -lh ${IMAGE_FILE} | awk '{print $5}'))"
echo ""
echo "Usage:"
echo "  • Interactive: ${VM_DIR}/start-freebsd.sh"
echo "  • Background:  ${VM_DIR}/start-freebsd-daemon.sh"
echo ""
echo "First-time setup:"
echo "  1. Start VM and wait for boot"
echo "  2. Login as 'root' (default password: empty or 'root')"
echo "  3. Set password: passwd"
echo "  4. Enable SSH: echo 'sshd_enable=\"YES\"' >> /etc/rc.conf && service sshd start"
echo "  5. Enable Linuxulator: kldload linux64 && sysrc linux_enable=\"YES\""
echo ""
echo "Test Simple:"
echo "  simple/script/test-freebsd-qemu.sh"
echo ""
