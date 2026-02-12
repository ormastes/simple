#!/bin/bash
# Configure SSH in FreeBSD VM (One-Time Setup)
#
# This script automates the initial SSH configuration for FreeBSD VM.
# Run this once before using --qemu-freebsd bootstrap.

set -euo pipefail

PORT=${1:-2222}

echo "================================================================"
echo "  FreeBSD VM SSH Configuration"
echo "================================================================"
echo ""
echo "This script will configure SSH access to the FreeBSD VM."
echo "VM must be running on port $PORT"
echo ""

# Check if VM is running
if ! nc -z localhost $PORT 2>/dev/null; then
    echo "ERROR: No VM found on port $PORT"
    echo ""
    echo "Start the VM first with:"
    echo "  $HOME/vms/freebsd/start-freebsd-daemon.sh"
    echo ""
    echo "Or manually:"
    echo "  qemu-system-x86_64 \\"
    echo "    -machine accel=kvm:tcg \\"
    echo "    -cpu host -m 4G -smp 4 \\"
    echo "    -drive file=build/freebsd/vm/FreeBSD-14.3-RELEASE-amd64.qcow2,format=qcow2,if=virtio \\"
    echo "    -net nic,model=virtio \\"
    echo "    -net user,hostfwd=tcp::$PORT-:22 \\"
    echo "    -display none \\"
    echo "    -daemonize \\"
    echo "    -pidfile /tmp/freebsd-qemu.pid"
    exit 1
fi

echo "VM detected on port $PORT"
echo ""

# Generate SSH key if needed
SSH_KEY="$HOME/.ssh/simple_freebsd_vm"
if [ ! -f "$SSH_KEY" ]; then
    echo "Generating SSH key: $SSH_KEY"
    ssh-keygen -t ed25519 -f "$SSH_KEY" -N "" -C "simple-freebsd-vm"
    echo ""
fi

# Instructions for manual configuration
cat << 'EOF'
================================================================
  Manual Configuration Required (One-Time, ~2 minutes)
================================================================

The FreeBSD VM requires initial setup via console.

1. Connect to VM console:
   - The VM is running in the background
   - You need to connect to its serial console

2. Login:
   - Username: root
   - Password: (press Enter - no password by default)

3. Run these commands:

   # Enable SSH daemon
   echo 'sshd_enable="YES"' >> /etc/rc.conf
   service sshd start

   # Set root password (or press Enter for no password)
   passwd

   # Create freebsd user
   pw useradd -n freebsd -m -s /bin/sh -G wheel
   passwd freebsd

   # Enable passwordless sudo
   pkg install -y sudo
   echo '%wheel ALL=(ALL) NOPASSWD: ALL' >> /usr/local/etc/sudoers

   # Install required packages
   pkg install -y cmake gmake git

4. Exit and test:
   exit

   # Test SSH connection
   ssh -p PORT freebsd@localhost

================================================================

ALTERNATIVE: Use cross-compilation (no VM setup needed)
========================================================

If you prefer not to configure the VM, you can build for FreeBSD
using cross-compilation:

  # Cross-compile FreeBSD seed compiler (already working)
  cd build/freebsd
  cmake -S ../../seed -B . \
    -DCMAKE_SYSTEM_NAME=FreeBSD \
    -DCMAKE_SYSTEM_PROCESSOR=x86_64 \
    -DCMAKE_C_COMPILER=clang \
    -DCMAKE_CXX_COMPILER=clang++ \
    -DCMAKE_SYSROOT=/opt/sysroots/freebsd-x86_64

  make -j$(nproc)

  # Result: FreeBSD seed compiler at build/freebsd/seed_cpp

EOF

# Provide simplified one-liner for testing SSH
echo ""
echo "To test SSH after configuration:"
echo "  ssh -o StrictHostKeyChecking=no -p $PORT freebsd@localhost 'echo SSH works'"
echo ""
