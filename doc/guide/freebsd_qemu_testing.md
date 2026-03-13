# FreeBSD QEMU Testing Guide

Testing the Simple Language Compiler on FreeBSD 14.4 via QEMU.

## Pre-configured Image

A fully configured FreeBSD 14.4 VM image is stored at:

```
~/vms/freebsd/FreeBSD-14.4-configured-simple.qcow2
```

**What's pre-configured:**
- SSH root login (pubkey auth with `~/.ssh/id_rsa`)
- Root password: `freebsd123`
- Packages: rust 1.92, clang 19.1.7, cmake 3.31, git, rsync, gmake
- Rust seed pre-built at `~/simple/src/compiler_rust/target/bootstrap/simple`
- Project synced to `~/simple/`

**Original (unmodified) image:**
```
~/vms/freebsd/FreeBSD-14.4-RELEASE-amd64.qcow2
```

## Quick Start

### 1. Start the VM

```bash
qemu-system-x86_64 \
  -machine type=q35,accel=kvm:tcg \
  -cpu host -smp 4 -m 4G \
  -drive file=$HOME/vms/freebsd/FreeBSD-14.4-configured-simple.qcow2,if=virtio,format=qcow2 \
  -netdev user,id=net0,hostfwd=tcp::2222-:22 \
  -device virtio-net-pci,netdev=net0 \
  -display none \
  -daemonize \
  -pidfile /tmp/freebsd-qemu.pid
```

### 2. SSH into the VM

```bash
ssh -p 2222 root@localhost
```

### 3. Sync project files

```bash
rsync -az --delete \
  -e "ssh -p 2222 -o StrictHostKeyChecking=no" \
  --exclude='.git' --exclude='build' --exclude='.jj' --exclude='target' \
  --exclude='*.o' --exclude='*.a' \
  . root@localhost:~/simple/
```

### 4. Run all tests

```bash
SSH="ssh -p 2222 root@localhost"
$SSH "cd ~/simple && src/compiler_rust/target/bootstrap/simple test"
$SSH "cd ~/simple && src/compiler_rust/target/bootstrap/simple test --only-slow"
```

## Building the Rust Seed (if needed)

If the pre-configured image doesn't have the Rust seed or it's outdated:

```bash
ssh -p 2222 root@localhost "cd ~/simple/src/compiler_rust && cargo build --profile bootstrap -p simple-driver"
```

Takes ~6 minutes on 4 vCPUs.

## Full Compiler Bootstrap on FreeBSD

The self-hosted binary (`bin/release/simple`) is a Linux ELF. On FreeBSD, use the
Rust seed interpreter to run tests. The Rust seed provides full test runner
functionality in interpreter mode.

**Why not a native FreeBSD binary?**

The self-hosted bootstrap requires `bin/release/simple build bootstrap` which needs
the full compiler to already exist. Cross-compilation from Linux generates Linux ELFs.
The C bootstrap (`build/simple`) is stubs only. The proper path for a native FreeBSD
binary is:

1. Build Rust seed on FreeBSD (works)
2. Use Rust seed to compile Simple source (blocked by `CompilerDriver.compile` extern)
3. Once the Rust runtime registers that extern, native FreeBSD binaries will work

For now, the Rust seed interpreter runs all tests correctly on FreeBSD.

## Setting Up a Fresh Image

If starting from a clean FreeBSD 14.4 RELEASE qcow2:

### Step 1: Boot into single-user mode

```bash
# Start VM with monitor socket
qemu-system-x86_64 \
  -machine type=q35,accel=kvm:tcg \
  -cpu host -smp 4 -m 4G \
  -drive file=FreeBSD-14.4-RELEASE-amd64.qcow2,if=virtio,format=qcow2 \
  -netdev user,id=net0,hostfwd=tcp::2222-:22 \
  -device virtio-net-pci,netdev=net0 \
  -display none \
  -serial unix:/tmp/freebsd-serial.sock,server,nowait \
  -monitor unix:/tmp/freebsd-monitor.sock,server,nowait \
  -daemonize \
  -pidfile /tmp/freebsd-qemu.pid
```

Reboot via monitor and press `2` at the FreeBSD bootloader for single-user mode:

```python
# Use Python to send commands via QEMU monitor
import socket
sock = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
sock.connect('/tmp/freebsd-monitor.sock')
sock.send(b'system_reset\n')  # reboot
# Wait ~10s, then send '2' for single-user mode
sock.send(b'sendkey 2\n')
```

### Step 2: Configure in single-user mode

At the `root@:/ #` prompt:

```sh
mount -u -w /
mount -a
echo 'freebsd123' | pw usermod root -h 0
```

### Step 3: Exit to multi-user mode

```sh
exit
```

### Step 4: Configure SSH (after multi-user boot)

Login via console as root, then:

```sh
# Write clean sshd_config
cat > /etc/ssh/sshd_config << 'EOF'
PermitRootLogin yes
PasswordAuthentication yes
KbdInteractiveAuthentication yes
PubkeyAuthentication yes
AuthorizedKeysFile .ssh/authorized_keys
UseDNS no
Subsystem sftp /usr/libexec/sftp-server
EOF

# Add SSH key (serve from host via HTTP on port 8899)
mkdir -p /root/.ssh && chmod 700 /root/.ssh
fetch -o /root/.ssh/authorized_keys http://10.0.2.2:8899/authorized_keys
chmod 600 /root/.ssh/authorized_keys

# Start sshd
service sshd start

# Enable sshd on boot
sysrc sshd_enable=YES
```

**Note:** `10.0.2.2` is the QEMU user-mode networking gateway to the host.
Start an HTTP server on the host: `python3 -m http.server 8899 --directory /tmp/keys`

### Step 5: Install packages

```bash
ssh -p 2222 root@localhost "pkg install -y cmake gmake git rsync rust"
```

### Step 6: Save the configured image

```bash
# Shut down VM cleanly
ssh -p 2222 root@localhost "shutdown -p now"
# Wait for shutdown, then copy
cp FreeBSD-14.4-RELEASE-amd64.qcow2 FreeBSD-14.4-configured-simple.qcow2
```

## VM Specs

| Setting | Value |
|---------|-------|
| OS | FreeBSD 14.4-RELEASE amd64 |
| Image format | qcow2 |
| RAM | 4 GB |
| CPUs | 4 |
| Disk | ~28 GB used |
| SSH port | 2222 (forwarded) |
| SSH user | root |
| Acceleration | KVM (fallback: TCG) |
| Clang | 19.1.7 (system) |
| Rust | 1.92.0 |
| CMake | 3.31.10 |

## Stopping the VM

```bash
# Graceful
ssh -p 2222 root@localhost "shutdown -p now"

# Force
kill $(cat /tmp/freebsd-qemu.pid)
```
