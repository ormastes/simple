# FreeBSD Quick Reference

Essential FreeBSD commands and workflows for Simple development.

---

## VM Management

### Start/Stop

```bash
# Start VM (background)
~/vms/freebsd/start-freebsd-daemon.sh

# Start VM (interactive - serial console)
~/vms/freebsd/start-freebsd.sh

# Check if running
cat /tmp/freebsd-qemu.pid && ps -p $(cat /tmp/freebsd-qemu.pid)

# Stop VM
kill $(cat /tmp/freebsd-qemu.pid)
```

### SSH Access

```bash
# SSH into VM
ssh -p 2222 root@localhost

# Copy file to VM
scp -P 2222 file.txt root@localhost:/tmp/

# Copy file from VM
scp -P 2222 root@localhost:/tmp/file.txt ./

# Execute command
ssh -p 2222 root@localhost 'uname -a'
```

---

## Package Management

### Install Packages

```bash
# Update repository
pkg update

# Install package
pkg install cmake

# Search package
pkg search llvm

# Show package info
pkg info cmake

# List installed
pkg info
```

### Common Packages

```bash
# Development tools
pkg install cmake llvm gmake git wget

# Libraries
pkg install glib pixman

# Linux compatibility
pkg install linux-c7
```

---

## System Configuration

### Enable Services

```bash
# Enable SSH
sysrc sshd_enable="YES"
service sshd start

# Enable Linuxulator
sysrc linux_enable="YES"
kldload linux64

# Enable on boot
echo 'linux_load="YES"' >> /boot/loader.conf
```

### System Info

```bash
# OS version
uname -a
freebsd-version

# CPU info
sysctl hw.model hw.ncpu

# Memory
sysctl hw.physmem hw.usermem

# Disk usage
df -h
```

---

## File Operations

### Differences from Linux

| Operation | Linux | FreeBSD |
|-----------|-------|---------|
| SHA256 | `sha256sum file` | `sha256 file` |
| GNU Make | `make` | `gmake` |
| Locate DB | `updatedb` | `locate.updatedb` |
| Install | `apt install` | `pkg install` |

### Common Commands

```bash
# Same as Linux
ls, cat, grep, find, tar, gzip, wget, curl, git

# FreeBSD-specific
sha256 file              # SHA256 hash (quiet: sha256 -q file)
gmake                    # GNU Make (BSD make is 'make')
pkg install              # Package install
sockstat -4 -l           # Listening ports (like netstat -tuln)
```

---

## Building Simple

### Bootstrap from Scratch

```bash
# Clone repository
git clone https://github.com/yourorg/simple.git
cd simple

# Install prerequisites
pkg install cmake llvm gmake

# Bootstrap
./scripts/bootstrap/bootstrap-from-scratch-freebsd.sh

# Test
bin/simple --version
bin/simple build
bin/simple test
```

### Build Options

```bash
# Fast build (skip verification)
./scripts/bootstrap/bootstrap-from-scratch-freebsd.sh --skip-verify

# Parallel build
./scripts/bootstrap/bootstrap-from-scratch-freebsd.sh --jobs=8

# Custom compiler
./scripts/bootstrap/bootstrap-from-scratch-freebsd.sh --cc=g++

# Keep artifacts
./scripts/bootstrap/bootstrap-from-scratch-freebsd.sh --keep-artifacts

# Verbose
./scripts/bootstrap/bootstrap-from-scratch-freebsd.sh --verbose
```

---

## Testing

### Run Tests

```bash
# All tests
bin/simple test

# Specific test
bin/simple test test/std/string_spec.spl

# Slow tests only
bin/simple test --only-slow

# List tests
bin/simple test --list
```

### Quality Checks

```bash
# Lint
bin/simple build lint

# Format
bin/simple build fmt

# All checks
bin/simple build check
```

---

## Linuxulator (Linux Binary Compat)

### Setup

```bash
# Load kernel module
kldload linux64

# Install Linux base
pkg install linux-c7

# Enable on boot
sysrc linux_enable="YES"

# Verify
kldstat | grep linux
```

### Usage

```bash
# Run Linux binary
/path/to/linux-simple --version

# Check binary type
file /path/to/linux-simple
# Output: ELF 64-bit LSB executable, x86-64, dynamically linked, for GNU/Linux

# Debug
brandelf /path/to/linux-simple
```

---

## Networking

### Port Forwarding

VM SSH forwarding: `localhost:2222` → VM `port 22`

```bash
# QEMU forwards automatically
-netdev user,id=net0,hostfwd=tcp::2222-:22
```

### Check Ports

```bash
# Listening ports
sockstat -4 -l

# All connections
sockstat -4
```

### Firewall

```bash
# Check firewall status
service pf status

# Disable (if needed for testing)
service pf stop
```

---

## Kernel Modules

### Load Modules

```bash
# Load module
kldload module_name

# Unload module
kldunload module_name

# List loaded
kldstat

# Search available
ls /boot/kernel/*.ko | grep linux
```

### Common Modules

```bash
kldload linux64    # Linux binary compatibility
kldload fdescfs    # File descriptor filesystem
kldload linprocfs  # Linux proc filesystem
```

---

## Performance

### CPU Info

```bash
# CPU model
sysctl hw.model

# Core count
sysctl hw.ncpu

# CPU frequency
sysctl dev.cpu.0.freq
```

### Memory

```bash
# Total physical memory
sysctl hw.physmem

# Available memory
sysctl hw.usermem

# Memory stats
vmstat -s
```

### Process Monitor

```bash
# Top (like Linux)
top

# Process tree
pstree

# Kill process
kill PID
pkill process_name
```

---

## Common Issues

### "Command not found"

```bash
# Install package
pkg install <package>

# Or check path
echo $PATH
rehash  # (for tcsh/csh)
```

### "Permission denied"

```bash
# Make executable
chmod +x script.sh

# Run as root
su -
# or
sudo <command>  # (if sudo installed)
```

### "gmake: not found"

```bash
# FreeBSD 'make' is BSD make
# Install GNU make
pkg install gmake

# Use gmake explicitly
gmake -j4
```

---

## Tips & Tricks

### Aliases (add to ~/.profile or ~/.bashrc)

```bash
# GNU tools
alias make='gmake'

# Quick SSH to VM (from host)
alias freebsd='ssh -p 2222 root@localhost'

# Package shortcuts
alias pkgi='pkg install'
alias pkgs='pkg search'
```

### Environment

```bash
# Set default editor
export EDITOR=vi

# Add to PATH
export PATH=$PATH:/usr/local/bin

# Compiler flags
export CFLAGS="-O2"
export CXXFLAGS="-O2"
```

### Shortcuts

```bash
# History
!!              # Repeat last command
!ssh            # Repeat last ssh command
Ctrl+R          # Reverse search history

# Navigation
cd -            # Previous directory
pushd / popd    # Directory stack

# Job control
Ctrl+Z          # Suspend
bg              # Background
fg              # Foreground
jobs            # List jobs
```

---

## Resources

### Documentation

- FreeBSD Handbook: https://docs.freebsd.org/en/books/handbook/
- Man pages: `man <command>`
- Port search: https://www.freshports.org/

### Help

```bash
# Man page
man pkg
man clang

# Command help
pkg help
llvm-config --help

# System manual
man hier     # Filesystem hierarchy
man rc       # Startup scripts
```

---

## Emergency

### Serial Console

If SSH fails, use serial console:

```bash
# Start VM interactively
~/vms/freebsd/start-freebsd.sh

# Login at console prompt
# Username: root
# Password: <your password>
```

### Reset Root Password

1. Boot to single-user mode (VM boot prompt)
2. Press `SPACE` at boot menu
3. Type `boot -s`
4. At prompt: `mount -u /`
5. `passwd root`
6. `exit`

### Force Stop VM

```bash
# Kill QEMU
pkill -9 -f "qemu-system.*freebsd"
rm -f /tmp/freebsd-qemu.pid
```

---

## Cheat Sheet

| Task | Command |
|------|---------|
| Start VM | `~/vms/freebsd/start-freebsd-daemon.sh` |
| SSH to VM | `ssh -p 2222 root@localhost` |
| Install pkg | `pkg install <name>` |
| Update pkgs | `pkg update && pkg upgrade` |
| Load module | `kldload <module>` |
| Enable svc | `sysrc <name>_enable="YES"` |
| Start svc | `service <name> start` |
| SHA256 | `sha256 file` |
| GNU make | `gmake` |
| Disk usage | `df -h` |
| Processes | `top` or `ps aux` |
| Ports | `sockstat -4 -l` |
| Reboot | `shutdown -r now` |
| Halt | `shutdown -p now` |

---

Happy FreeBSD hacking! 🐡
