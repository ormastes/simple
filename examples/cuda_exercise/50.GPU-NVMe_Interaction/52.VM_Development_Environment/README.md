# 🎯 Part 52: VM Development Environment for GPUDirect Testing
**Status**: ⚠️ **DOCUMENTATION-ONLY** - Scripts referenced are external (from `llm_storage` project)

**Goal**: Set up a QEMU-based virtual machine with NVMe device emulation and GPU passthrough for safe, reproducible GPUDirect experimentation using automated scripts from the `llm_storage` project.

> **NOTE**: This module contains documentation only. The scripts referenced below are maintained externally.
> To use these scripts, either:
> 1. Copy scripts from the `llm_storage` project into `scripts/` directory, OR
> 2. Reference scripts directly from their external repository

## Project Structure (Reference)
```
52.VM_Development_Environment/
├── README.md          - This documentation (DOCUMENTATION-ONLY)
└── scripts/           - ⚠️ NOT INCLUDED - External automation scripts
    ├── 0.setup_dev_environment.sh  - Complete dev toolchain installer
    ├── _0.setup_qemu.sh            - Build QEMU-NVMe from source
    ├── _1.install_os.sh            - Download and install Ubuntu Server
    ├── 1.run_code.sh               - VS Code tunnel server launcher
    ├── 2.setup_kernel_module_sudo.sh - Password-less kernel module operations
    ├── _2.run_qemu.sh              - Run VM with GPU/NVMe passthrough
    └── _3.setup_libvirt.sh         - Setup libvirt for VM management
```

## Quick Navigation
- [52.1 Virtualized Lab Overview](#521-virtualized-lab-overview)
- [52.2 System Requirements](#522-system-requirements)
- [52.3 QEMU VM Scripts](#523-qemu-vm-scripts)
- [52.4 Developer Environment Scripts](#524-developer-environment-scripts)
- [52.5 GPU Passthrough Setup](#525-gpu-passthrough-setup)
- [52.6 VM Configuration and Disk Formats](#526-vm-configuration-and-disk-formats)
- [52.7 Troubleshooting](#527-troubleshooting)
- [52.8 Module 53: NVMe VFIO Test Scripts](#528-module-53-nvme-vfio-test-scripts)
- [Build & Run](#build--run)
- [Summary](#summary)

---

## **52.1 Virtualized Lab Overview**

This module provides automated VM provisioning for safe GPUDirect development by isolating VFIO, custom kernel modules, and NVMe experiments from your host system. The virtualization environment enables disk snapshots, reproducible builds, and collaborative development through shared automation scripts.

This setup provides:

**QEMU VM Environment:**
- **QEMU with NVMe emulation** from [OpenChannelSSD/qemu-nvme](https://github.com/OpenChannelSSD/qemu-nvme) for accurate NVMe device simulation
- **GPU passthrough** using VFIO for direct GPU access in VMs, enabling real GPUDirect testing
- **Ubuntu Server** VMs with version selection (24.04 LTS, 24.10, 25.04, 25.10) for flexibility
- **Headless auto-detection** - automatically uses `-nographic` for server environments
- **SSH access** on port 6665 for easy remote connectivity
- **Multi-core compilation** for faster QEMU builds

**Developer Environment:**
- **Complete dev toolchain** - clang, gcc, cmake, ninja, build tools for C/C++ development
- **Multiple languages** - Python, Node.js, Rust, Go for diverse project needs
- **NVIDIA & CUDA** - Optional CUDA 13.0 and latest drivers for GPU development
- **Linux kernel development** - KUNIT, headers, kernel tools for driver development
- **Containers** - Docker CE with user permissions for containerized workflows
- **VS Code Server** - Remote tunnel with autostart support for remote editing
- **Terminal tools** - tmux, vim, htop, ripgrep, fzf for productivity

### **52.1.1 Safety and Reproducibility**

The VM approach ensures host safety by isolating potentially unstable kernel modules and driver experiments. All provisioning scripts copy from the `llm_storage` project, bind VM assets under `cuda_exercise/data/`, and expose the repository through Virtio-FS. This pattern keeps the host environment stateless while guaranteeing that downstream modules (Parts 53-57) inherit consistent PCI topology, CUDA driver versions, and kernel headers.

All large artifacts (installer ISOs, QCOW2 disks, NVMe playground image) live directly inside `data/` so you can inspect and snapshot them without drilling into subdirectories.

### **52.1.2 Automation and CI/CD Support**

All scripts support non-interactive execution for automated workflows through sudo password arguments or environment variables. This enables integration with CI/CD pipelines, Docker builds, and automated testing frameworks without manual intervention.

---

## **52.2 System Requirements**

This section outlines the host capabilities required to run GPU passthrough together with NVMe emulation. Understanding these requirements before starting prevents common setup failures and ensures smooth VM operation.

### **52.2.1 Hardware Requirements**

Verify your host meets these hardware capabilities before investing time in the virtualization setup. Missing virtualization support or IOMMU will prevent GPU passthrough from working correctly.

**Required Hardware:**
- **CPU with virtualization support** (Intel VT-x or AMD-V) - Required for KVM acceleration
  - **KVM Recommended**: For best performance, enable KVM acceleration (10-50x faster than software emulation)
  - **Software Fallback**: Works without KVM (slower, uses `-cpu max` instead of `-cpu host`)
- **IOMMU support** (Intel VT-d or AMD-Vi) - Required for GPU passthrough
- **NVIDIA GPU** (optional for GPU passthrough, Ampere tested, Pascal+ recommended)
- **At least 16GB RAM** recommended (32GB for comfortable development)
- **200GB+ disk space** for QCOW2 images, ISOs, kernel sources, and build artifacts

**Verify virtualization support:**
```bash
# Check CPU virtualization support (should return > 0)
egrep -c '(vmx|svm)' /proc/cpuinfo

# Check KVM device availability
ls -l /dev/kvm
# Should show: crw-rw---- 1 root kvm

# Load KVM modules if needed
sudo modprobe kvm kvm_intel  # For Intel CPUs
sudo modprobe kvm kvm_amd    # For AMD CPUs

# Add user to kvm group
sudo usermod -aG kvm $USER
# Log out and log back in for group changes to take effect
```

### **52.2.2 Software Prerequisites**

Install these software packages on the host before running the VM scripts. The `_0.setup_qemu.sh` script automatically installs most dependencies, but IOMMU configuration requires manual setup.

**Required Software:**
- **Ubuntu 22.04 or later** (host OS) - Tested on 22.04 and 24.04
- **Root/sudo access** - Required for VFIO binding and VM management
- **OVMF** (UEFI firmware, recommended for modern boot):
  ```bash
  # Ubuntu/Debian (automatically installed by _0.setup_qemu.sh)
  sudo apt install ovmf

  # Fedora/RHEL
  sudo dnf install edk2-ovmf

  # Arch Linux
  sudo pacman -S edk2-ovmf
  ```
- **Build dependencies** - Automatically installed by `_0.setup_qemu.sh`:
  - git, ninja-build, pkg-config, libglib2.0-dev, libpixman-1-dev
  - libfdt-dev, zlib1g-dev, flex, bison, libslirp-dev

**IOMMU Configuration:**

Enable IOMMU in BIOS/UEFI firmware first, then configure the kernel:

```bash
# Edit /etc/default/grub
sudo nano /etc/default/grub

# For Intel CPUs:
GRUB_CMDLINE_LINUX_DEFAULT="quiet splash intel_iommu=on"

# For AMD CPUs:
GRUB_CMDLINE_LINUX_DEFAULT="quiet splash amd_iommu=on"

# Update GRUB and reboot
sudo update-grub
sudo reboot
```

**Verify IOMMU is enabled:**
```bash
# For Intel:
dmesg | grep VT-d
# Should show: "DMAR: Intel(R) Virtualization Technology for Directed I/O"

# For AMD:
dmesg | grep AMD-Vi
# Should show: "AMD-Vi: Initialized for Directed I/O"
```

### **52.2.3 BIOS/UEFI Settings**

Enable the following settings in your system BIOS/UEFI for KVM acceleration and GPU passthrough:

- **CPU Virtualization** (Intel VT-x / AMD-V) - Required for KVM
- **IOMMU** (Intel VT-d / AMD-Vi) - Required for GPU passthrough

**Note**: Settings location varies by manufacturer (typically under Advanced → CPU Configuration or Chipset).

---

## **52.3 QEMU VM Scripts**

This section details the QEMU-focused automation scripts that build the virtualization environment, install guest operating systems, and manage VM lifecycle. Each script supports both interactive and automated execution modes for flexibility.

### **52.3.1 Building QEMU with NVMe Support**

The `_0.setup_qemu.sh` script builds QEMU from the OpenChannelSSD fork, which provides accurate NVMe emulation for storage experiments. This script handles all dependencies and performs multi-core builds for speed.

**Purpose**: Build and install QEMU-NVMe from source with all required dependencies.

**Source**: `scripts/_0.setup_qemu.sh`

**What it does**:
- Checks for existing QEMU installation and offers incremental updates
- Installs all required dependencies including **OVMF** for UEFI boot
- Clones/updates qemu-nvme repository from [OpenChannelSSD/qemu-nvme](https://github.com/OpenChannelSSD/qemu-nvme)
- Builds QEMU with multi-core support (uses all CPU cores via `$(nproc)`)
- Installs to `${HOME}/qemu-nvme/bin/qemu-system-x86_64`
- Optionally creates initial disk images

**Usage**:
```bash
# Interactive mode (default)
./scripts/_0.setup_qemu.sh

# Non-interactive mode (no prompts, smart defaults)
./scripts/_0.setup_qemu.sh --non-interactive

# Force rebuild everything
./scripts/_0.setup_qemu.sh --force

# Create disk images automatically
./scripts/_0.setup_qemu.sh --create-disks

# Combine options for CI/CD
./scripts/_0.setup_qemu.sh --non-interactive --create-disks --sudo-password mypass
```

**Build time**: Approximately 10-30 minutes depending on CPU cores.

**Expected output**:
```
✓ QEMU dependencies installed
✓ Cloning qemu-nvme from GitHub...
✓ Building QEMU (using 24 cores)...
✓ QEMU installed to /home/user/qemu-nvme/bin/
✓ QEMU version: QEMU emulator version 8.1.0
```

### **52.3.2 Installing Ubuntu Server Guest**

The `_1.install_os.sh` script automates ISO downloading, disk creation, and VM installation. It supports multiple Ubuntu versions and provides a clean installation workflow.

**Purpose**: Download Ubuntu Server ISO and install OS in VM.

**Source**: `scripts/_1.install_os.sh`

**What it does**:
- Lists available Ubuntu Server versions (24.04 LTS, 24.10, 25.04, 25.10)
- Downloads ISO if not present (auto-detects existing ISOs)
- Creates version-specific VM disk images (e.g., `ubuntu_server_24.10_nvme_qemu.qcow2`)
- Detects headless sessions and runs a fully unattended autoinstall via cloud-init
- Launches the interactive installer when a GUI is available

**Supported Ubuntu versions**:
- Ubuntu 24.04 LTS (Server)
- Ubuntu 24.10 (Server)
- Ubuntu 25.04 (Server)
- Ubuntu 25.10 (Server)

**Usage**:
```bash
# Interactive mode - prompts for version selection
./scripts/_1.install_os.sh

# Specify version explicitly (e.g., Ubuntu 24.04 LTS)
./scripts/_1.install_os.sh 24.04

# Specify version by index (1-4, based on sorted list)
./scripts/_1.install_os.sh 2

# Provide sudo password non-interactively (needed for loop mounts/KVM)
./scripts/_1.install_os.sh 24.04 --sudo-password YOUR_PASSWORD
```

**Headless autoinstall defaults**:
- Username: `ormastes`
- Password: `YOUR_PASSWORD` (sudo-enabled)
- Hostname: `gpu-direct-vm`
- Packages: `qemu-guest-agent` + OpenSSH Server
- Storage layout: automatic full-disk provisioning

**Interactive installation checklist** (only when a GUI is available):
- Select language and keyboard layout
- Configure network (use DHCP for simplicity)
- **Important**: Enable "Install OpenSSH server" for remote access
- Use entire disk for installation (virtio disk)
- Create user account (recommended: `ormastes` for consistency)
- Set password (consider matching the headless default for uniform workflows)

**Result**: Creates `data/ubuntu_server_<version>_nvme_qcow2`, stores `data/ubuntu-<version>-live-server-amd64.iso`, and caches unattended seed assets under `data/autoinstall/<version>/`.

### **52.3.3 Running VM with GPU Passthrough**

The `_2.run_qemu.sh` script manages VFIO binding and launches the VM with GPU and NVMe passthrough. This is the main entry point for starting your development VM.

**Purpose**: Run VM with GPU/NVMe passthrough using VFIO.

**Source**: `scripts/_2.run_qemu.sh`

**What it does**:
1. Stops existing QEMU instances to free resources
2. Kills processes using NVIDIA devices (`/dev/nvidia*`)
3. Removes NVIDIA kernel modules (`nvidia`, `nvidia_uvm`, etc.)
4. Sets up VFIO GPU passthrough by binding devices to `vfio-pci`
5. Launches QEMU VM with GPU attached
6. Auto-detects headless environments and adds `-nographic`

**Usage**:
```bash
# Run with GPU passthrough (auto-detects GPU PCI address)
./scripts/_2.run_qemu.sh

# Run with specific Ubuntu version
./scripts/_2.run_qemu.sh --guest-version 24.10

# Run without GPU passthrough
./scripts/_2.run_qemu.sh --no-gpu

# Custom memory and CPU allocation
./scripts/_2.run_qemu.sh --memory 64G --vcpu 16

# Headless automation (skip prompts entirely)
./scripts/_2.run_qemu.sh --guest-version 24.10 --memory 32G --vcpu 12 --auto-start

# Show full command and help
./scripts/_2.run_qemu.sh --help
```

**VM Configuration** (defaults):
- **Memory**: 16GB (configurable via `--memory`)
- **CPUs**: All available cores (uses `nproc`)
- **Disk**: Version-specific QCOW2 (e.g., `ubuntu_server_24.10_nvme_qemu.qcow2`)
- **SSH port**: 6665 (host) → 22 (guest)
- **Additional ports**: 9000-9010 forwarded for custom services
- **NVMe device**: OCSSD emulated drive (50GB raw image)
- **Display**: Auto-detects headless and uses `-nographic` appropriately
- **Acceleration fallback**: Automatically falls back to TCG software emulation when KVM access is unavailable

**Connecting to VM**:
```bash
# SSH into the VM
ssh ormastes@localhost -p 6665

# Inside VM, verify GPU passthrough
lspci | grep NVIDIA
nvidia-smi  # After installing NVIDIA drivers
```

**Note**: The script echoes the full QEMU command before execution for debugging.

### **52.3.4 Libvirt Integration for Production**

The `_3.setup_libvirt.sh` script imports your QEMU VM into libvirt for easier long-term management, including autostart and snapshot capabilities.

**Purpose**: Setup libvirt for persistent VM management.

**Source**: `scripts/_3.setup_libvirt.sh`

**What it does**:
1. Installs libvirt packages (daemon, clients, virt-viewer)
2. Adds current user to `libvirtd` group for permissions
3. Creates libvirt XML definition for the VM
4. Configures custom qemu-nvme binary path in XML
5. Sets up GPU passthrough in libvirt format
6. Imports VM into libvirt management system

**Usage**:
```bash
./scripts/_3.setup_libvirt.sh
```

**Benefits of libvirt**:
- Persistent VM configuration in XML format
- Easy start/stop with `virsh` commands
- Autostart capability on system boot
- Snapshot and backup management
- GUI management via `virt-manager`

**Common virsh commands**:
```bash
# Start VM
sudo virsh start qemu-nvme

# Start VM and open viewer
sudo virsh start qemu-nvme && sudo virt-viewer qemu-nvme

# Stop VM gracefully
sudo virsh shutdown qemu-nvme

# Force stop VM
sudo virsh destroy qemu-nvme

# Enable autostart on boot
sudo virsh autostart qemu-nvme

# Check VM status
sudo virsh list --all

# Create snapshot
sudo virsh snapshot-create-as qemu-nvme snap1 "Before kernel update"

# List and restore snapshots
sudo virsh snapshot-list qemu-nvme
sudo virsh snapshot-revert qemu-nvme snap1
```

**Source**: Full libvirt workflow described in `scripts/_3.setup_libvirt.sh`.

---

## **52.4 Developer Environment Scripts**

This section covers the scripts that set up comprehensive development toolchains inside the host or guest VM. These scripts install compilers, language runtimes, debugging tools, and optional NVIDIA/CUDA components.

### **52.4.1 Complete Development Environment Setup**

The `0.setup_dev_environment.sh` script installs a complete development environment suitable for CUDA development, kernel work, and general programming. This script can run on either the host or inside the guest VM.

**Purpose**: Setup comprehensive development environment on host or in VMs.

**Source**: `scripts/0.setup_dev_environment.sh`

**What it installs**:

#### Build Tools & Compilers
- **GCC toolchain**: gcc, g++, build-essential for C/C++ development
- **LLVM toolchain**: clang, llvm for alternative C/C++ compilation
- **Build systems**: cmake, ninja, make, ccache for faster builds
- **Build utilities**: autotools, pkg-config, libtool for library management

#### Programming Languages
- **Python 3**: pip, venv, poetry, black, flake8, pytest, jupyter, ipython
- **Node.js 20**: npm, yarn, pnpm, typescript, eslint, prettier
- **Rust**: Complete toolchain via rustup (cargo, rustc, rustfmt)
- **Go 1.21.5**: Full Go environment for system programming

#### Development Tools
- **Terminal**: tmux, screen for session management
- **Editors**: vim, neovim for in-terminal editing
- **Monitoring**: htop, btop, iotop, nethogs, sysstat for system monitoring
- **Search**: ripgrep, fd-find, bat, fzf for fast file/content search
- **Debugging**: gdb, valgrind, strace, ltrace, perf for debugging and profiling

#### NVIDIA & CUDA (Optional)
- **NVIDIA Drivers**: Latest from graphics-drivers PPA
- **CUDA 13.0**: Full toolkit and libraries including nvcc, cublas, cufft
- **cuDNN**: Deep learning primitives (optional)

#### Linux Kernel Development
- **KUNIT**: Kernel unit testing framework for in-kernel tests
- **Kernel headers**: `linux-headers-$(uname -r)` for building kernel modules
- **Development libs**: libelf-dev, dwarves, libssl-dev, libncurses-dev
- **Build tools**: bison, flex, bc, kmod, cpio for kernel compilation
- **Debugging tools**: linux-tools-common, linux-tools-generic, perf, BPF tools
- **Testing**: QEMU for kernel testing, python3-pytest for test automation

#### Container & Virtualization
- **Docker CE**: Latest Docker with user permissions (no sudo needed)
- **QEMU/KVM**: Full virtualization stack for nested VMs
- **Libvirt**: VM management tools (virsh, virt-viewer, virt-manager)

#### VS Code & Git
- **VS Code CLI**: Command-line tunnel server for remote development
- **Git**: With useful aliases (lg for log graph, st for status, co for checkout)

**Usage**:
```bash
# Full installation (includes NVIDIA + CUDA)
./scripts/0.setup_dev_environment.sh

# Skip NVIDIA drivers
./scripts/0.setup_dev_environment.sh --skip-nvidia

# Skip CUDA only (keep NVIDIA drivers)
./scripts/0.setup_dev_environment.sh --skip-cuda

# Automated installation for CI/CD
./scripts/0.setup_dev_environment.sh --sudo-password mypassword
```

**Post-installation verification**:
```bash
# Verify compilers
clang --version
gcc --version
nvcc --version    # If CUDA installed

# Verify languages
python3 --version
node --version
rustc --version
go version

# Verify tools
code --version
docker --version
nvidia-smi        # If NVIDIA installed

# Verify kernel tools
ls /usr/src | grep linux-headers
```

**Directory structure created**:
```
~/dev/
├── projects/   # Your development projects
├── tools/      # Development tools and utilities
├── repos/      # Git repositories
└── bin/        # Personal binaries
```

### **52.4.2 VS Code Tunnel Server**

The `1.run_code.sh` script starts a VS Code tunnel server for remote development through a web browser or VS Code client. This enables seamless remote development on the VM from any device.

**Purpose**: Start VS Code tunnel server for remote development.

**Source**: `scripts/1.run_code.sh`

**Features**:
- Automatically accepts server license terms
- Network connectivity checking (important for autostart)
- Process management (detects running tunnels to avoid duplicates)
- Logging with timestamps for troubleshooting
- Suitable for cron or systemd autostart

**Usage**:
```bash
# Start VS Code tunnel
./scripts/1.run_code.sh

# Specify custom log file
./scripts/1.run_code.sh --log-file ~/vscode.log

# Check if already running
pgrep -af "code tunnel"
```

**First-time setup**:
1. Run `./scripts/1.run_code.sh`
2. Visit the URL shown in output
3. Sign in with Microsoft/GitHub account
4. Connect your VS Code client (desktop or web)

**Autostart on boot (systemd)**:

Create `/etc/systemd/system/vscode-tunnel.service`:
```ini
[Unit]
Description=VS Code Tunnel Service
After=network-online.target
Wants=network-online.target

[Service]
Type=simple
User=ormastes
ExecStart=/path/to/scripts/1.run_code.sh
Restart=on-failure
RestartSec=10
StandardOutput=append:/tmp/vscode-tunnel.log
StandardError=append:/tmp/vscode-tunnel.log

[Install]
WantedBy=multi-user.target
```

Enable and start:
```bash
sudo systemctl daemon-reload
sudo systemctl enable vscode-tunnel
sudo systemctl start vscode-tunnel
sudo systemctl status vscode-tunnel
```

**View logs**:
```bash
# Live log
tail -f /tmp/vscode-tunnel.log

# Full log
cat /tmp/vscode-tunnel.log
```

### **52.4.3 Kernel Module Sudo Automation**

The `2.setup_kernel_module_sudo.sh` script creates sudoers entries for password-less kernel module operations, streamlining the load/unload cycle during kernel development.

**Purpose**: Configure password-less sudo for kernel module operations.

**Source**: `scripts/2.setup_kernel_module_sudo.sh`

**What it does**:
- Creates sudoers entries for `insmod`, `rmmod`, `modprobe`
- Allows password-less PCI device bind/unbind
- Supports per-module and per-directory configurations
- Validates sudoers syntax before applying

**Usage**:
```bash
# Setup for specific user and module directory
./scripts/2.setup_kernel_module_sudo.sh \
  --user ormastes \
  --ko-dir /path/to/kernel/modules

# Verify generated rules
sudo visudo -cf /etc/sudoers.d/*
```

**Generated permissions** (example):
- `sudo insmod *.ko` - Load kernel modules
- `sudo rmmod module_name` - Unload kernel modules
- `sudo tee /sys/bus/pci/drivers/*/bind` - Bind PCI devices
- `sudo tee /sys/bus/pci/drivers/*/unbind` - Unbind PCI devices

**Security note**: Only grant these permissions on development VMs, not production systems.

---

## **52.5 GPU Passthrough Setup**

This section details the GPU passthrough configuration process, including PCI device identification, IOMMU group verification, and VFIO binding procedures. GPU passthrough enables real GPUDirect testing inside the VM by providing direct hardware access to the GPU.

### **52.5.1 Identifying GPU PCI Address**

Before configuring GPU passthrough, you must identify your GPU's PCI address and IOMMU group. This information is critical for proper VFIO binding and ensures the GPU can be safely passed through to the VM.

**Identify GPU PCI address**:
```bash
lspci -nnk | grep NVIDIA
```

**Example output**:
```
09:00.0 VGA compatible controller [0300]: NVIDIA Corporation GA102GL [RTX A6000] [10de:2230] (rev a1)
09:00.1 Audio device [0403]: NVIDIA Corporation GA102 High Definition Audio Controller [10de:1aef] (rev a1)
```

Note the PCI address (e.g., `09:00.0` for VGA and `09:00.1` for audio) and device IDs (e.g., `10de:2230` and `10de:1aef`). Update `GPU_PCI_ADDR` in `_2.run_qemu.sh` if your GPU is at a different address than the default.

### **52.5.2 Checking IOMMU Groups**

IOMMU groups determine which devices can be passed through together. Your GPU should ideally be in its own IOMMU group for clean passthrough without affecting other system devices.

**Create and run IOMMU group checker**:
```bash
#!/bin/bash
# iommu.sh - Check IOMMU groups
for d in /sys/kernel/iommu_groups/*/devices/*; do
  n=${d#*/iommu_groups/*}; n=${n%%/*}
  printf 'IOMMU Group %s ' "$n"
  lspci -nns "${d##*/}"
done
```

**Run the script**:
```bash
chmod +x iommu.sh
./iommu.sh | grep NVIDIA
```

**Expected output** (GPU in isolated group):
```
IOMMU Group 15 09:00.0 VGA compatible controller [0300]: NVIDIA Corporation GA102GL [RTX A6000] [10de:2230] (rev a1)
IOMMU Group 15 09:00.1 Audio device [0403]: NVIDIA Corporation GA102 High Definition Audio Controller [10de:1aef] (rev a1)
```

If your GPU shares an IOMMU group with other critical devices, you may need ACS override patches or a different hardware configuration.

### **52.5.3 VFIO Driver Binding**

The `_2.run_qemu.sh` script automatically handles VFIO binding, but understanding the process helps with troubleshooting. Manual binding is rarely needed but useful when debugging passthrough issues.

**How `_2.run_qemu.sh` performs GPU passthrough**:

1. **Stop conflicting processes**: Kills any processes using `/dev/nvidia*` devices
2. **Remove NVIDIA modules**: Unloads `nvidia`, `nvidia_uvm`, `nvidia_modeset`, `nvidia_drm` kernel modules
3. **Load VFIO**: Loads `vfio-pci` kernel module for device passthrough
4. **Unbind GPU**: Unbinds GPU from current driver (if any)
5. **Bind to VFIO**: Binds GPU to `vfio-pci` driver for passthrough
6. **Launch QEMU**: Starts VM with GPU attached via `-device vfio-pci,host=09:00.0`

**Manual VFIO binding** (for troubleshooting):
```bash
# Load VFIO modules
sudo modprobe vfio-pci

# Unbind from current driver
echo "0000:09:00.0" | sudo tee /sys/bus/pci/devices/0000:09:00.0/driver/unbind

# Bind to vfio-pci
echo "10de 2230" | sudo tee /sys/bus/pci/drivers/vfio-pci/new_id

# Verify binding
lspci -nnk -s 09:00.0
# Should show "Kernel driver in use: vfio-pci"
```

### **52.5.4 Optional: Permanent VFIO Binding**

For permanent GPU passthrough setup (dedicated passthrough GPU that won't be used by host), blacklist NVIDIA drivers on the host and configure VFIO to claim the GPU at boot.

**Create VFIO configuration**:
```bash
sudo nano /etc/modprobe.d/vfio.conf
```

**Add** (replace with your device IDs):
```
blacklist nouveau
blacklist nvidia
blacklist nvidia_drm
blacklist nvidia_modeset
blacklist nvidia_uvm
options vfio-pci ids=10de:2230,10de:1aef
```

**Update initramfs and reboot**:
```bash
sudo update-initramfs -u
sudo reboot
```

**Verify drivers are not loaded**:
```bash
lspci -nnk | grep -A 3 NVIDIA
# Should NOT show "Kernel driver in use: nvidia"
# Should show "Kernel driver in use: vfio-pci"
```

**Note**: Only use permanent binding if you have a dedicated passthrough GPU. For shared GPUs, let `_2.run_qemu.sh` handle dynamic binding.

---

## **52.6 VM Configuration and Disk Formats**

This section explains the VM configuration options and the two disk formats used: QCOW2 for the OS disk and raw IMG for NVMe emulation. Understanding these formats helps optimize storage usage and performance.

### **52.6.1 Default VM Configuration**

The VM scripts use these default settings, which can be customized via command-line arguments:

**VM Settings**:
- **OS**: Ubuntu 24.10 Server (default, supports 24.04 LTS, 24.10, 25.04, 25.10)
- **Username**: `ormastes` (configured during installation)
- **Password**: Set during VM installation (choose a secure password)
- **SSH Port**: 6665 (host) → 22 (guest)
- **Memory**: 16GB (configurable via `--memory`)
- **CPUs**: All host CPU cores (uses `nproc`)
- **Disk**: 128GB QCOW2 (expandable)
- **NVMe**: 50GB raw image (OCSSD format)

**Port Forwarding**:
- **SSH**: 6665 → 22 (primary access)
- **Custom**: 9000-9010 → 9000-9010 (for development servers)

### **52.6.2 OVMF (UEFI Firmware)**

The VM uses OVMF (Open Virtual Machine Firmware) for modern UEFI boot instead of legacy BIOS. OVMF provides better hardware compatibility and supports modern features like Secure Boot and GPT partitions.

**What is OVMF?**
- Part of TianoCore EDK II project
- Provides UEFI firmware for QEMU/KVM VMs
- Enables modern boot features (Secure Boot, GPT partitions, etc.)
- Better hardware compatibility than legacy BIOS

**Detection & Usage**:
- Scripts **automatically detect** OVMF installation
- Falls back to **legacy BIOS** if OVMF not found
- VM configuration shows which firmware is being used

**Benefits of UEFI (OVMF)**:
- ✅ Modern boot standard
- ✅ Better hardware initialization
- ✅ Secure Boot support (if needed)
- ✅ GPT partition support (>2TB disks)
- ✅ Network boot (PXE)

### **52.6.3 QCOW2 Format (OS Disk)**

The main VM operating system disk uses **QCOW2** (QEMU Copy-On-Write version 2) format for space efficiency and snapshot support.

**Purpose**: Main VM operating system disk

**Characteristics**:
- **Dynamic allocation** - Only uses actual disk space for written data (128GB image might use only 10GB)
- **Snapshots support** - Save VM state and revert later for safe experimentation
- **Compression & encryption** - Built-in features for space savings
- **Easy backup** - Simple to clone and backup VMs
- **Slightly slower** - Small performance overhead (~5-10%) due to metadata

**Why used for OS disk**:
- Space efficiency (OS uses only what it needs)
- Snapshot capability before major system changes
- Easy VM cloning and backup

**Common commands**:
```bash
# Create qcow2 disk
qemu-img create -f qcow2 ubuntu_server_nvme_qemu.qcow2 128G

# Check disk info
qemu-img info ubuntu_server_nvme_qemu.qcow2

# Create snapshot
qemu-img snapshot -c before_update ubuntu_server_nvme_qemu.qcow2

# Restore snapshot
qemu-img snapshot -a before_update ubuntu_server_nvme_qemu.qcow2

# Resize disk
qemu-img resize ubuntu_server_nvme_qemu.qcow2 +128G
```

### **52.6.4 Raw IMG Format (NVMe Playground)**

The NVMe device uses **raw IMG** format for maximum I/O performance and hardware simulation accuracy.

**Purpose**: NVMe device for storage experiments and playground

**Characteristics**:
- **Pre-allocated** - Uses full 50GB immediately
- **No overhead** - Maximum I/O performance
- **Raw block device** - Direct hardware simulation
- **No special features** - Just raw data blocks
- **Universal compatibility** - Works with standard tools

**Why used for NVMe**:
- OpenChannelSSD requires raw block device access
- Maximum performance for storage research
- Simulates real NVMe hardware behavior
- Used as playground for NVMe command testing

**Common commands**:
```bash
# Create raw OCSSD disk (for NVMe playground)
qemu-img create -f ocssd -o num_grp=2,num_pu=4,num_chk=60 nvme_playground_disk.img 50G

# Create standard raw disk
qemu-img create -f raw nvme_playground_disk.img 50G

# Check disk usage
ls -lh nvme_playground_disk.img
du -h nvme_playground_disk.img
```

### **52.6.5 Disk Format Comparison**

| Feature | QCOW2 (OS Disk) | Raw IMG (NVMe Playground) |
|---------|-----------------|---------------------------|
| **File size** | Grows dynamically | Fixed 50GB from start |
| **Performance** | Good (~5-10% overhead) | Maximum (no overhead) |
| **Snapshots** | ✅ Yes | ❌ No |
| **Compression** | ✅ Yes | ❌ No |
| **Use case** | System disk, development | NVMe experiments, storage research |
| **Space efficiency** | High (sparse file) | Low (pre-allocated) |
| **Purpose** | Boot and run Ubuntu | NVMe command playground |

---

## **52.7 Troubleshooting**

This section covers common issues and their solutions when working with the VM environment. These solutions have been tested with the `llm_storage` setup.

### **52.7.1 KVM Not Available (Slow Performance)**

If you see "WARNING: KVM not available. Using software emulation", the VM will run 10-50x slower than with KVM acceleration.

**Diagnosis**:
```bash
# Check if KVM device exists
ls -l /dev/kvm
# Should show: crw-rw---- 1 root kvm

# Check if CPU supports virtualization
egrep -c '(vmx|svm)' /proc/cpuinfo
# Should return > 0

# Check if KVM modules are loaded
lsmod | grep kvm
# Should show: kvm_intel or kvm_amd
```

**Solution**:
```bash
# Load KVM modules
sudo modprobe kvm kvm_intel  # Intel CPUs
sudo modprobe kvm kvm_amd    # AMD CPUs

# Add user to kvm group
sudo usermod -aG kvm $USER
# Log out and log back in

# Check permissions
sudo chmod 666 /dev/kvm  # Temporary fix
```

**Enable in BIOS**:
- Intel: Enable "Intel VT-x" or "Virtualization Technology"
- AMD: Enable "AMD-V" or "SVM Mode"

### **52.7.2 GPU Passthrough Not Working**

**Diagnosis**:
```bash
# Check IOMMU is enabled
dmesg | grep -i iommu

# Check VFIO module is loaded
lsmod | grep vfio

# Check GPU binding
lspci -nnk -s 09:00.0  # Replace with your GPU address

# Check for processes holding NVIDIA devices
sudo lsof | grep nvidia
```

**Solution**:
- Verify IOMMU is enabled in kernel (`intel_iommu=on` or `amd_iommu=on`)
- Check GPU is in its own IOMMU group
- Ensure no processes are using the GPU before passthrough
- Review `_2.run_qemu.sh` for automatic VFIO binding

### **52.7.3 VM Won't Start**

**Diagnosis**:
```bash
# Check disk images exist
ls -lh data/ubuntu_server_24.10_nvme_qemu.qcow2
ls -lh data/nvme_playground_disk.img

# Check QEMU binary exists
${HOME}/qemu-nvme/bin/qemu-system-x86_64 --version

# Check for port conflicts
sudo netstat -tlnp | grep 6665
```

**Solution**:
- Ensure disk images were created by `_1.install_os.sh`
- Verify QEMU was built successfully by `_0.setup_qemu.sh`
- Kill processes using port 6665 if needed
- Check OVMF firmware is installed: `ls /usr/share/ovmf/`

### **52.7.4 SSH Connection Refused**

**Diagnosis**:
```bash
# Check if VM is running
ps aux | grep qemu

# Check if SSH port is listening
sudo netstat -tlnp | grep 6665
```

**Solution inside VM**:
```bash
# Ensure SSH is running
sudo systemctl status ssh
sudo systemctl enable ssh
sudo systemctl start ssh
```

### **52.7.5 Resize VM Disk**

**Expand QCOW2 disk**:
```bash
# On host: resize disk image
${HOME}/qemu-nvme/bin/qemu-img resize ubuntu_server_nvme_qemu.qcow2 +128G

# Inside VM: resize partition
sudo growpart /dev/vda 1
sudo resize2fs /dev/vda1
```

---

## **52.8 Module 53: NVMe VFIO Test Scripts**

This section describes the VFIO test environment setup scripts located in Module 53. These scripts automate NVMe device binding for VFIO integration tests and work seamlessly with the VM environment established in this module.

### **52.8.1 Setup VFIO Test Environment**

The `setup_vfio_test_env.sh` script (located in `53.NVMe_VFIO_Host_Layer/scripts/`) automates the complete setup of VFIO environment for NVMe integration tests. This script is designed to work inside the guest VM created by Module 52 scripts.

**Purpose**: Automate VFIO binding and environment configuration for Module 53 integration tests.

**Key Features:**
- Automatically detects and lists NVMe devices
- **Excludes boot/root devices** for safety
- Auto-selects first non-boot NVMe device
- Detects namespace information (NSID, LBA size, capacity) using `nvme-cli`
- Binds selected device to vfio-pci driver
- Exports test environment variables to `nvme_test_env.sh`
- Optionally builds and runs integration tests

**Usage inside VM:**
```bash
# Interactive mode (prompts for device selection)
cd 53.NVMe_VFIO_Host_Layer/scripts
sudo ./setup_vfio_test_env.sh

# Auto-select first available non-boot device
sudo ./setup_vfio_test_env.sh --auto

# Auto-select and run tests immediately
sudo ./setup_vfio_test_env.sh --auto --test
```

**Prerequisites:**
- IOMMU enabled (configured in Module 52 host setup)
- At least one non-boot NVMe device (provided by QEMU OCSSD emulation)
- `nvme-cli` package (auto-installed by script)

**Environment Variables Generated:**

The script creates `nvme_test_env.sh` containing:

```bash
export NVME_BDF="0000:08:00.0"  # PCI address
export NVME_NSID=1               # Namespace ID
export NVME_LBA_SIZE=512         # LBA size in bytes
export NVME_SLBA=1000000         # Safe test start LBA
export NVME_LBAS=8               # Number of LBAs for test
```

### **52.8.2 Running Integration Tests**

The `run_integration_test.sh` script provides a convenience wrapper for running Module 53 integration tests with pre-configured VFIO environment.

**Purpose**: Run integration tests with automatic environment loading and build management.

**Features:**
- Loads environment from `nvme_test_env.sh`
- Verifies VFIO device accessibility
- Builds project if needed (cmake + ninja)
- Runs all tests or specific test executable
- Provides detailed test summary with pass/fail tracking

**Usage:**
```bash
# Run all integration tests
sudo ./run_integration_test.sh

# Run specific test
sudo ./run_integration_test.sh test_integration

# Non-interactive mode (for CI automation)
sudo ./run_integration_test.sh < /dev/null
```

### **52.8.3 Typical Workflow (VM + VFIO Testing)**

Complete workflow combining Module 52 VM and Module 53 VFIO tests:

**On Host (Module 52):**
```bash
# 1. Build QEMU with NVMe support
cd 52.VM_Development_Environment/scripts
./_0.setup_qemu.sh --non-interactive

# 2. Install Ubuntu Server in VM
./_1.install_os.sh 24.10

# 3. Launch VM with NVMe passthrough/emulation
./_2.run_qemu.sh --guest-version 24.10
```

**Inside VM (Module 53):**
```bash
# 1. Setup development environment (includes nvme-cli)
cd /mnt/cuda_exercise
./52.VM_Development_Environment/scripts/0.setup_dev_environment.sh

# 2. Build Module 53
cd 53.NVMe_VFIO_Host_Layer
mkdir build && cd build
cmake .. -DBUILD_TESTING=ON -GNinja
ninja

# 3. Setup VFIO environment and run tests
cd ../scripts
sudo ./setup_vfio_test_env.sh --auto --test
```

**Subsequent Test Runs:**
```bash
# After initial setup, simply run:
cd 53.NVMe_VFIO_Host_Layer/scripts
sudo ./run_integration_test.sh
```

### **52.8.4 Safety Features**

The Module 53 scripts include multiple safety mechanisms:

1. **Boot Device Protection**: Automatically excludes any NVMe device used for boot/root filesystem
2. **Safe LBA Range**: Tests use last 1% of drive (minimum 1MB) to avoid data corruption
3. **IOMMU Verification**: Checks IOMMU is enabled before attempting VFIO binding
4. **Device Validation**: Verifies namespace info and capacity before testing
5. **Confirmation Prompts**: Interactive mode requires user confirmation before binding

### **52.8.5 Troubleshooting VFIO Tests**

**IOMMU Not Enabled:**
Already configured in Module 52 host setup. Verify with:
```bash
dmesg | grep -i iommu
```

**No Non-Boot Devices Available:**
If running on bare metal with single NVMe, use Module 52 VM environment which provides OCSSD-emulated NVMe device for safe testing.

**Permission Denied on /dev/vfio/vfio:**
```bash
# Run with sudo
sudo ./run_integration_test.sh

# Or add user to vfio group
sudo usermod -a -G vfio $USER
# Logout and login for group changes
```

**Tests Fail with "No such device":**
```bash
# Verify device binding
lspci -nnk | grep -A 3 NVMe

# Re-run setup if needed
sudo ./setup_vfio_test_env.sh --auto
```

### **52.8.6 Integration with Module 52**

These Module 53 scripts are designed to work seamlessly inside the Module 52 VM:

1. **VM provides safe NVMe device**: QEMU OCSSD emulation creates dedicated NVMe device for testing
2. **Shared repository**: Virtio-FS mounts host repository at `/mnt/cuda_exercise`
3. **Consistent environment**: Dev environment script installs all dependencies including nvme-cli
4. **Snapshot capability**: QCOW2 VM disk allows reverting after testing

**See Also:**
- [Module 53 README](../53.NVMe_VFIO_Host_Layer/README.md) - Full Module 53 documentation
- [Module 53 Integration Tests](../53.NVMe_VFIO_Host_Layer/test/unit/) - Test source code
- [Module 51 VFIO Setup](../51.Knowledge_and_VFIO_Setup/scripts/) - Original VFIO binding scripts

---

## **Build & Run**

Follow this command sequence to provision the virtualization stack, launch the GPU-passthrough guest, and prepare it for kernel development.

```bash
# Ensure the shared data/ directory exists
cmake --build . --target vm_env_prepare

# Build QEMU NVMe-capable binaries
cd data
../50.GPU-NVMe_Interaction/52.VM_Development_Environment/scripts/_0.setup_qemu.sh --non-interactive

# Install Ubuntu Server guest (choose version)
../50.GPU-NVMe_Interaction/52.VM_Development_Environment/scripts/_1.install_os.sh 24.10 --disk-size 256G

# Launch VM with GPU/NVMe passthrough
../50.GPU-NVMe_Interaction/52.VM_Development_Environment/scripts/_2.run_qemu.sh \
  --guest-version 24.10 \
  --gpu 0000:01:00.0 \
  --nvme 0000:02:00.0

# Inside guest: install toolchain and NVIDIA driver
sudo ./scripts/0.setup_dev_environment.sh

# Optional: configure password-less kernel module operations
cd /mnt/cuda_exercise/build
../50.GPU-NVMe_Interaction/52.VM_Development_Environment/scripts/2.setup_kernel_module_sudo.sh --user ormastes
```

---

## **Summary**

### **Key Takeaways**

Review the highlights below to ensure you captured the rationale and workflow dependencies before moving forward.

1. Virtualizing the GPUDirect lab reproduces the proven `llm_storage` workflow with identical scripts, paths, and tooling.
2. Automated scripts manage VFIO binding, QEMU builds, guest installation, and VS Code tunnels without manual path edits.
3. Installing the developer environment inside the guest yields a full CUDA + kernel toolchain backed by DKMS headers for driver work.
4. Virtio-FS sharing and sudo automation bridge VM-built `.ko` artifacts back to host tests in Part 55.

### **Performance Metrics**

These reference numbers provide a baseline for spotting regressions in future iterations of the virtualization lab.

- VM boot time with hugepages and GPU passthrough: ~12 s on a 24-core Threadripper (from `llm_storage` measurements)
- NVMe passthrough bandwidth (`fio --randread --bs=4k`): ~3.1 GB/s inside guest
- GPU passthrough latency (`cudaMemcpy` H2D 4 MB): ~13 µs, matching bare metal

### **Common Errors & Solutions**

Keep this quick lookup table handy when the automation fails so troubleshooting remains fast and repeatable.

| Error | Cause | Solution |
|-------|-------|----------|
| `vfio-pci: bind failed` | Device still attached to host driver | Stop the VM launcher, unbind the GPU from host drivers per [52.5 GPU Passthrough Setup](#525-gpu-passthrough-setup), then rerun `_2.run_qemu.sh --gpu`. |
| `OVMF not found` | Firmware package missing | Install `ovmf` or rerun `_0.setup_qemu.sh` with sudo password. |
| ISO checksum mismatch | Incomplete download | Re-run `_1.install_os.sh` to retry the download with validation. |
| Guest lacks CUDA headers | Driver installed without DKMS | Re-run `0.setup_dev_environment.sh` or install `nvidia-dkms` packages. |

### **Next Steps**

Move through the follow-up items in order to build on the environment you just provisioned.

- 📚 Continue to [Part 53: NVMe VFIO Host Layer](../53.NVMe_VFIO_Host_Layer/README.md) to build user-space queues against the passthrough NVMe.
- 🔧 Capture VM-based traces to validate PRP construction before implementing kernel IOCTLs in Part 55.
- 📊 Benchmark different NVIDIA driver versions by snapshotting QCOW2 images and re-running the provisioning scripts.

### **References**

Consult these sources for deeper dives into virtualization, VFIO, and GPUDirect documentation referenced throughout this module.

- [OpenChannelSSD QEMU-NVMe](https://github.com/OpenChannelSSD/qemu-nvme)
- [QEMU PCI Passthrough Documentation](https://wiki.qemu.org/Documentation/Devices/PCI-Passthrough)
- [NVIDIA GPUDirect RDMA Guide](https://docs.nvidia.com/cuda/gpudirect-rdma/)
- [Kernel VFIO Documentation](https://www.kernel.org/doc/html/latest/driver-api/vfio.html)
