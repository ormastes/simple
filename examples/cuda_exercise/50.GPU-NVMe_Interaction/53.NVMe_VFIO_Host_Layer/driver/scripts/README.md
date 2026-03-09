# Module 53 Scripts

## Overview

Module 53 provides three types of setup scripts:

1. **[Run Without Sudo](#run-tests-without-sudo-recommended)** ✅ - VFIO group access (no sudo needed!)
2. **[Passwordless Sudo](#passwordless-sudo-setup)** - Alternative: sudo without password prompts
3. **[P2P DMA Setup](#gpu-nvme-p2p-setup)** - GPU-NVMe peer-to-peer configuration

---

## Run Tests Without Sudo (Recommended)

Module 53 tests require access to VFIO devices. You can grant access via group membership instead of sudo:

### Quick Setup

```bash
# Step 1: Create vfio group and add user
sudo groupadd -f vfio
sudo usermod -a -G vfio $USER

# Step 2: Create udev rule for VFIO device permissions
echo 'SUBSYSTEM=="vfio", OWNER="root", GROUP="vfio", MODE="0660"' | \
  sudo tee /etc/udev/rules.d/99-vfio.rules

# Step 3: Reload udev rules
sudo udevadm control --reload-rules
sudo udevadm trigger --subsystem-match=vfio

# Step 4: Verify setup
groups | grep vfio          # Should show "vfio"
ls -la /dev/vfio/           # Group should be "vfio" with mode "crw-rw----"

# Step 5: Run tests WITHOUT sudo using sg command
sg vfio -c "./build/.../test_host_io_system"

# Or for multiple commands in the vfio group context:
sg vfio
./build/.../test_host_io_system  # Now running with vfio group
```

### What This Does

1. Creates `vfio` group if it doesn't exist
2. Adds your user to the `vfio` group
3. Creates udev rule: `/etc/udev/rules.d/99-vfio.rules`
4. Sets VFIO device permissions: `root:vfio` with mode `0660`

### Benefits

- ✅ **No sudo needed** for running tests
- ✅ **More secure** than full sudo or passwordless sudo
- ✅ **Standard Linux approach** for device access
- ✅ **Works with CTest** and automated testing

### Usage Examples

**Run single test:**
```bash
export NVME_BDF="0000:41:00.0"
sg vfio -c "./build/.../test_host_io_system --gtest_filter='*DeviceInitialization'"
```

**Run all tests:**
```bash
export NVME_BDF="0000:41:00.0" NVME_NSID="1" NVME_LBA_SIZE="512" NVME_SLBA="2000000"
sg vfio -c "./build/.../test_host_io_system"
```

**Interactive session (for running multiple commands):**
```bash
sg vfio                    # Start new shell with vfio group
export NVME_BDF="0000:41:00.0"
./build/.../test_host_io_system
./build/.../test_another
exit                       # Exit vfio group shell
```

### Troubleshooting

If tests still fail with "Permission denied":

```bash
# Check group membership (requires logout/login to take effect)
groups | grep vfio

# Check VFIO device permissions
ls -la /dev/vfio/

# Force trigger udev rules
sudo udevadm control --reload-rules
sudo udevadm trigger --subsystem-match=vfio
```

---

## Passwordless Sudo Setup

Alternative to vfio group: Configure sudo to not prompt for password.

Module 53 tests require root privileges for VFIO operations. To run tests with sudo but without password prompts:

### Quick Setup (Automated)

```bash
# From repository root
./50.GPU-NVMe_Interaction/53.NVMe_VFIO_Host_Layer/scripts/sudo_setup/setup_sudo_nopasswd.sh

# Or specify custom build directory
./50.GPU-NVMe_Interaction/53.NVMe_VFIO_Host_Layer/scripts/sudo_setup/setup_sudo_nopasswd.sh /path/to/build
```

### Manual Setup

```bash
./50.GPU-NVMe_Interaction/53.NVMe_VFIO_Host_Layer/scripts/sudo_setup/setup_sudo_nopasswd.sh

# Or specify custom build directory
./50.GPU-NVMe_Interaction/53.NVMe_VFIO_Host_Layer/scripts/sudo_setup/setup_sudo_nopasswd.sh /path/to/build
```

## What Gets Configured

The setup scripts create:

1. **VFIO Helper Scripts** (`/usr/local/sbin/`)
   - `vfio-bind.sh` - Bind NVMe device to vfio-pci
   - `vfio-unbind.sh` - Restore NVMe device to nvme driver

2. **Sudoers Configuration** (`/etc/sudoers.d/99-nopasswd-vfio-$USER`)
   - Passwordless sudo for VFIO helper scripts
   - Passwordless sudo for kernel module operations
   - Passwordless sudo for Module 53 test executables

## Usage Examples

### Bind/Unbind NVMe Device

```bash
# Find your NVMe device
lspci -nn | grep -i nvme
# Example output: 41:00.0 Non-Volatile memory controller [0108]: ...

# Bind to vfio-pci (for VFIO tests)
sudo /usr/local/sbin/vfio-bind.sh 0000:41:00.0

# Run your tests...
sudo -E ./build/50.GPU-NVMe_Interaction/53.NVMe_VFIO_Host_Layer/test/system_test/test_host_io_system

# Restore to nvme driver (for normal use)
sudo /usr/local/sbin/vfio-unbind.sh 0000:41:00.0
```

### Run Tests

```bash
# System tests
sudo -E ./build/50.GPU-NVMe_Interaction/53.NVMe_VFIO_Host_Layer/test/system_test/test_host_io_system

# Helper tests
sudo -E ./build/50.GPU-NVMe_Interaction/53.NVMe_VFIO_Host_Layer/test/helper/test_setup_tasks

# Note: -E preserves environment variables (NVME_BDF, NVME_NSID, etc.)
```

### Using CTest

```bash
# Set environment variables
export NVME_BDF="0000:41:00.0"
export NVME_NSID="1"
export NVME_LBA_SIZE="512"
export NVME_SLBA="2000000"

# Bind device first
sudo /usr/local/sbin/vfio-bind.sh "$NVME_BDF"

# Run tests with CTest
cd build
sudo -E ctest -R "HostIoHelperSystemTest" --verbose

# Or run all Module 53 system tests
sudo -E ctest -L "system.*53" --verbose

# Unbind when done
sudo /usr/local/sbin/vfio-unbind.sh "$NVME_BDF"
```

## Sudo-Required Setup Tasks

`run_system_test.sh` intentionally refuses to run unless invoked with `sudo -E` so the admin-only `SetupHelper` tasks (binding devices, launching daemons, programming IOMMUs) can complete without mid-test prompts. After you run `sudo_setup/setup_sudo_nopasswd.sh` once, the helper scripts it installs under `/usr/local/sbin/` (`vfio-bind.sh`, `vfio-unbind.sh`) execute with passwordless sudo, so every admin task listed below just works when the tests call into `SetupHelper`. You can still bypass sudo entirely by following the vfio group instructions above—`ensure_vfio_binding()` simply detects that `/dev/vfio/*` is already accessible and skips the helper scripts.

| SetupHelper task (class) | Why it needs sudo / what it touches | System tests that trigger it | Helper script / automation |
| --- | --- | --- | --- |
| `VfioBindingTask` and `NvmeSetupTask` | Binds the NVMe BDF to `vfio-pci`, opens `/dev/vfio/<group>`, and maps the doorbell BARs for MMIO access. Uses `/usr/local/sbin/vfio-bind.sh` and `vfio-unbind.sh`, which require sudo unless the vfio group already owns the device node. | All Module 53/54/55 host system tests (`test_host_io_system`, `test_cuda_host_io_system`, 55.x suites) | Installed by `sudo_setup/setup_sudo_nopasswd.sh`, invoked automatically by `SetupHelper` or manually via `run_system_test.sh` (run with `sudo -E`). |
| `GpuP2PSetupTask` | Loads VFIO + NVIDIA peer-memory modules, configures `/dev/gpu_p2p_nvme`, and pins BAR mappings for GPU-initiated queues. Needs CAP_SYS_MODULE and CAP_SYS_ADMIN. | Module 56 GPU queue/buffer tests (`56_test_gpu_queue_gpu_buffer`) | Use `scripts/sudo_setup/gpu_p2p_setup_task.sh` to pre-configure the machine; `GpuP2PSetupTask` assumes the script has been run and will fail fast with guidance if not. |
| `DbcShadowBufferTask` | Allocates pinned host memory for NVMe Doorbell Buffer Config (“shadow doorbells”) and maps it into IOVA space via VFIO. Requires CAP_SYS_ADMIN to call `host_map_iova()`. | Module 55.2 shadow doorbell tests, Module 55.3 host DBC daemon tests, and the 55.4 mode harness when selecting shadow/DBC modes. | Runs inside the system tests; no standalone script, but it relies on the VFIO helper scripts noted above to ensure the device is already bound. |
| `HostDoorbellDaemonTask` | Launches the Module 55.1 doorbell daemon that polls SQ tails and rings MMIO doorbells on behalf of test queues. Needs sudo to mmap doorbells and raise thread priority. | Module 55.1 host-daemon tests and the host-daemon branch of the 55.4 harness. | Compiled into the test binary; invoked via `SetupHelper` once VFIO binding succeeds. |
| `HostDbcDaemonTask` | Spawns the Module 55.3 daemon that mirrors updates from the shadow doorbell buffer into MMIO doorbells (Doorbell Buffer Config “host + daemon” mode). Needs sudo because it opens `/dev/nvme*`, `/dev/vfio/*`, and configures shared memory. | Module 55.3 Host DBC daemon tests and the host_dbc mode in 55.4. | Also bundled with the test binary; assumes `setup_sudo_nopasswd.sh` installed the VFIO helpers so binding already succeeded. |

When you run `sudo -E ./scripts/run_system_test.sh` (or invoke the gtest binaries the same way), the script preserves `NVME_*` environment variables and executes the binary as root so each admin task above can call the helper scripts without additional prompts. After the helpers are installed you can run the same binaries without `sudo` by entering the `vfio` group shell (`sg vfio`) so `/dev/vfio/*` is writable—the tasks see that no binding is needed and stay in user mode.

## Security Notes

- Scripts only grant NOPASSWD for specific commands (not full sudo)
- Test executables must be in the configured build directory
- Helper scripts validate input and use full paths
- Sudoers file is owned by root:root with mode 0440

## Removal

To remove the sudo configuration:

```bash
sudo rm /etc/sudoers.d/99-nopasswd-vfio-$USER
sudo rm /usr/local/sbin/vfio-bind.sh
sudo rm /usr/local/sbin/vfio-unbind.sh
```

## Troubleshooting

### Still Prompts for Password

Check sudoers syntax:
```bash
sudo visudo -c -f /etc/sudoers.d/99-nopasswd-vfio-$USER
```

Verify your username matches:
```bash
grep "$USER" /etc/sudoers.d/99-nopasswd-vfio-$USER
```

### Device Binding Fails

Check IOMMU is enabled:
```bash
dmesg | grep -i iommu
```

Check device exists:
```bash
ls -la /sys/bus/pci/devices/0000:41:00.0
```

Check vfio-pci module loaded:
```bash
lsmod | grep vfio
```

### Tests Can't Access Device

Check VFIO group permissions:
```bash
# Find IOMMU group
readlink /sys/bus/pci/devices/0000:41:00.0/iommu_group

# Check device node permissions
ls -la /dev/vfio/  # Group should be accessible
```

You may need to add your user to the vfio group:
```bash
sudo usermod -a -G vfio $USER
# Log out and back in for group changes to take effect
```

---

## GPU-NVMe P2P Setup

For GPU-initiated NVMe operations (Modules 55+), you need to configure P2P (Peer-to-Peer) DMA between GPU and NVMe devices.

**See [README_P2P.md](README_P2P.md) for complete guide.**

### Quick P2P Check

```bash
cd /home/ormastes/dev/pub/cuda_exercise/50.GPU-NVMe_Interaction/53.NVMe_VFIO_Host_Layer/scripts
sudo ./check_p2p_capability.sh
```

This checks:
- IOMMU enabled
- NVIDIA GPU and driver
- nvidia-peermem module (required for P2P)
- NVMe devices
- PCIe topology (GPU-NVMe proximity)
- Resizable BAR status

### Quick P2P Setup

```bash
sudo ./sudo_setup/gpu_p2p_setup_task.sh
```

This configures:
- ✅ Kernel parameters (`intel_iommu=on iommu=pt`)
- ✅ VFIO module auto-loading
- ⚠️ Provides guidance for BIOS settings
- ⚠️ Provides guidance for nvidia-peermem installation

**Note**: Some steps require manual BIOS configuration:
- Enable VT-d/AMD-Vi (IOMMU)
- Enable Above 4G Decoding
- Enable Resizable BAR (recommended)
- UEFI Boot mode (for Resizable BAR)

### Verify CUDA P2P Tokens (Required for Modes 5 & 6)

Even if `/dev/gpu_p2p_nvme` exists, CUDA must expose non-zero P2P tokens or GPU buffers cannot be mapped.

```bash
cd /home/ormastes/dev/pub/cuda_exercise/50.GPU-NVMe_Interaction/53.NVMe_VFIO_Host_Layer/driver/scripts
sudo ./check_p2p_token.sh
```

If the probe reports `p2p_token=0`:
- Rebuild/reload the dual P2P modules against the running NVIDIA driver (`sudo make -f Makefile.dual load`)
- Ensure MIG/vGPU is disabled (tokens are hidden when the GPU is partitioned)
- Confirm `nvidia-peermem`/`nvidia_p2p` symbols are present (`dmesg | grep nvidia_p2p`)
- Modes 5/6 will refuse to run without a valid token because true GPU P2P mapping is unavailable

### What P2P Enables

P2P DMA allows:
- **Direct GPU-to-NVMe transfers** without CPU involvement
- **Lower latency** - No system RAM copies
- **Higher bandwidth** - Direct PCIe transfers
- **Lower CPU usage** - CPU free for other work

Required for:
- Module 55: GPU-Initiated NVMe operations
- Module 56: GPU queue management
- Module 57: Performance benchmarks comparing host vs GPU paths

### Full Documentation

See [README_P2P.md](README_P2P.md) for:
- Detailed P2P requirements
- Step-by-step setup process
- Hardware vs software configuration
- Troubleshooting guide
- Performance optimization tips
