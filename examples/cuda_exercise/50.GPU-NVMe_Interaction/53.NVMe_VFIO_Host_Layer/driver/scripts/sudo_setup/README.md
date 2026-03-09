# Sudo Setup Scripts

Administrative setup scripts for privileged operations. Scripts are categorized by when they need to be run.

---

## ONE-TIME SETUP (Run once per boot/system)

These configure system-level resources that persist until reboot or manual teardown.

### `vfio_binding_task.sh`
**Purpose**: Bind NVMe device to VFIO driver for userspace access

**When to run**: Once after boot, or when NVMe device changes
```bash
sudo ./vfio_binding_task.sh
```

**What it does**:
- Unbinds NVMe from kernel driver (nvme)
- Binds to vfio-pci driver
- Sets up /dev/vfio/* device nodes

**Persists until**: Device unbind or system reboot

---

### `gpu_p2p_setup_task.sh`
**Purpose**: Load GPU P2P kernel modules for GPU VRAM → NVMe DMA

**When to run**: Once after boot (if using GPU memory modes)
```bash
sudo ./gpu_p2p_setup_task.sh
```

**What it does**:
- Builds gpu_p2p_core.ko (GPL)
- Builds gpu_p2p_nvidia.ko (Proprietary)
- Loads both kernel modules
- Creates /dev/gpu_p2p_core and /dev/gpu_p2p_nvidia

**Persists until**: Module unload (`rmmod`) or system reboot

**Note**: Only needed for Modes 2-6 (GPU memory). Not needed for Mode 0-1 (host memory).

---

### `setup_sudo_nopasswd.sh`
**Purpose**: Configure sudoers to allow test binaries to run privileged operations

**When to run**: Once per system setup
```bash
sudo ./setup_sudo_nopasswd.sh
```

**What it does**:
- Adds sudoers rules for specific test binaries
- Allows running tests without password prompts

**Persists until**: Sudoers file modified or system reinstall

---

## PER-TEST RUNTIME (Deprecated - Now Handled in C++)

**Previous Design:** Standalone daemon process required sudo

**Current Design:** In-process `DoorbellDaemon` thread (no sudo needed)

### ~~`host_dbc_daemon_task.sh`~~ (DEPRECATED)

**Status:** ⚠️ **Deprecated** - Replaced by in-process `DoorbellDaemon` class

**Why deprecated:**
- ❌ Required sudo (security risk - entire daemon ran as root)
- ❌ Complex lifecycle management (separate process)
- ❌ IPC overhead (passing shadow buffer address)

**New approach:**
```cpp
// In test code (no sudo needed):
#include "common/doorbell/doorbell_daemon.h"

ShadowDoorbellBuffer* shadow = allocate_shadow_doorbell_buffer(1);
DoorbellDaemon daemon(iosq, shadow, qid, 10us);
daemon.start();  // In-process thread
// ... run test ...
daemon.stop();
```

**Benefits:**
- ✅ No sudo required
- ✅ Same privileges as test (uses VFIO access)
- ✅ Simpler lifecycle (automatic with test)
- ✅ No IPC needed (same memory space)

**Legacy script location:** Kept for reference only in `daemon/legacy/`

**See:** `daemon/UNIFIED_DAEMON_DESIGN.md` for details

---

## NO SCRIPT NEEDED (See .md documentation)

These tasks are handled entirely in userspace C++ code.

### `nvme_setup_task.md`
**Why no script**: Uses VFIO userspace APIs (`open()`, `mmap()`, `ioctl()`)

### `dbc_shadow_buffer_task.md`
**Why no script**: Allocates host RAM with `cudaHostAlloc()` + VFIO mapping

### `host_doorbell_daemon_task.md`
**Why no script**: In-process thread (not standalone daemon)

### `gds_memory_factory_task.md`
**Why no script**: NVIDIA GDS stack (`nvidia-fs`, `cuFile`) handles everything

---

## Quick Reference

| Task | Script Type | Run Frequency | Required For |
|------|-------------|---------------|--------------|
| **VFIO Binding** | `.sh` | Once per boot | All modes |
| **GPU P2P Modules** | `.sh` | Once per boot | Modes 2-6 only |
| **Sudoers Config** | `.sh` | Once per system | Optional |
| ~~**DBC Daemon**~~ | ~~`.sh`~~ | ~~Per test~~ | **DEPRECATED** (use C++ class) |
| **NVMe Setup** | `.md` | — | (C++ handles it) |
| **Shadow Buffer** | `.md` | — | (C++ handles it) |
| **Doorbell Daemon** | `.md` | — | (C++ `DoorbellDaemon` class) |
| **GDS Factory** | `.md` | — | (NVIDIA handles it) |

---

## Typical Workflow

### Initial Setup (One-Time)
```bash
# 1. Bind NVMe to VFIO
sudo ./vfio_binding_task.sh

# 2. Load GPU P2P modules (if using GPU memory modes)
sudo ./gpu_p2p_setup_task.sh

# 3. Configure sudoers (optional, for password-less sudo in tests)
sudo ./setup_sudo_nopasswd.sh
```

### Running Tests (All Modes)
```bash
# No per-test scripts needed!
# Doorbell daemon is now in-process C++ thread

# Mode 0-1: Host memory
./test_mode0_baseline
./test_mode1_host_pinned

# Mode 2-3: Hardware DBC
./test_mode2_hardware_dbc

# Mode 5: GPU-initiated with daemon (daemon auto-starts in test)
./test_mode5_gpu_initiated_io
```

**No manual daemon management required** - tests handle everything internally!
