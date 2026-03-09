# 🎯 Part 51.3: System Setup

**Goal**: Configure VFIO, enable IOMMU, integrate GPU memory, and verify the complete development environment for GPU-NVMe interaction.

This section provides practical setup procedures, verification steps, and troubleshooting guidance for establishing a working GPU-NVMe development environment.

---

## Quick Navigation

- [51.3.1 VFIO Setup and Configuration](#5131-vfio-setup-and-configuration)
- [51.3.2 GPU Memory Integration](#5132-gpu-memory-integration)
- [51.3.3 Testing Environment and Verification](#5133-testing-environment-and-verification)

---

## **51.3.1 VFIO Setup and Configuration**

VFIO (Virtual Function I/O) is the recommended approach for safe user-space device access with IOMMU support.

### **User-Space I/O Approach Comparison**

| Feature | VFIO | UIO | Custom Module |
|---------|------|-----|---------------|
| **Safety** | ✅ High | ❌ None | ✅ High (if done right) |
| **GPU DMA** | ✅ Yes | ❌ No | ✅ Yes |
| **Setup Complexity** | Medium | Low | Very High |
| **Production Ready** | ✅ Yes | ❌ No | ⚠️ Depends |
| **Requires IOMMU** | ✅ Yes | ❌ No | ⚠️ Optional |
| **Root Privileges** | ⚠️ Initial setup | ✅ Always | ⚠️ Module load |

**Recommendation**: Use **VFIO** for GPU-NVMe integration.

### **Enabling IOMMU**

**Step 1: Check current status**

```bash
# Check if IOMMU is enabled
dmesg | grep -i iommu

# Expected output with IOMMU enabled:
# DMAR: IOMMU enabled
# iommu: Default domain type: Translated
```

**Step 2: Enable in BIOS/UEFI**

- **Intel**: Enable "VT-d" or "Intel Virtualization Technology for Directed I/O"
- **AMD**: Enable "AMD-Vi" or "IOMMU"

**Step 3: Enable in Linux kernel**

Edit `/etc/default/grub`:

```bash
# For Intel systems:
GRUB_CMDLINE_LINUX="intel_iommu=on iommu=pt"

# For AMD systems:
GRUB_CMDLINE_LINUX="amd_iommu=on iommu=pt"
```

Update GRUB and reboot:

```bash
sudo update-grub
sudo reboot
```

**Step 4: Load VFIO modules**

```bash
# Load VFIO modules
sudo modprobe vfio
sudo modprobe vfio-pci
sudo modprobe vfio_iommu_type1

# Verify
lsmod | grep vfio
```

### **VFIO Device Binding**

**Prerequisites:**
- IOMMU enabled
- Device not in use (unmount filesystems!)
- Device in separate IOMMU group (or entire group bound)

**Using the setup script:**

```bash
# Identify NVMe devices
lsblk -d -o NAME,SIZE,MODEL | grep nvme

# Check which is boot device (DO NOT BIND!)
lsblk | grep "/$"

# Bind non-boot NVMe to VFIO
sudo ./scripts/setup_vfio_nvme.sh bind 0000:01:00.0

# Verify binding
ls -la /dev/vfio/
```

**Manual binding process:**

```bash
# 1. Get device PCI address
lspci | grep NVMe
# Output: 01:00.0 Non-Volatile memory controller: Samsung...

# 2. Check IOMMU group
readlink /sys/bus/pci/devices/0000:01:00.0/iommu_group
# Output: ../../../../kernel/iommu_groups/1

# 3. Unbind from nvme driver
echo "0000:01:00.0" | sudo tee /sys/bus/pci/drivers/nvme/unbind

# 4. Get vendor:device ID
lspci -n -s 01:00.0
# Output: 01:00.0 0108: 144d:a808

# 5. Bind to vfio-pci
echo "144d a808" | sudo tee /sys/bus/pci/drivers/vfio-pci/new_id
```

### **Permissions for Non-Root Access**

**Add user to vfio group:**

```bash
# Add user to vfio group
sudo usermod -aG vfio $USER

# Logout and login for group to take effect
```

**Set VFIO device permissions** (via udev rule):

```bash
# Create /etc/udev/rules.d/99-vfio.rules
SUBSYSTEM=="vfio", OWNER="root", GROUP="vfio", MODE="0660"

# Reload udev rules
sudo udevadm control --reload-rules
sudo udevadm trigger
```

### **Restoring the Device**

```bash
# Unbind from vfio-pci
sudo ./scripts/setup_vfio_nvme.sh unbind 0000:01:00.0

# Rebind to nvme driver
echo "0000:01:00.0" | sudo tee /sys/bus/pci/drivers/nvme/bind

# Verify device is back
lsblk | grep nvme
```

---

## **51.3.2 GPU Memory Integration**

### **GPU Memory Allocation Options**

**1. cudaMalloc (GPU VRAM):**
```cpp
void* d_buffer;
cudaMalloc(&d_buffer, size);  // GPU VRAM only
```
- ❌ Not directly DMA-capable
- ✅ Requires nvidia_p2p_* APIs to get IOVAs
- ✅ Best performance for GPU access

**2. cudaMallocHost (Pinned host memory):**
```cpp
void* h_buffer;
cudaMallocHost(&h_buffer, size);  // Pinned host RAM
```
- ✅ CPU and GPU can access
- ✅ DMA-capable via VFIO_IOMMU_MAP_DMA
- ⚠️ Slower for GPU (PCIe overhead)

**3. cudaHostRegister (Register existing memory):**
```cpp
void* buffer = aligned_alloc(4096, size);
cudaHostRegister(buffer, size, cudaHostRegisterDefault);
```
- ✅ Pins existing allocation
- ✅ CPU and GPU can access
- ✅ DMA-capable via VFIO_IOMMU_MAP_DMA

### **GPU Memory to IOVA Translation**

**Option 1: nvidia_p2p_* APIs (requires kernel module)**

```c
// Kernel module code (not userspace!)
#include <nv-p2p.h>

nvidia_p2p_page_table_t* page_table;
nvidia_p2p_get_pages(
    0, 0,  // p2p_token, va_space
    gpu_vaddr,
    size,
    &page_table,
    free_callback,
    NULL
);

// page_table->pages[i]->physical_address contains IOVAs
```

**Option 2: Host pinned memory (userspace-friendly)**

```c
// Allocate pinned host memory
void* host_buffer;
cudaMallocHost(&host_buffer, size);

// Map to IOVA via VFIO
struct vfio_iommu_type1_dma_map map = {
    .argsz = sizeof(map),
    .flags = VFIO_DMA_MAP_FLAG_READ | VFIO_DMA_MAP_FLAG_WRITE,
    .vaddr = (uint64_t)host_buffer,
    .iova = 0x7000000000ULL,
    .size = size
};
ioctl(vfio_container, VFIO_IOMMU_MAP_DMA, &map);

// Now accessible by:
// - CPU: host_buffer (virtual address)
// - GPU: host_buffer (via cudaHostRegister)
// - NVMe: 0x7000000000 (IOVA from VFIO map)
```

---

## **51.3.3 Testing Environment and Verification**

### **Prerequisites Checklist**

```bash
# IOMMU enabled
dmesg | grep -E "DMAR|AMD-Vi|IOMMU"

# VFIO modules loaded
lsmod | grep vfio

# NVMe device detected
lsblk | grep nvme

# CUDA available
nvidia-smi

# User in vfio group
groups | grep vfio
```

### **Creating Test Files**

**Why contiguous files matter:**
- Fewer PRP list entries
- Single sequential DMA
- Maximum bandwidth
- Simpler testing

**Create test file:**

```bash
# Create 1GB test file
fallocate -l 1G /path/to/test_file.bin

# Check fragmentation
filefrag /path/to/test_file.bin
# /path/to/test_file.bin: 1 extent found (good!)

# If fragmented, defragment
sudo e4defrag /path/to/test_file.bin

# Verify contiguity
filefrag /path/to/test_file.bin
```

**Write pattern data:**

```bash
# Write sequential pattern
dd if=<(seq 0 255 | xargs -I{} printf "\\x$(printf %02x {})" | cat) \
   of=/path/to/test_file.bin bs=1M count=1024 conv=notrunc

# Verify first 256 bytes
xxd -l 256 /path/to/test_file.bin
```

### **Verification Script**

```bash
#!/bin/bash
# Complete system verification

echo "=== Hardware Verification ==="
echo -n "IOMMU enabled: "
dmesg | grep -q "IOMMU enabled" && echo "✅ YES" || echo "❌ NO"

echo -n "VT-d/AMD-Vi: "
dmesg | grep -qE "DMAR.*enabled|AMD-Vi.*enabled" && echo "✅ YES" || echo "❌ NO"

echo -e "\n=== Kernel Modules ==="
for mod in vfio vfio_pci vfio_iommu_type1 nvme nvidia; do
    echo -n "$mod: "
    lsmod | grep -q "^$mod " && echo "✅ Loaded" || echo "❌ Not loaded"
done

echo -e "\n=== VFIO Devices ==="
if [ -d /dev/vfio ]; then
    echo "✅ /dev/vfio exists"
    ls -la /dev/vfio/
else
    echo "❌ /dev/vfio not found"
fi

echo -e "\n=== NVMe Devices ==="
lsblk | grep nvme

echo -e "\n=== GPU Status ==="
nvidia-smi --query-gpu=name,driver_version --format=csv,noheader

echo -e "\n=== User Permissions ==="
echo -n "vfio group: "
groups | grep -q vfio && echo "✅ YES" || echo "❌ NO (run: sudo usermod -aG vfio $USER)"
```

### **Troubleshooting Common Issues**

| Error | Root Cause | Solution |
|-------|------------|----------|
| **IOMMU fault on DMA** | Used CPU-VA instead of IOVA | Always use IOVA from `VFIO_IOMMU_MAP_DMA` |
| **PRP alignment error** | PRP2 not page-aligned | Mask lower 12 bits: `iova & ~0xFFFULL` |
| **Admin queue timeout** | ASQ/ACQ base wrong | Use IOVA not VA: check mapping |
| **Permission denied /dev/vfio/** | User not in vfio group | `sudo usermod -aG vfio $USER` + re-login |
| **Cannot unbind device** | Device in use | `umount` all partitions first |
| **Boot failure** | Accidentally bound boot device | **Never bind boot NVMe!** |
| **GPU DMA fails** | nvidia-peermem not loaded | Check `lsmod | grep nvidia_peermem` |

---

## **Summary**

This section covered practical setup procedures:

1. **VFIO Configuration**: IOMMU enablement, device binding, permissions
2. **GPU Memory Integration**: Allocation options, IOVA translation methods
3. **Testing Environment**: File creation, verification checklist, troubleshooting

**Key Takeaways:**
- VFIO requires IOMMU enabled in BIOS + kernel
- Device binding must be done carefully (never bind boot device!)
- GPU memory requires special handling for IOVA translation
- Contiguous test files provide optimal performance

**Practical Exercises:**
1. ✅ Enable IOMMU and verify with `dmesg`
2. ✅ Bind a non-boot NVMe device to VFIO
3. ✅ Create contiguous test file and verify with `filefrag`
4. ✅ Run verification script and ensure all checks pass

**Next**: [Part 53: NVMe VFIO Host Layer](../../53.NVMe_VFIO_Host_Layer/README.md) - Start implementing user-space NVMe driver using these concepts!
