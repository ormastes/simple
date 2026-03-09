#!/usr/bin/env bash
# check_p2p_capability.sh
# Check if GPU-NVMe P2P (Peer-to-Peer) DMA is possible
#
# P2P DMA allows NVMe to write directly to GPU memory without
# going through system RAM, significantly improving performance.

set -euo pipefail

# Colors
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m' # No Color

echo "╔════════════════════════════════════════════════════════════════╗"
echo "║  GPU-NVMe P2P Capability Checker                             ║"
echo "╚════════════════════════════════════════════════════════════════╝"
echo

# Track overall status
P2P_POSSIBLE=true
ISSUES=()

# ============================================================================
# 1. Check IOMMU
# ============================================================================

echo -e "${BLUE}[1/8] Checking IOMMU...${NC}"

if dmesg 2>/dev/null | grep -qi "iommu.*enabled"; then
    echo -e "  ${GREEN}✓ IOMMU enabled${NC}"
    IOMMU_TYPE=$(dmesg 2>/dev/null | grep -i "iommu" | grep -i "enabled" | head -1)
    echo "    $IOMMU_TYPE"
else
    echo -e "  ${RED}✗ IOMMU not enabled${NC}"
    ISSUES+=("IOMMU not enabled - add intel_iommu=on or amd_iommu=on to kernel boot parameters")
    P2P_POSSIBLE=false
fi

# Check IOMMU passthrough mode
if grep -q "iommu=pt" /proc/cmdline 2>/dev/null; then
    echo -e "  ${GREEN}✓ IOMMU in passthrough mode (optimal)${NC}"
elif dmesg 2>/dev/null | grep -qi "iommu.*passthrough"; then
    echo -e "  ${GREEN}✓ IOMMU in passthrough mode${NC}"
else
    echo -e "  ${YELLOW}⚠ IOMMU not in passthrough mode (add iommu=pt for better performance)${NC}"
fi

echo

# ============================================================================
# 2. Check NVIDIA Driver and GPU
# ============================================================================

echo -e "${BLUE}[2/8] Checking NVIDIA GPU and driver...${NC}"

if command -v nvidia-smi &>/dev/null && nvidia-smi &>/dev/null; then
    echo -e "  ${GREEN}✓ NVIDIA GPU detected${NC}"
    GPU_COUNT=$(nvidia-smi --list-gpus 2>/dev/null | wc -l)
    echo "    GPUs: $GPU_COUNT"

    # Show GPU info
    nvidia-smi --query-gpu=index,name,pci.bus_id --format=csv,noheader 2>/dev/null | while read line; do
        echo "    $line"
    done

    # Check driver version
    DRIVER_VERSION=$(nvidia-smi --query-gpu=driver_version --format=csv,noheader 2>/dev/null | head -1)
    echo "    Driver version: $DRIVER_VERSION"
else
    echo -e "  ${RED}✗ NVIDIA GPU or driver not found${NC}"
    ISSUES+=("NVIDIA GPU/driver required for P2P")
    P2P_POSSIBLE=false
fi

echo

# ============================================================================
# 3. Check NVIDIA Kernel Modules
# ============================================================================

echo -e "${BLUE}[3/8] Checking NVIDIA kernel modules...${NC}"

if lsmod | grep -q "^nvidia "; then
    echo -e "  ${GREEN}✓ nvidia module loaded${NC}"
else
    echo -e "  ${RED}✗ nvidia module not loaded${NC}"
    ISSUES+=("nvidia kernel module not loaded")
    P2P_POSSIBLE=false
fi

# Check for nvidia-peermem (required for P2P)
if lsmod | grep -q "nvidia_peermem"; then
    echo -e "  ${GREEN}✓ nvidia-peermem module loaded (P2P support)${NC}"
elif lsmod | grep -q "nvidia_p2p"; then
    echo -e "  ${GREEN}✓ nvidia P2P module loaded${NC}"
else
    echo -e "  ${YELLOW}⚠ nvidia-peermem not loaded${NC}"
    echo "    P2P DMA requires nvidia-peermem or custom kernel module"
    ISSUES+=("nvidia-peermem module not loaded - P2P will not work without it")
fi

echo

# ============================================================================
# 4. Check NVMe Devices
# ============================================================================

echo -e "${BLUE}[4/8] Checking NVMe devices...${NC}"

if lspci | grep -i "nvme" >/dev/null; then
    echo -e "  ${GREEN}✓ NVMe devices found${NC}"

    lspci -nn | grep -i "nvme" | while read line; do
        BDF=$(echo "$line" | awk '{print $1}')
        echo "    $line"

        # Check if VFIO bound
        if [[ -e "/sys/bus/pci/devices/0000:$BDF/driver" ]]; then
            DRIVER=$(basename "$(readlink "/sys/bus/pci/devices/0000:$BDF/driver")")
            if [[ "$DRIVER" == "vfio-pci" ]]; then
                echo -e "      ${GREEN}✓ Bound to vfio-pci${NC}"
            else
                echo "      Driver: $DRIVER (use vfio-bind.sh to bind to vfio-pci)"
            fi
        fi
    done
else
    echo -e "  ${RED}✗ No NVMe devices found${NC}"
    ISSUES+=("No NVMe devices detected")
    P2P_POSSIBLE=false
fi

echo

# ============================================================================
# 5. Check PCIe Topology
# ============================================================================

echo -e "${BLUE}[5/8] Checking PCIe topology (GPU-NVMe proximity)...${NC}"

# Get GPU BDFs
GPU_BDFS=()
if command -v nvidia-smi &>/dev/null; then
    while read bdf; do
        # Remove domain prefix if present
        bdf_short=$(echo "$bdf" | sed 's/^0000://')
        GPU_BDFS+=("$bdf_short")
    done < <(nvidia-smi --query-gpu=pci.bus_id --format=csv,noheader 2>/dev/null)
fi

# Get NVMe BDFs
NVME_BDFS=()
while read line; do
    bdf=$(echo "$line" | awk '{print $1}')
    NVME_BDFS+=("$bdf")
done < <(lspci | grep -i "nvme" || true)

echo "  GPU-NVMe topology analysis:"

for gpu_bdf in "${GPU_BDFS[@]}"; do
    echo "    GPU: 0000:$gpu_bdf"

    # Get GPU root complex
    GPU_ROOT=$(lspci -tv 2>/dev/null | grep -B20 "$gpu_bdf" | grep "^\-\[" | tail -1 || echo "Unknown")

    for nvme_bdf in "${NVME_BDFS[@]}"; do
        echo "      NVMe: $nvme_bdf"

        # Get NVMe root complex
        NVME_ROOT=$(lspci -tv 2>/dev/null | grep -B20 "$nvme_bdf" | grep "^\-\[" | tail -1 || echo "Unknown")

        if [[ "$GPU_ROOT" == "$NVME_ROOT" ]]; then
            echo -e "        ${GREEN}✓ Same PCIe root complex (optimal P2P)${NC}"
        else
            echo -e "        ${YELLOW}⚠ Different PCIe root complex (P2P may have reduced performance)${NC}"
        fi
    done
done

echo

# ============================================================================
# 6. Check BAR (Base Address Register) Size
# ============================================================================

echo -e "${BLUE}[6/8] Checking GPU BAR size (Resizable BAR)...${NC}"

for gpu_bdf in "${GPU_BDFS[@]}"; do
    echo "  GPU 0000:$gpu_bdf:"

    # Check BAR sizes
    if [[ -e "/sys/bus/pci/devices/0000:$gpu_bdf/resource" ]]; then
        BAR0_SIZE=$(cat "/sys/bus/pci/devices/0000:$gpu_bdf/resource" | head -1 | awk '{printf "%.0f GB\n", (strtonum("0x"$2) - strtonum("0x"$1)) / 1024 / 1024 / 1024}')
        echo "    BAR0 size: $BAR0_SIZE"

        # Check if Resizable BAR is enabled (BAR should be large)
        BAR0_BYTES=$(cat "/sys/bus/pci/devices/0000:$gpu_bdf/resource" | head -1 | awk '{print strtonum("0x"$2) - strtonum("0x"$1)}')
        if [[ $BAR0_BYTES -gt $((16 * 1024 * 1024 * 1024)) ]]; then
            echo -e "    ${GREEN}✓ Resizable BAR likely enabled (large BAR size)${NC}"
        else
            echo -e "    ${YELLOW}⚠ Small BAR size - consider enabling Resizable BAR in BIOS${NC}"
            echo "      Resizable BAR improves P2P performance"
        fi
    fi
done

echo

# ============================================================================
# 7. Check CUDA and GPUDirect Storage
# ============================================================================

echo -e "${BLUE}[7/8] Checking CUDA and GPUDirect Storage...${NC}"

# Check CUDA
if command -v nvcc &>/dev/null; then
    CUDA_VERSION=$(nvcc --version | grep "release" | awk '{print $5}' | sed 's/,//')
    echo -e "  ${GREEN}✓ CUDA installed${NC}"
    echo "    Version: $CUDA_VERSION"
else
    echo -e "  ${YELLOW}⚠ CUDA compiler not in PATH${NC}"
fi

# Check for GPUDirect Storage (cuFile)
if ldconfig -p 2>/dev/null | grep -q "libcufile"; then
    echo -e "  ${GREEN}✓ cuFile library found (GPUDirect Storage)${NC}"
    CUFILE_PATH=$(ldconfig -p | grep "libcufile" | head -1 | awk '{print $NF}')
    echo "    Path: $CUFILE_PATH"
elif [[ -e "/usr/local/cuda/lib64/libcufile.so" ]]; then
    echo -e "  ${GREEN}✓ cuFile library found in CUDA directory${NC}"
else
    echo -e "  ${YELLOW}⚠ GPUDirect Storage (cuFile) not found${NC}"
    echo "    Install CUDA GDS from: https://developer.nvidia.com/gpudirect-storage"
    ISSUES+=("GPUDirect Storage (cuFile) not installed - recommended for P2P")
fi

echo

# ============================================================================
# 8. Check Above 4G Decoding (BIOS setting)
# ============================================================================

echo -e "${BLUE}[8/8] Checking Above 4G Decoding...${NC}"

# This is harder to check from software, but we can look for evidence
LARGE_BARS_FOUND=false
for gpu_bdf in "${GPU_BDFS[@]}"; do
    if [[ -e "/sys/bus/pci/devices/0000:$gpu_bdf/resource" ]]; then
        while read start end flags; do
            if [[ -n "$start" && "$start" != "0x0000000000000000" ]]; then
                start_dec=$((16#${start#0x}))
                if [[ $start_dec -gt $((4 * 1024 * 1024 * 1024)) ]]; then
                    LARGE_BARS_FOUND=true
                    break
                fi
            fi
        done < <(cat "/sys/bus/pci/devices/0000:$gpu_bdf/resource" | grep "0x")
    fi
done

if [[ "$LARGE_BARS_FOUND" == "true" ]]; then
    echo -e "  ${GREEN}✓ Above 4G Decoding likely enabled (BARs mapped above 4GB)${NC}"
else
    echo -e "  ${YELLOW}⚠ Cannot confirm Above 4G Decoding${NC}"
    echo "    Enable in BIOS if GPU P2P DMA has issues"
fi

echo

# ============================================================================
# Summary
# ============================================================================

echo "═══════════════════════════════════════════════════════════════"
echo "                         SUMMARY                                "
echo "═══════════════════════════════════════════════════════════════"
echo

if [[ "$P2P_POSSIBLE" == "true" && ${#ISSUES[@]} -eq 0 ]]; then
    echo -e "${GREEN}✓ GPU-NVMe P2P DMA appears to be possible!${NC}"
    echo
    echo "Your system has the basic requirements for P2P DMA."
    echo "Additional software (nvidia-peermem or custom kernel module) may be needed."
elif [[ ${#ISSUES[@]} -gt 0 ]]; then
    echo -e "${YELLOW}⚠ P2P DMA may be possible, but issues found:${NC}"
    echo
    for issue in "${ISSUES[@]}"; do
        echo "  • $issue"
    done
else
    echo -e "${RED}✗ P2P DMA not possible - critical requirements missing${NC}"
fi

echo
echo "═══════════════════════════════════════════════════════════════"
echo

# ============================================================================
# Recommendations
# ============================================================================

if [[ ${#ISSUES[@]} -gt 0 ]]; then
    echo "RECOMMENDATIONS:"
    echo

    # IOMMU
    if printf '%s\n' "${ISSUES[@]}" | grep -q "IOMMU"; then
        echo "1. Enable IOMMU:"
        echo "   • Edit /etc/default/grub:"
        echo "     GRUB_CMDLINE_LINUX=\"intel_iommu=on iommu=pt\"  # or amd_iommu=on"
        echo "   • sudo update-grub && sudo reboot"
        echo
    fi

    # nvidia-peermem
    if printf '%s\n' "${ISSUES[@]}" | grep -q "nvidia-peermem"; then
        echo "2. Install nvidia-peermem:"
        echo "   Option A: Use GPUDirect Storage (recommended):"
        echo "     • Download from: https://developer.nvidia.com/gpudirect-storage"
        echo "     • Includes nvidia-fs kernel module with P2P support"
        echo
        echo "   Option B: Build nvidia-peermem from source:"
        echo "     • git clone https://github.com/Mellanox/nv_peer_memory"
        echo "     • cd nv_peer_memory && ./build_module.sh"
        echo "     • sudo insmod nvidia-peermem.ko"
        echo
    fi

    # Resizable BAR
    if lspci -vv 2>/dev/null | grep -A5 "VGA\|3D" | grep -q "Region 0.*256M"; then
        echo "3. Enable Resizable BAR (optional, improves performance):"
        echo "   • Enable in BIOS: Above 4G Decoding + Resizable BAR"
        echo "   • Requires UEFI boot mode (not Legacy)"
        echo
    fi
fi

echo "For more information, see:"
echo "  /home/ormastes/dev/pub/cuda_exercise/50.GPU-NVMe_Interaction/51.Knowledge_and_VFIO_Setup/51.3.System_Setup/README.md"
echo
