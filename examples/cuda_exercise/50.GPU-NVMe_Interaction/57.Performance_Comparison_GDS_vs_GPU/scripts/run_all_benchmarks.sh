#!/bin/bash
# Comprehensive NVMe-GPU I/O Performance Benchmarking Suite
# Auto-detects hardware capabilities and runs all applicable modes
# Output: PERFORMANCE_LOG.md in build/50.GPU-NVMe_Interaction/57.Performance_Comparison_GDS_vs_GPU/

set -euo pipefail

# Colors
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
CYAN='\033[0;36m'
MAGENTA='\033[0;35m'
NC='\033[0m'

print_error() { echo -e "${RED}[ERROR]${NC} $@"; }
print_success() { echo -e "${GREEN}[SUCCESS]${NC} $@"; }
print_warning() { echo -e "${YELLOW}[WARNING]${NC} $@"; }
print_info() { echo -e "${BLUE}[INFO]${NC} $@"; }
print_skip() { echo -e "${YELLOW}[SKIP]${NC} $@"; }
print_header() { echo -e "${CYAN}═══════════════════════════════════════════════════════════════${NC}"; }
print_section() { echo -e "${MAGENTA}[SECTION]${NC} $@"; }

# Script paths
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
MODULE_57_DIR="$(dirname "$SCRIPT_DIR")"
PROJECT_ROOT="$(cd "${MODULE_57_DIR}/../.." && pwd)"
GPU_NVME_ROOT="${PROJECT_ROOT}/50.GPU-NVMe_Interaction"
REPORT_DIR="${PROJECT_ROOT}/build/50.GPU-NVMe_Interaction/57.Performance_Comparison_GDS_vs_GPU"

# Output file
TIMESTAMP=$(date +%Y%m%d_%H%M%S)
PERFORMANCE_LOG="${REPORT_DIR}/PERFORMANCE_LOG_${TIMESTAMP}.md"
IOPS_TABLE="${REPORT_DIR}/IOPS_SUMMARY_${TIMESTAMP}.md"
TEMP_LOG="/tmp/benchmark_results_${TIMESTAMP}.txt"
mkdir -p "${REPORT_DIR}"

# Benchmark results storage
declare -A BENCHMARK_STATUS
declare -A BENCHMARK_IOPS

# Hardware capability flags
HAS_VFIO=false
HAS_P2P_MODULE=false
HAS_NVME_ENV=false
NVME_DEVICES=()

# ============================================================================
# Driver verification
# ============================================================================

check_proprietary_nvidia_driver() {
    local sym_file="/lib/modules/$(uname -r)/modules.symbols"
    local required_symbol="nvidia_p2p_dma_map_pages"

    if [[ ! -f "$sym_file" ]]; then
        print_error "Kernel symbols file not found: ${sym_file}"
        print_info "Ensure kernel modules are installed for $(uname -r)"
        exit 1
    fi

    if ! grep -q "${required_symbol}" "$sym_file"; then
        print_error "Unsupported NVIDIA driver detected (missing ${required_symbol})."
        print_info "Install the proprietary NVIDIA driver; the open kernel module does not expose this symbol."
        exit 1
    fi

    print_success "NVIDIA driver exports ${required_symbol} (proprietary driver detected)."
}

# ============================================================================
# Helper functions
# ============================================================================

# Keep module 57 aligned with module 53 env helpers
source_module53_env() {
    if [[ -z "${NVME_BDF:-}" && -f /tmp/_nvme_test_env.sh ]]; then
        source /tmp/_nvme_test_env.sh
    fi
    if [[ -z "${NVME_BDF_2:-}" && -z "${NVME_BDF2:-}" && -f /tmp/_nvme_test_env_dual.sh ]]; then
        source /tmp/_nvme_test_env_dual.sh
    fi

    # Backwards compatibility with earlier docs
    if [[ -n "${NVME_BDF2:-}" && -z "${NVME_BDF_2:-}" ]]; then
        NVME_BDF_2="${NVME_BDF2}"
    fi
}

# Resolve the namespace block device for a given BDF (e.g., /dev/nvme2n1)
resolve_namespace_for_bdf() {
    local bdf="$1"
    local pci_path="/sys/bus/pci/devices/${bdf}"
    local nvme_dir namespace_dir

    nvme_dir=$(ls -d "${pci_path}"/nvme/nvme* 2>/dev/null | head -n1 || true)
    if [[ -z "$nvme_dir" ]]; then
        echo ""
        return
    fi

    namespace_dir=$(ls -d "${nvme_dir}"/nvme*n* 2>/dev/null | head -n1 || true)
    if [[ -z "$namespace_dir" ]]; then
        echo ""
        return
    fi

    echo "/dev/$(basename "$namespace_dir")"
}

# Check whether a block device (including its partitions) is mounted
is_device_mounted() {
    local device="$1"
    [[ -b "$device" ]] || return 1

    if lsblk -rno MOUNTPOINT "$device" 2>/dev/null | grep -qE '.+'; then
        return 0
    fi

    local dev_name
    dev_name=$(basename "$device")
    if lsblk -rno NAME,MOUNTPOINT "/dev/${dev_name}" 2>/dev/null | awk 'NF==2 && $2 != ""' | grep -q .; then
        return 0
    fi

    return 1
}

# Detect DBC support on a specific device node
device_supports_dbc() {
    local device_node="$1"
    if ! command -v nvme &>/dev/null; then
        print_warning "nvme-cli not installed, cannot check DBC capability for ${device_node}"
        return 1
    fi

    local oacs
    oacs=$(nvme id-ctrl "$device_node" 2>/dev/null | awk '/oacs/ {print $3}' || echo "")
    if [[ -z "$oacs" ]]; then
        return 1
    fi

    local oacs_dec=$((16#${oacs#0x}))
    local dbc_bit=$(( (oacs_dec >> 8) & 1 ))
    [[ $dbc_bit -eq 1 ]]
}

print_device_status() {
    local key="$1"
    local status="$2"
    if [[ "$status" == "SUCCESS" ]]; then
        print_success "  ${key}: ${status}"
    elif [[ "$status" == "FAILED" ]]; then
        print_error "  ${key}: ${status}"
    else
        print_warning "  ${key}: ${status}"
    fi
}

source_module53_env

echo ""
print_header
echo -e "${CYAN}   GPU-NVMe I/O Performance Benchmark Suite${NC}"
echo -e "${CYAN}   Module 57: 6-Way Performance Comparison${NC}"
print_header
echo ""

# Require proprietary NVIDIA driver (exports nvidia_p2p_dma_map_pages)
check_proprietary_nvidia_driver

# ============================================================================
# Hardware Detection
# ============================================================================

print_section "Hardware Capability Detection"
echo ""

# Check VFIO
print_info "Checking VFIO..."
if [[ -c /dev/vfio/vfio ]]; then
    HAS_VFIO=true
    print_success "VFIO: Available"
else
    print_error "VFIO: Not available"
    print_info "Run module 53's setup_vfio.sh to configure VFIO"
    exit 1
fi

# Check environment variables (shared for both devices)
print_info "Checking NVMe environment variables..."
if [[ -n "${NVME_NSID:-}" && -n "${NVME_LBA_SIZE:-}" && -n "${NVME_SLBA:-}" ]]; then
    HAS_NVME_ENV=true
    print_success "NVMe Environment: NSID=${NVME_NSID}, LBA_SIZE=${NVME_LBA_SIZE}, SLBA=${NVME_SLBA}"
else
    print_error "NVMe Environment: Missing NVME_NSID / NVME_LBA_SIZE / NVME_SLBA"
    print_info "Source the environment file (generated by module 53 tooling):"
    print_info "  source /tmp/_nvme_test_env.sh"
    print_info "Or set manually:"
    print_info "  export NVME_NSID='1'"
    print_info "  export NVME_LBA_SIZE='512'"
    print_info "  export NVME_SLBA='1000000'"
    exit 1
fi

# Collect NVMe devices (primary + optional secondary)
declare -A _seen_bdfs
for candidate in "${NVME_BDF:-}" "${NVME_BDF_2:-}" "${NVME_BDF_WITH_DBC:-}" "${NVME_BDF_NO_DBC:-}"; do
    if [[ -n "$candidate" && -z "${_seen_bdfs[$candidate]:-}" ]]; then
        NVME_DEVICES+=("$candidate")
        _seen_bdfs[$candidate]=1
    fi
done

if [[ ${#NVME_DEVICES[@]} -eq 0 ]]; then
    print_error "No NVMe test devices configured."
    print_info "Set NVME_BDF for the primary test device, optionally NVME_BDF_2 for a second (non-OS) device."
    exit 1
fi

# Check P2P module
print_info "Checking GPU P2P module..."
if [[ -c /dev/gpu_p2p_nvme ]]; then
    HAS_P2P_MODULE=true
    print_success "P2P Module: /dev/gpu_p2p_nvme available"
else
    print_warning "P2P Module: Not available"
    print_info "  Modes 2, 4, and hardware DBC will be skipped"
    print_info "  Modes 3 and 5 will use pinned memory fallback"
fi

echo ""
print_header
print_section "Benchmark Execution Plan"
echo ""

# ============================================================================
# Run Benchmarks per NVMe device (skip OS drives unless explicitly allowed)
# ============================================================================

TOTAL_MODES=0
SUCCESSFUL_MODES=0

for NVME_BDF in "${NVME_DEVICES[@]}"; do
    print_header
    print_section "Preparing device ${NVME_BDF}"

    DEVICE_NODE=$(resolve_namespace_for_bdf "$NVME_BDF")
    if [[ -z "$DEVICE_NODE" ]]; then
        print_warning "Could not resolve namespace for ${NVME_BDF} (likely VFIO-bound) - skipping OS-drive check"
    else
        if is_device_mounted "$DEVICE_NODE" && [[ "${ALLOW_OS_NVME:-0}" != "1" ]]; then
            print_warning "Device ${NVME_BDF} (${DEVICE_NODE}) appears to be mounted. Skipping to avoid OS drive."
            for MODE in 1 2 3 4 5 6; do
                BENCHMARK_STATUS["${NVME_BDF}_mode${MODE}"]="SKIPPED"
            done
            continue
        fi
    fi

    DEVICE_HAS_DBC=false
    if [[ -n "${NVME_BDF_WITH_DBC:-}" && "$NVME_BDF" == "$NVME_BDF_WITH_DBC" ]]; then
        DEVICE_HAS_DBC=true
        print_success "DBC Capability: Marked supported via NVME_BDF_WITH_DBC for ${NVME_BDF}"
    elif [[ -n "$DEVICE_NODE" ]] && device_supports_dbc "$DEVICE_NODE"; then
        DEVICE_HAS_DBC=true
        print_success "DBC Capability: Supported for ${NVME_BDF}"
    else
        print_warning "DBC Capability: Not detected for ${NVME_BDF}"
    fi

    MODES_TO_RUN=()
    MODES_TO_RUN+=("1")
    if $HAS_P2P_MODULE; then MODES_TO_RUN+=("2"); fi
    MODES_TO_RUN+=("3")
    if $HAS_P2P_MODULE && $DEVICE_HAS_DBC; then MODES_TO_RUN+=("4"); fi
    MODES_TO_RUN+=("5")

    # Always exercise Mode 6 to validate GPU command path, even without P2P/DBC.
    # Lacking P2P falls back to pinned host mapping; lacking DBC uses daemon mirror.
    if ! $HAS_P2P_MODULE; then
        print_warning "Mode 6: P2P module missing - will use pinned host fallback for ${NVME_BDF}"
    fi
    if ! $DEVICE_HAS_DBC; then
        print_warning "Mode 6: DBC not detected - will run with daemon-based mirror for ${NVME_BDF}"
    fi
    MODES_TO_RUN+=("6")

    echo ""
    print_info "Modes scheduled for ${NVME_BDF}: ${MODES_TO_RUN[*]}"
    echo ""

    for MODE in "${MODES_TO_RUN[@]}"; do
        ((TOTAL_MODES++))
        echo ""
        print_info "════════════════════════════════════════════════════════"
        print_info "  Running Mode ${MODE} Benchmark on ${NVME_BDF}"
        print_info "════════════════════════════════════════════════════════"
        echo ""

        BENCHMARK_SCRIPT="${SCRIPT_DIR}/run_mode${MODE}_benchmark.sh"

        if [[ ! -f "$BENCHMARK_SCRIPT" ]]; then
            print_error "Benchmark script not found: $BENCHMARK_SCRIPT"
            BENCHMARK_STATUS["${NVME_BDF}_mode${MODE}"]="MISSING"
            continue
        fi

        MODE_ENV=()
        if [[ "$MODE" == "6" ]]; then
            MODE_ENV+=(ALLOW_P2P_FALLBACK=1)
        fi

        start_line=$(wc -l < "$TEMP_LOG" 2>/dev/null || true)
        if [[ -z "$start_line" ]]; then start_line=0; fi

        if "${MODE_ENV[@]}" NVME_BDF="$NVME_BDF" NVME_NSID="$NVME_NSID" NVME_LBA_SIZE="$NVME_LBA_SIZE" NVME_SLBA="$NVME_SLBA" \
            bash "$BENCHMARK_SCRIPT" 2>&1 | tee -a "$TEMP_LOG"; then
            BENCHMARK_STATUS["${NVME_BDF}_mode${MODE}"]="SUCCESS"
            print_success "Mode ${MODE} on ${NVME_BDF} completed successfully"
            ((SUCCESSFUL_MODES++))
        else
            BENCHMARK_STATUS["${NVME_BDF}_mode${MODE}"]="FAILED"
            print_error "Mode ${MODE} on ${NVME_BDF} failed"
        fi

        end_line=$(wc -l < "$TEMP_LOG" 2>/dev/null || true)
        if [[ -z "$end_line" ]]; then end_line="$start_line"; fi
        segment_start=$((start_line + 1))
        if [[ $segment_start -lt 1 ]]; then segment_start=1; fi
        MODE_SEGMENT=$(sed -n "${segment_start},${end_line}p" "$TEMP_LOG")
        mode_iops=$(echo "$MODE_SEGMENT" | grep -Eo "Measured IOPS:\\s*[0-9]+(\\.[0-9]+)?" | tail -1 | awk '{print $3}')
        if [[ -z "$mode_iops" ]]; then
            mode_iops=$(echo "$MODE_SEGMENT" | grep -Eo "IOPS[:=][[:space:]]*[0-9,]+(\\.[0-9]+)?" | tail -1 | sed 's/.*[=:] *//' | tr -d ',' )
        fi
        [[ -z "$mode_iops" ]] && mode_iops="N/A"
        BENCHMARK_IOPS["${NVME_BDF}_mode${MODE}"]="$mode_iops"

        echo ""
    done
done

# ============================================================================
# Generate Performance Report
# ============================================================================

print_header
print_section "Generating Performance Report"
print_header
echo ""

print_info "Writing performance log to: $PERFORMANCE_LOG"
print_info "Writing IOPS summary to:    $IOPS_TABLE"

cat > "$PERFORMANCE_LOG" <<EOF
# GPU-NVMe I/O Performance Benchmark Results

**Generated**: $(date '+%Y-%m-%d %H:%M:%S')
**System**: $(uname -n) - $(uname -r)
**GPU**: $(nvidia-smi --query-gpu=name --format=csv,noheader 2>/dev/null || echo "Unknown")

---

## Hardware Capabilities

| Component | Status | Notes |
|-----------|--------|-------|
| VFIO | $([ "$HAS_VFIO" = true ] && echo "✅ Available" || echo "❌ Not Available") | Required for all modes |
| NVMe Environment | $([ "$HAS_NVME_ENV" = true ] && echo "✅ Configured" || echo "❌ Not Configured") | NVME_NSID/LBA settings shared across devices |
| P2P Module | $([ "$HAS_P2P_MODULE" = true ] && echo "✅ Available" || echo "⚠️ Not Available") | Required for Modes 2, 4, 6; optional for 3, 5 |

---

## Benchmark Results Summary (per NVMe device)

EOF

for NVME_BDF in "${NVME_DEVICES[@]}"; do
cat >> "$PERFORMANCE_LOG" <<EOF

### Device ${NVME_BDF}

| Mode | Description | Status | IOPS | Notes |
|------|-------------|--------|------|-------|
| **1** | Host + MMIO (Baseline) | ${BENCHMARK_STATUS[${NVME_BDF}_mode1]:-SKIPPED} | ${BENCHMARK_IOPS[${NVME_BDF}_mode1]:-N/A} | Traditional CPU-managed I/O |
| **2** | Host Daemon + GPU Memory | ${BENCHMARK_STATUS[${NVME_BDF}_mode2]:-SKIPPED} | ${BENCHMARK_IOPS[${NVME_BDF}_mode2]:-N/A} | Requires P2P module |
| **3** | Host + Daemon | ${BENCHMARK_STATUS[${NVME_BDF}_mode3]:-SKIPPED} | ${BENCHMARK_IOPS[${NVME_BDF}_mode3]:-N/A} | Falls back to pinned memory if no P2P |
| **4** | DBC Shadow + GPU | ${BENCHMARK_STATUS[${NVME_BDF}_mode4]:-SKIPPED} | ${BENCHMARK_IOPS[${NVME_BDF}_mode4]:-N/A} | Requires DBC + P2P |
| **5** | GPU + Daemon | ${BENCHMARK_STATUS[${NVME_BDF}_mode5]:-SKIPPED} | ${BENCHMARK_IOPS[${NVME_BDF}_mode5]:-N/A} | True GPU autonomy |
| **6** | Hardware DBC (GPU) | ${BENCHMARK_STATUS[${NVME_BDF}_mode6]:-SKIPPED} | ${BENCHMARK_IOPS[${NVME_BDF}_mode6]:-N/A} | Prefers DBC+P2P; falls back to daemon+pinned |

---
EOF
done

cat >> "$PERFORMANCE_LOG" <<EOF

## Mode Architecture Comparison

### Mode 1: Host + MMIO (Baseline)
- **Command Building**: CPU
- **I/O Queue**: Host memory
- **Data Buffer**: Pinned host memory
- **Doorbell**: Direct MMIO from CPU
- **CPU Overhead**: HIGH (per I/O)
- **GPU Autonomy**: 0%

### Mode 2: Host Daemon + GPU Memory
- **Command Building**: CPU
- **I/O Queue**: GPU VRAM
- **Data Buffer**: GPU VRAM (P2P)
- **Doorbell**: Daemon polls GPU memory
- **CPU Overhead**: LOW (daemon only)
- **GPU Autonomy**: 0%

### Mode 3: Host + Daemon
- **Command Building**: CPU
- **I/O Queue**: Host/GPU memory
- **Data Buffer**: GPU VRAM (P2P) or Pinned Host
- **Doorbell**: Daemon polls shadow buffer
- **CPU Overhead**: LOW (daemon only)
- **GPU Autonomy**: 0%

### Mode 4: DBC Shadow + GPU
- **Command Building**: GPU
- **I/O Queue**: GPU VRAM
- **Data Buffer**: GPU VRAM (P2P)
- **Doorbell**: NVMe polls DBC shadow (DMA)
- **CPU Overhead**: ZERO (hardware polling)
- **GPU Autonomy**: 90%

### Mode 5: GPU + Daemon
- **Command Building**: GPU
- **I/O Queue**: GPU VRAM
- **Data Buffer**: GPU VRAM (P2P) or Pinned Host
- **Doorbell**: Daemon polls shadow buffer
- **CPU Overhead**: LOW (daemon only)
- **GPU Autonomy**: 90%

### Mode 6: Hardware DBC (GPU)
- **Command Building**: GPU
- **Doorbell**: NVMe hardware polls shadow buffer via DMA
- **Dependency**: Requires DBC-capable NVMe + P2P module

---

## Detailed Results

EOF

# Append detailed results from temp log
if [[ -f "$TEMP_LOG" ]]; then
    echo "" >> "$PERFORMANCE_LOG"
    echo "### Benchmark Execution Log" >> "$PERFORMANCE_LOG"
    echo '```' >> "$PERFORMANCE_LOG"
    cat "$TEMP_LOG" >> "$PERFORMANCE_LOG"
    echo '```' >> "$PERFORMANCE_LOG"
fi

print_success "Performance log generated: $PERFORMANCE_LOG"

# ============================================================================
# Generate IOPS-only summary table (compact)
# ============================================================================
cat > "$IOPS_TABLE" <<EOF
# Module 57 IOPS Summary

**Generated**: $(date '+%Y-%m-%d %H:%M:%S')

Compact IOPS/status matrix per mode and device.

EOF

for NVME_BDF in "${NVME_DEVICES[@]}"; do
cat >> "$IOPS_TABLE" <<EOF
## Device ${NVME_BDF}

| Mode | Status | IOPS |
|------|--------|------|
| 1 | ${BENCHMARK_STATUS[${NVME_BDF}_mode1]:-SKIPPED} | ${BENCHMARK_IOPS[${NVME_BDF}_mode1]:-N/A} |
| 2 | ${BENCHMARK_STATUS[${NVME_BDF}_mode2]:-SKIPPED} | ${BENCHMARK_IOPS[${NVME_BDF}_mode2]:-N/A} |
| 3 | ${BENCHMARK_STATUS[${NVME_BDF}_mode3]:-SKIPPED} | ${BENCHMARK_IOPS[${NVME_BDF}_mode3]:-N/A} |
| 4 | ${BENCHMARK_STATUS[${NVME_BDF}_mode4]:-SKIPPED} | ${BENCHMARK_IOPS[${NVME_BDF}_mode4]:-N/A} |
| 5 | ${BENCHMARK_STATUS[${NVME_BDF}_mode5]:-SKIPPED} | ${BENCHMARK_IOPS[${NVME_BDF}_mode5]:-N/A} |
| 6 | ${BENCHMARK_STATUS[${NVME_BDF}_mode6]:-SKIPPED} | ${BENCHMARK_IOPS[${NVME_BDF}_mode6]:-N/A} |

EOF
done

print_success "IOPS summary generated:    $IOPS_TABLE"

# ============================================================================
# Summary
# ============================================================================

echo ""
print_header
print_section "Benchmark Suite Complete"
print_header
echo ""

print_info "Results Summary:"
for key in "${!BENCHMARK_STATUS[@]}"; do
    print_device_status "$key" "${BENCHMARK_STATUS[$key]}"
done

echo ""
print_info "Performance log: ${PERFORMANCE_LOG}"
print_info "Temporary log: ${TEMP_LOG}"
echo ""

print_info "Success Rate: ${SUCCESSFUL_MODES}/${TOTAL_MODES} modes completed"
echo ""

if [[ $SUCCESSFUL_MODES -eq $TOTAL_MODES && $TOTAL_MODES -gt 0 ]]; then
    print_success "All benchmarks completed successfully!"
    exit 0
else
    print_warning "Some benchmarks failed or were skipped"
    exit 1
fi
