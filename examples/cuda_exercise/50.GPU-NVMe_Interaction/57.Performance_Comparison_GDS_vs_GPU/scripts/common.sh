#!/bin/bash
# Common functions for Mode 1-6 benchmark scripts
# Source this file at the beginning of each run_mode*.sh script

set -euo pipefail

# ═══════════════════════════════════════════════════════════════
# Color Definitions
# ═══════════════════════════════════════════════════════════════
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m'

# ═══════════════════════════════════════════════════════════════
# Print Helper Functions
# ═══════════════════════════════════════════════════════════════
print_error() { echo -e "${RED}[ERROR]${NC} $@"; }
print_success() { echo -e "${GREEN}[SUCCESS]${NC} $@"; }
print_warning() { echo -e "${YELLOW}[WARNING]${NC} $@"; }
print_info() { echo -e "${BLUE}[INFO]${NC} $@"; }

# ═══════════════════════════════════════════════════════════════
# Path Setup
# ═══════════════════════════════════════════════════════════════
# Use BASH_SOURCE[0] for this file, and if that doesn't work, fall back to the caller's directory
COMMON_SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
SCRIPT_DIR="${COMMON_SCRIPT_DIR}"
MODULE_57_DIR="$(dirname "$SCRIPT_DIR")"
MODULE_56_DIR="${MODULE_57_DIR}/../56.GPU_Queue_GPU_Buffer"
PROJECT_ROOT="$(cd "${MODULE_57_DIR}/../.." && pwd)"
BUILD_DIR="${PROJECT_ROOT}/build"

# ═══════════════════════════════════════════════════════════════
# Binary Path Resolver
# Maps mode number to actual executable binary
# ═══════════════════════════════════════════════════════════════
# Usage: get_benchmark_binary MODE_NUMBER
#   MODE_NUMBER: 0-6
# Returns: Full path to benchmark executable
get_benchmark_binary() {
    local mode=$1
    local binary=""

    case $mode in
        0)
            # Mode 0: Host + MMIO + Pageable Memory (BASELINE)
            binary="${BUILD_DIR}/50.GPU-NVMe_Interaction/57.Performance_Comparison_GDS_vs_GPU/benchmark_mode0"
            ;;
        1)
            # Mode 1: Host + MMIO (Module 57's GDS benchmark)
            binary="${BUILD_DIR}/50.GPU-NVMe_Interaction/57.Performance_Comparison_GDS_vs_GPU/benchmark_gds"
            ;;
        2)
            # Mode 2: Host Daemon + GPU Memory (Module 57)
            # Note: CMakeLists defines benchmark_mode2_host_daemon_gpu_mem, but actual binary is benchmark_mode2
            binary="${BUILD_DIR}/50.GPU-NVMe_Interaction/57.Performance_Comparison_GDS_vs_GPU/benchmark_mode2"
            ;;
        3)
            # Mode 3: Host + Daemon (Module 57)
            binary="${BUILD_DIR}/50.GPU-NVMe_Interaction/57.Performance_Comparison_GDS_vs_GPU/benchmark_mode3"
            ;;
        31)
            # Mode 3.1: Host + GDS/cuFile (optional GPU buffer via GDS)
            binary="${BUILD_DIR}/50.GPU-NVMe_Interaction/57.Performance_Comparison_GDS_vs_GPU/benchmark_mode3_gds_cufile"
            ;;
        4)
            # Mode 4: DBC Shadow + GPU (Module 57)
            # Note: CMakeLists defines benchmark_mode4_dbc_shadow_gpu, but actual binary is benchmark_mode4
            binary="${BUILD_DIR}/50.GPU-NVMe_Interaction/57.Performance_Comparison_GDS_vs_GPU/benchmark_mode4"
            ;;
        5)
            # Mode 5: GPU + Daemon (Module 57)
            binary="${BUILD_DIR}/50.GPU-NVMe_Interaction/57.Performance_Comparison_GDS_vs_GPU/benchmark_mode5_dbc_daemon_gpu_command"
            ;;
        6)
            # Mode 6: GPU + Hardware DBC (Module 57)
            binary="${BUILD_DIR}/50.GPU-NVMe_Interaction/57.Performance_Comparison_GDS_vs_GPU/benchmark_mode6_hardware_dbc_gpu"
            ;;
        *)
            print_error "Invalid mode number: $mode (must be 0-6 or 31 for GDS/cuFile optional path)"
            return 1
            ;;
    esac

    echo "$binary"
}

# ═══════════════════════════════════════════════════════════════
# Process Cleanup Functions
# ═══════════════════════════════════════════════════════════════

# Kill any pre-existing daemon processes to avoid conflicts
# Usage: cleanup_daemon_processes
cleanup_daemon_processes() {
    print_info "Cleaning up any pre-existing daemon processes..."
    pkill -9 -f "host_dbc_daemon" 2>/dev/null || true
    pkill -9 -f "host_dbc_daemon_realtime" 2>/dev/null || true
    pkill -9 -f "benchmark_mode" 2>/dev/null || true
    sleep 0.5  # Wait for processes to terminate
}

# Kill any pre-existing benchmark processes to avoid conflicts
# Usage: cleanup_benchmark_processes
cleanup_benchmark_processes() {
    print_info "Cleaning up any pre-existing benchmark processes..."
    # Kill benchmark executables that might be lingering
    pkill -9 -f "benchmark_gds" 2>/dev/null || true
    pkill -9 -f "benchmark_mode" 2>/dev/null || true
    sleep 0.2
}

# ═══════════════════════════════════════════════════════════════
# Hardware Prerequisite Checks
# ═══════════════════════════════════════════════════════════════

# Check VFIO availability
check_vfio() {
    if [[ ! -c /dev/vfio/vfio ]]; then
        print_error "/dev/vfio/vfio not found"
        print_info "Run module 53's setup_vfio.sh to configure VFIO"
        return 1
    fi
    print_success "VFIO: OK"
    return 0
}

# Check environment variables
check_env_vars() {
    # Auto-load module 53 env exports when available
    if [[ -z "${NVME_BDF:-}" ]]; then
        if [[ -f /tmp/_nvme_test_env_dual.sh ]]; then
            source /tmp/_nvme_test_env_dual.sh
        fi
        if [[ -f /tmp/_nvme_test_env.sh ]]; then
            source /tmp/_nvme_test_env.sh
        fi
    fi

    # Backwards compatibility for secondary device variables
    if [[ -z "${NVME_BDF:-}" && -n "${NVME_BDF_2:-}" ]]; then
        NVME_BDF="${NVME_BDF_2}"
    fi
    if [[ -z "${NVME_BDF:-}" && -n "${NVME_BDF2:-}" ]]; then
        NVME_BDF="${NVME_BDF2}"
    fi

    if [[ -z "${NVME_BDF:-}" ]]; then
        print_error "NVME_BDF environment variable not set"
        print_info "Source the environment file: source /tmp/_nvme_test_env.sh"
        print_info "Or set manually:"
        print_info "  export NVME_BDF='0000:41:00.0'"
        print_info "  export NVME_NSID='1'"
        print_info "  export NVME_LBA_SIZE='512'"
        print_info "  export NVME_SLBA='1000000'"
        return 1
    fi

    print_success "NVMe Device: ${NVME_BDF}"
    print_success "Namespace: ${NVME_NSID}"
    print_success "LBA Size: ${NVME_LBA_SIZE} bytes"
    print_success "Starting LBA: ${NVME_SLBA}"
    return 0
}

# Check P2P module availability
check_p2p_module() {
    if [[ ! -c /dev/gpu_p2p_nvme ]]; then
        print_warning "/dev/gpu_p2p_nvme not found"
        print_warning "This mode requires GPU P2P module for GPU device buffer"
        print_warning ""
        print_info "Known Issue: NVIDIA P2P symbols may not be available"
        print_info "Driver builds but fails to load with 'Unknown symbol' errors"
        print_info ""
        print_info "To attempt loading:"
        print_info "  cd ${PROJECT_ROOT}/50.GPU-NVMe_Interaction/56.GPU_Queue_GPU_Buffer/driver"
        print_info "  make"
        print_info "  sudo insmod build/.../kernel/gpu_g2p_map_module_backend_nv.ko"
        print_info "  sudo insmod build/.../kernel/gpu_g2p_map_module.ko"
        return 1
    fi

    print_success "P2P Module: /dev/gpu_p2p_nvme found"
    return 0
}

# Check DBC capability (NVMe Doorbell Buffer Config)
check_dbc_capability() {
    local nvme_device="${NVME_BDF}"

    # Extract bus:device.function
    local bus_dev_func="${nvme_device##*:}"  # Remove domain
    local nvme_node="/dev/nvme$(lspci -D | grep "${nvme_device}" | grep -oP 'NVME \K[0-9]+')"

    if [[ ! -e "$nvme_node" ]]; then
        print_warning "Cannot find NVMe node for ${nvme_device}"
        print_info "DBC capability detection requires nvme-cli"
        return 1
    fi

    # Check OACS bit 8 (Doorbell Buffer Config supported)
    if command -v nvme &> /dev/null; then
        local oacs=$(sudo nvme id-ctrl "$nvme_node" 2>/dev/null | grep -oP 'oacs\s+:\s+0x\K[0-9a-f]+' || echo "0")
        local oacs_dec=$((16#$oacs))
        local dbc_bit=$((oacs_dec & 0x100))  # Bit 8

        if [[ $dbc_bit -ne 0 ]]; then
            print_success "DBC Capability: Supported (OACS bit 8 = 1)"
            return 0
        else
            print_warning "DBC Capability: NOT supported (OACS bit 8 = 0)"
            print_info "This device does not support NVMe Doorbell Buffer Config"
            return 1
        fi
    else
        print_warning "nvme-cli not installed, cannot check DBC capability"
        print_info "Install: sudo apt-get install nvme-cli"
        return 1
    fi
}

# ═══════════════════════════════════════════════════════════════
# Benchmark Execution
# ═══════════════════════════════════════════════════════════════

# Print mode banner
# Usage: print_mode_banner MODE_NUMBER "Mode Title"
print_mode_banner() {
    local mode=$1
    local title=$2

    echo ""
    print_info "════════════════════════════════════════════════════════"
    print_info "  Mode ${mode} Benchmark: ${title}"
    print_info "════════════════════════════════════════════════════════"
    echo ""
}

# Check benchmark binary exists
# Usage: check_benchmark_binary BINARY_PATH
check_benchmark_binary() {
    local binary=$1

    if [[ ! -f "$binary" ]]; then
        print_error "Benchmark binary not found: $binary"
        print_info "Build the project first:"
        print_info "  cd ${PROJECT_ROOT}"
        print_info "  cmake -B build -G Ninja"
        print_info "  ninja -C build"
        return 1
    fi

    print_success "Benchmark binary: $(basename $binary)"
    return 0
}

# Run benchmark with output capture
# Usage: run_benchmark BINARY_PATH [additional args...]
# Returns: Sets BENCHMARK_OUTPUT (temp file) and BENCHMARK_EXIT_CODE
run_benchmark() {
    local binary=$1
    shift  # Remove first argument, keep rest

    print_info "Running benchmark..."
    print_info "This may take 1-5 minutes depending on iterations"
    echo ""

    # Create temp file for output
    BENCHMARK_OUTPUT=$(mktemp)

    # Run benchmark
    sudo -E "$binary" "$@" 2>&1 | tee "$BENCHMARK_OUTPUT"
    BENCHMARK_EXIT_CODE=${PIPESTATUS[0]}

    echo ""
    print_success "════════════════════════════════════════════════════════"
    print_success "  Benchmark Complete"
    print_success "════════════════════════════════════════════════════════"
    echo ""
}

# Validate benchmark results
# Usage: validate_results MODE_NUMBER
# Reads from BENCHMARK_OUTPUT temp file
validate_results() {
    local mode=$1

    print_info "Validating performance metrics..."
    local validation_passed=true

    # Extract metrics from output
    local mean_latency=""
    local mean_iops=""
    local latency_line
    local iops_line

    latency_line=$(grep -E "Average latency[:=]" "$BENCHMARK_OUTPUT" 2>/dev/null | tail -1 || true)
    if [[ -n "$latency_line" ]]; then
        mean_latency=$(echo "$latency_line" | sed -E 's/.*[:=] *//' | tr -cd '0-9.')
    fi
    if [[ -z "$mean_latency" ]]; then
        mean_latency=$(grep -oP "Mean:\\s+\\K[0-9.]+" "$BENCHMARK_OUTPUT" 2>/dev/null | head -1 || true)
    fi

    iops_line=$(grep -E "IOPS[:=]" "$BENCHMARK_OUTPUT" 2>/dev/null | tail -1 || true)
    if [[ -n "$iops_line" ]]; then
        mean_iops=$(echo "$iops_line" | sed -E 's/.*[:=] *//' | tr -cd '0-9.' | sed -E 's/\..*//')
    fi
    if [[ -z "$mean_iops" ]]; then
        mean_iops=$(grep -Eo "IOPS[^0-9]*[0-9,]+(\\.[0-9]+)?" "$BENCHMARK_OUTPUT" 2>/dev/null | tail -1 | tr -cd '0-9.' | sed -E 's/\..*//' || true)
    fi

    # Latency validation
    if [[ -n "$mean_latency" ]]; then
        print_info "  Measured Latency: ${mean_latency} μs"

        # Mode-specific latency thresholds
        local latency_threshold
        case $mode in
            1) latency_threshold=10000 ;;  # Mode 1: < 10ms
            3) latency_threshold=100 ;;    # Mode 3: < 100μs (daemon)
            5) latency_threshold=10000 ;;  # Mode 5: < 10ms (GPU autonomy)
            6) latency_threshold=5000 ;;   # Mode 6: < 5ms (hardware DBC, better than Mode 5)
            *) latency_threshold=10000 ;;
        esac

        if command -v bc &> /dev/null; then
            if (( $(echo "$mean_latency < $latency_threshold" | bc -l) )); then
                print_success "  ✓ Latency check passed (< ${latency_threshold} μs)"
            else
                print_warning "  ⚠ Latency higher than expected (> ${latency_threshold} μs)"
                validation_passed=false
            fi
        fi
    else
        print_warning "  ⚠ Could not extract latency metrics"
    fi

    # IOPS validation
    if [[ -n "$mean_iops" ]]; then
        print_info "  Measured IOPS: ${mean_iops}"

        # Mode-specific IOPS thresholds
        local iops_threshold
        case $mode in
            1) iops_threshold=1000 ;;     # Mode 1: > 1K IOPS
            3) iops_threshold=100000 ;;   # Mode 3: > 100K IOPS (daemon)
            5) iops_threshold=1000 ;;     # Mode 5: > 1K IOPS (GPU autonomy)
            6) iops_threshold=5000 ;;     # Mode 6: > 5K IOPS (hardware DBC, better than Mode 5)
            *) iops_threshold=1000 ;;
        esac

        if (( mean_iops > iops_threshold )); then
            print_success "  ✓ IOPS check passed (> ${iops_threshold})"
        else
            print_warning "  ⚠ IOPS lower than expected (minimum ${iops_threshold})"
            validation_passed=false
        fi
    else
        print_warning "  ⚠ Could not extract IOPS metrics"
    fi

    # Check for test failures
    if grep -q "\[  FAILED  \]" "$BENCHMARK_OUTPUT" 2>/dev/null; then
        print_error "  ✗ Benchmark tests failed"
        validation_passed=false
    elif grep -q "\[  PASSED  \]" "$BENCHMARK_OUTPUT" 2>/dev/null; then
        print_success "  ✓ All benchmark tests passed"
    fi

    # Final validation result
    echo ""
    if [[ "$validation_passed" == "true" ]] && [[ "$BENCHMARK_EXIT_CODE" -eq 0 ]]; then
        print_success "════════════════════════════════════════════════════════"
        print_success "  Performance Validation: PASSED"
        print_success "════════════════════════════════════════════════════════"
    else
        print_warning "════════════════════════════════════════════════════════"
        print_warning "  Performance Validation: COMPLETED WITH WARNINGS"
        print_warning "════════════════════════════════════════════════════════"
        print_info "  Note: Performance may vary based on NVMe device and system configuration"
    fi

    # Cleanup
    rm -f "$BENCHMARK_OUTPUT"
    echo ""
}

# ═══════════════════════════════════════════════════════════════
# Mode-Specific Expected Performance
# ═══════════════════════════════════════════════════════════════

# Print expected performance for each mode
# Usage: print_expected_performance MODE_NUMBER
print_expected_performance() {
    local mode=$1

    print_info "Expected Performance (from README - Samsung S4LV008 + RTX A6000):"

    case $mode in
        1)
            print_info "  Latency: ~267 μs (P50: 255 μs, P99: 955 μs)"
            print_info "  IOPS: 3,614 (4KB reads)"
            print_info "  CPU Usage: 15-25% (one core, per I/O)"
            ;;
        2)
            print_info "  (Performance data not yet available)"
            print_info "  Expected: Similar to Mode 1 with daemon polling overhead"
            ;;
        3)
            print_info "  Latency: ~3.14 μs"
            print_info "  IOPS: 318,163 (mean), range 308K-333K"
            print_info "  CPU Usage: 5-8% (daemon only)"
            ;;
        4)
            print_info "  (Performance data not yet available)"
            print_info "  Expected: Similar to Mode 3 with hardware DBC support"
            ;;
        5)
            print_info "  Latency: ~550 μs (P50: 528 μs, P99: 1605 μs)"
            print_info "  IOPS: 5,396 (write-only), range 4.4K-6.1K"
            print_info "  CPU Usage: 5-8% (daemon only)"
            print_info "  GPU Autonomy: 90%"
            echo ""
            print_info "Comparison with Mode 3:"
            print_info "  Mode 3 (CPU commands): 3.14 μs, 318K IOPS"
            print_info "  Mode 5 (GPU commands): 550 μs, 5K IOPS"
            print_info "  Trade-off: Higher latency but TRUE GPU autonomy"
            ;;
        6)
            print_info "  (Performance data not yet available)"
            print_info "  Expected: Similar to Mode 5 but with HARDWARE DBC"
            print_info "  Key Difference: NVMe controller polls shadow buffer via DMA"
            print_info "  Benefits: No CPU daemon required, lower latency than Mode 5"
            print_info "  Requirements: DBC-capable NVMe (OACS bit 8) + P2P module"
            echo ""
            print_info "Hardware vs Software DBC:"
            print_info "  Mode 5 (Software): CPU daemon polls shadow, rings doorbell"
            print_info "  Mode 6 (Hardware): NVMe controller polls shadow directly"
            print_info "  Expected: Lower latency and higher IOPS than Mode 5"
            ;;
    esac
    echo ""
}
