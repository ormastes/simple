#!/bin/bash
# Run Mode 6 benchmark: GPU + Hardware DBC (Hardware-Polled Shadow Doorbell)
# GPU builds commands, NVMe controller polls shadow buffer via DMA
# Requires DBC-capable NVMe controller (OACS bit 8 set)

# Source common functions
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
source "${SCRIPT_DIR}/common.sh"

# Mode configuration
MODE_NUMBER=6
MODE_TITLE="GPU + Hardware DBC (Hardware-Polled)"

# Print banner
print_mode_banner $MODE_NUMBER "$MODE_TITLE"

# Check prerequisites
print_info "Checking prerequisites..."

# Cleanup any pre-existing daemon/benchmark processes
cleanup_daemon_processes

check_vfio || exit 1
check_env_vars || exit 1

# Mode 6 REQUIRES DBC-capable NVMe device
echo ""
print_warning "Mode 6 requires a DBC-capable NVMe controller (OACS bit 8 set)"
print_warning "Run detect_dbc_support utility to check your devices:"
print_warning "  cd 53.NVMe_VFIO_Host_Layer/test/util && ./detect_dbc_support"
echo ""

# Mode 6 prefers P2P module for GPU buffer mapping, but fallback should still run.
P2P_FALLBACK_ALLOWED="${ALLOW_P2P_FALLBACK:-1}"
if ! check_p2p_module; then
    if [[ "${P2P_FALLBACK_ALLOWED}" == "1" ]]; then
        print_warning "P2P module missing - continuing with pinned host fallback (lower perf, but should still run)"
        export ALLOW_P2P_FALLBACK=1
    else
        print_error "Mode 6 REQUIRES P2P module for GPU buffer DMA mapping"
        print_error "Load the P2P kernel module or set ALLOW_P2P_FALLBACK=1 to use pinned host fallback"
        exit 1
    fi
fi

# PM9A1 firmware hides OACS bit 8; force DBC detection unless explicitly disabled
export NVME_FORCE_DBC="${NVME_FORCE_DBC:-1}"

# Get benchmark binary
BENCHMARK_BIN=$(get_benchmark_binary $MODE_NUMBER)
check_benchmark_binary "$BENCHMARK_BIN" || exit 1

echo ""

# Run benchmark
print_info "Running Mode 6 benchmark (Hardware DBC)..."
print_info "Single CUDA kernel loops 100k iterations summing on-GPU; NVMe hardware should poll the shadow buffer."
print_info "If hardware DBC is absent, use RUN_SHADOW_DB_CONTROLLER=1 to mirror doorbells in software."
echo ""

# Optional software mirror for shadow doorbells (host-side) when hardware polling is absent.
# Set RUN_SHADOW_DB_CONTROLLER=1 to enable; requires test helper build of ShadowDbControllerTask.
if [[ "${RUN_SHADOW_DB_CONTROLLER:-0}" == "1" ]]; then
    print_warning "Starting host-side ShadowDbController daemon to mirror shadow DB -> MMIO (safety net)"
    # Build and invoke the helper binary if available
    CONTROLLER_BIN="${BUILD_DIR}/50.GPU-NVMe_Interaction/53.NVMe_VFIO_Host_Layer/test/helper/tools/shadow_db_controller_runner"
    if [[ -x "${CONTROLLER_BIN}" ]]; then
        "${CONTROLLER_BIN}" "${NVME_BDF}" "${NVME_NSID}" "${NVME_LBA_SIZE}" "${NVME_SLBA}" &
        CONTROLLER_PID=$!
        print_info "Shadow DB controller daemon PID: ${CONTROLLER_PID}"
    else
        print_warning "Shadow DB controller runner not built; skipping (expected at ${CONTROLLER_BIN})"
    fi
fi

run_benchmark "$BENCHMARK_BIN" "$@"

# Print expected performance
print_expected_performance $MODE_NUMBER

# Validate results
validate_results $MODE_NUMBER

# Cleanup controller daemon if started
if [[ -n "${CONTROLLER_PID:-}" ]]; then
    print_info "Stopping ShadowDbController daemon (pid=${CONTROLLER_PID})"
    kill "${CONTROLLER_PID}" >/dev/null 2>&1 || true
    wait "${CONTROLLER_PID}" 2>/dev/null || true
fi

exit $BENCHMARK_EXIT_CODE
