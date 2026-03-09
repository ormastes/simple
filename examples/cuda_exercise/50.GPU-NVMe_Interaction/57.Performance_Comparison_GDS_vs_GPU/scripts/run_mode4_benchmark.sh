#!/bin/bash
# Run Mode 4 benchmark: DBC Shadow + GPU
# GPU builds commands, NVMe polls DBC shadow (zero CPU), requires DBC hardware
# Based on module 57's benchmark_mode4_dbc_shadow_gpu

# Source common functions
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
source "${SCRIPT_DIR}/common.sh"

# Mode configuration
MODE_NUMBER=4
MODE_TITLE="DBC Shadow + GPU"

# Print banner
print_mode_banner $MODE_NUMBER "$MODE_TITLE"

# Check prerequisites
print_info "Checking prerequisites..."

check_vfio || exit 1
check_env_vars || exit 1

# Mode 4 REQUIRES DBC capability
print_info "Checking DBC capability..."
if ! check_dbc_capability; then
    echo ""
    print_info "Mode 4 requires DBC-capable NVMe controller"
    print_info "Your device does not support Doorbell Buffer Config (DBC)"
    print_info ""
    print_info "Skipping Mode 4 benchmark (this is expected on most hardware)"
    print_info "Use Mode 3 (Host + Daemon) or Mode 5 (GPU + Daemon) instead"
    exit 0
fi

# Mode 4 REQUIRES P2P module (cannot fall back)
if ! check_p2p_module; then
    echo ""
    print_error "Cannot run Mode 4 without P2P module"
    exit 1
fi

# Get benchmark binary
BENCHMARK_BIN=$(get_benchmark_binary $MODE_NUMBER)
check_benchmark_binary "$BENCHMARK_BIN" || exit 1

echo ""

# Run benchmark
print_info "This test seeds a 4KB NVMe read, then a single CUDA kernel loops 100k iterations summing on-GPU."
print_info "GPU builds commands; NVMe polls DBC shadow buffer (zero CPU doorbells)."
echo ""

run_benchmark "$BENCHMARK_BIN" "$@"

# Print expected performance
print_expected_performance $MODE_NUMBER

# Validate results
validate_results $MODE_NUMBER

exit $BENCHMARK_EXIT_CODE
