#!/bin/bash
# Run Mode 2 benchmark: Host Daemon + GPU Memory
# CPU builds commands, daemon polls GPU memory, requires P2P
# Based on module 57's benchmark_mode2_host_daemon_gpu_mem

# Source common functions
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
source "${SCRIPT_DIR}/common.sh"

# Mode configuration
MODE_NUMBER=2
MODE_TITLE="Host Daemon + GPU Memory"

# Print banner
print_mode_banner $MODE_NUMBER "$MODE_TITLE"

# Check prerequisites
print_info "Checking prerequisites..."

# Cleanup any pre-existing daemon/benchmark processes
cleanup_daemon_processes

check_vfio || exit 1
check_env_vars || exit 1

# Mode 2 REQUIRES P2P module (cannot fall back)
if ! check_p2p_module; then
    echo ""
    print_error "Cannot run Mode 2 without P2P module"
    exit 1
fi

# Get benchmark binary
BENCHMARK_BIN=$(get_benchmark_binary $MODE_NUMBER)
check_benchmark_binary "$BENCHMARK_BIN" || exit 1

echo ""

# Run benchmark
print_info "This test performs 4KB NVMe reads and launches a CUDA sum kernel per iteration (host loop)."
print_info "Host builds commands; daemon polls GPU memory (sq_tail)."
echo ""

run_benchmark "$BENCHMARK_BIN" "$@"

# Print expected performance
print_expected_performance $MODE_NUMBER

# Validate results
validate_results $MODE_NUMBER

exit $BENCHMARK_EXIT_CODE
