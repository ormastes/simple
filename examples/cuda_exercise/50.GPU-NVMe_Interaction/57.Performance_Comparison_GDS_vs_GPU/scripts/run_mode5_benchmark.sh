#!/bin/bash
# Run Mode 5 benchmark: GPU + Daemon (GPU Command Building)
# GPU builds commands, daemon polls shadow buffer, true GPU autonomy
# Based on module 56's benchmark_dbc_daemon_gpu_command

# Source common functions
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
source "${SCRIPT_DIR}/common.sh"

# Mode configuration
MODE_NUMBER=5
MODE_TITLE="GPU + Daemon (GPU Command Building)"

# Print banner
print_mode_banner $MODE_NUMBER "$MODE_TITLE"

# Check prerequisites
print_info "Checking prerequisites..."

# Cleanup any pre-existing daemon/benchmark processes
cleanup_daemon_processes

check_vfio || exit 1
check_env_vars || exit 1

# Mode 5 requires P2P module for GPU buffer (but can fall back to pinned host memory)
if ! check_p2p_module; then
    print_warning ""
    print_warning "Mode 5 will use pinned host memory fallback"
    print_warning "GPU still builds commands autonomously (90% GPU autonomy)"
    print_warning "For true GPU device buffer, fix P2P module loading"
    echo ""
fi

# Get benchmark binary
BENCHMARK_BIN=$(get_benchmark_binary $MODE_NUMBER)
check_benchmark_binary "$BENCHMARK_BIN" || exit 1

echo ""

# Run benchmark
print_info "Running Mode 5 benchmark (GPU-initiated I/O)."
print_info "Single CUDA kernel loops 100k iterations summing on-GPU; daemon mirrors doorbells."
echo ""

run_benchmark "$BENCHMARK_BIN" "$@"

# Print expected performance
print_expected_performance $MODE_NUMBER

# Validate results
validate_results $MODE_NUMBER

exit $BENCHMARK_EXIT_CODE
