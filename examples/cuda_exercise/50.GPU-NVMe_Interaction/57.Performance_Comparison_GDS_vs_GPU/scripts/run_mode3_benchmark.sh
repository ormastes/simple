#!/bin/bash
# Run Mode 3 benchmark: Host + Daemon (GPU Buffer)
# CPU builds commands, daemon polls shadow buffer, GPU device buffer
# Based on module 56's benchmark_host_dbc_daemon_real

# Source common functions
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
source "${SCRIPT_DIR}/common.sh"

# Mode configuration
MODE_NUMBER=3
MODE_TITLE="Host + Daemon (GPU Device Buffer)"

# Print banner
print_mode_banner $MODE_NUMBER "$MODE_TITLE"

# Check prerequisites
print_info "Checking prerequisites..."

# Cleanup any pre-existing daemon/benchmark processes
cleanup_daemon_processes

check_vfio || exit 1
check_env_vars || exit 1

# Mode 3 requires P2P module for GPU buffer (but can fall back to pinned host memory)
if ! check_p2p_module; then
    print_warning ""
    print_warning "Mode 3 will use pinned host memory fallback (CPU pattern fill)"
    print_warning "For true GPU device buffer, fix P2P module loading"
    echo ""
fi

# Get benchmark binary
BENCHMARK_BIN=$(get_benchmark_binary $MODE_NUMBER)
check_benchmark_binary "$BENCHMARK_BIN" || exit 1

echo ""

# Run benchmark
print_info "Running Mode 3 benchmark (host loop: 4KB READ + CUDA sum each iteration)."
print_info "GPU buffer target; falls back to host→GPU copy if P2P is unavailable."
echo ""

run_benchmark "$BENCHMARK_BIN" "$@"

# Print expected performance
print_expected_performance $MODE_NUMBER

# Validate results
validate_results $MODE_NUMBER

exit $BENCHMARK_EXIT_CODE
