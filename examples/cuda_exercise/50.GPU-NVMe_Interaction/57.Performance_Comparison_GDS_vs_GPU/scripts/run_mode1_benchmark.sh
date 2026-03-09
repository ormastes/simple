#!/bin/bash
# Run Mode 1 benchmark: Host + MMIO (Baseline)
# CPU builds commands, pinned host memory, direct MMIO doorbells
# Based on module 56's benchmark_host_queue_real

# Source common functions
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
source "${SCRIPT_DIR}/common.sh"

# Mode configuration
MODE_NUMBER=1
MODE_TITLE="Host + MMIO (Baseline)"

# Print banner
print_mode_banner $MODE_NUMBER "$MODE_TITLE"

# Check prerequisites
print_info "Checking prerequisites..."

check_vfio || exit 1
check_env_vars || exit 1

# Mode 1 does NOT require P2P module (uses pinned host memory)
print_success "Mode 1: No P2P module required (uses pinned host memory)"

# Get benchmark binary
BENCHMARK_BIN=$(get_benchmark_binary $MODE_NUMBER)
check_benchmark_binary "$BENCHMARK_BIN" || exit 1

echo ""

# Run benchmark
print_info "This test performs 4KB NVMe reads and launches a CUDA sum kernel per iteration (host loop)."
print_info "Pinned host buffer only (no GPU buffer); traditional CPU-managed I/O with direct MMIO doorbells."
echo ""

run_benchmark "$BENCHMARK_BIN" "$@"

# Print expected performance
print_expected_performance $MODE_NUMBER

# Validate results
validate_results $MODE_NUMBER

exit $BENCHMARK_EXIT_CODE
