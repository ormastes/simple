#!/bin/bash
# Run Mode 0 benchmark: Host + MMIO + Pageable Memory (BASELINE)
# CPU builds commands, regular pageable host memory, direct MMIO doorbells
# This is intentionally suboptimal to serve as a baseline for comparison

# Source common functions
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
source "${SCRIPT_DIR}/common.sh"

# Mode configuration
MODE_NUMBER=0
MODE_TITLE="Host + MMIO + Pageable Memory (BASELINE)"

# Print banner
print_mode_banner $MODE_NUMBER "$MODE_TITLE"

# Check prerequisites
print_info "Checking prerequisites..."

check_vfio || exit 1
check_env_vars || exit 1

# Mode 0 does NOT require P2P module (uses pageable host memory)
print_success "Mode 0: No P2P module required (uses pageable host memory)"
print_warning "Mode 0 uses PAGEABLE memory - performance will be SUBOPTIMAL!"

# Get benchmark binary
BENCHMARK_BIN=$(get_benchmark_binary $MODE_NUMBER)
check_benchmark_binary "$BENCHMARK_BIN" || exit 1

echo ""

# Run benchmark
print_info "This test performs 4KB NVMe reads, then runs a CUDA sum kernel each iteration (host loop)."
print_info "Traditional CPU-managed I/O with direct MMIO doorbells."
print_warning "Host-to-GPU transfers use PAGEABLE memory; expect slower copies than Mode 1."
echo ""

run_benchmark "$BENCHMARK_BIN" "$@"

# Print expected performance
print_expected_performance $MODE_NUMBER

# Validate results
validate_results $MODE_NUMBER

exit $BENCHMARK_EXIT_CODE
