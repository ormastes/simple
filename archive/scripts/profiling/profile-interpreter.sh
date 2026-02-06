#!/bin/bash
# Profile Simple interpreter with perf and generate flamegraph
#
# Usage:
#   ./script/profiling/profile-interpreter.sh <simple-script.spl>
#   ./script/profiling/profile-interpreter.sh --benchmark
#
# Requirements:
#   - perf (linux-perf-tools)
#   - flamegraph (cargo install flamegraph)
#
# Output:
#   - perf.data - raw perf data
#   - flamegraph.svg - interactive flamegraph visualization

set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "$SCRIPT_DIR/../.." && pwd)"

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
NC='\033[0m' # No Color

# Configuration
PERF_RECORD_FREQ=99  # Sampling frequency (Hz)
PERF_RECORD_TIME=10  # Recording time (seconds)

usage() {
    echo "Usage: $0 <simple-script.spl> [options]"
    echo ""
    echo "Options:"
    echo "  --benchmark          Profile benchmark workload instead of script"
    echo "  --freq=N             Sampling frequency (default: 99 Hz)"
    echo "  --time=N             Recording time (default: 10 seconds)"
    echo "  --output=FILE        Output flamegraph file (default: flamegraph.svg)"
    echo "  --keep-perf-data     Keep perf.data after generating flamegraph"
    echo ""
    echo "Examples:"
    echo "  $0 examples/fibonacci.spl"
    echo "  $0 --benchmark --time=30"
    echo "  $0 test.spl --freq=999 --output=test-profile.svg"
}

# Parse arguments
SCRIPT_FILE=""
MODE="script"
OUTPUT_FILE="flamegraph.svg"
KEEP_PERF_DATA=false

while [[ $# -gt 0 ]]; do
    case $1 in
        --benchmark)
            MODE="benchmark"
            shift
            ;;
        --freq=*)
            PERF_RECORD_FREQ="${1#*=}"
            shift
            ;;
        --time=*)
            PERF_RECORD_TIME="${1#*=}"
            shift
            ;;
        --output=*)
            OUTPUT_FILE="${1#*=}"
            shift
            ;;
        --keep-perf-data)
            KEEP_PERF_DATA=true
            shift
            ;;
        --help|-h)
            usage
            exit 0
            ;;
        *)
            if [[ -z "$SCRIPT_FILE" ]]; then
                SCRIPT_FILE="$1"
            else
                echo -e "${RED}Error: Unknown argument: $1${NC}"
                usage
                exit 1
            fi
            shift
            ;;
    esac
done

# Check requirements
check_command() {
    if ! command -v "$1" &> /dev/null; then
        echo -e "${RED}Error: $1 is not installed${NC}"
        echo "Install with: $2"
        exit 1
    fi
}

check_command perf "sudo apt-get install linux-tools-generic"
check_command flamegraph "cargo install flamegraph"

# Validate input
if [[ "$MODE" == "script" && -z "$SCRIPT_FILE" ]]; then
    echo -e "${RED}Error: Script file required${NC}"
    usage
    exit 1
fi

if [[ "$MODE" == "script" && ! -f "$SCRIPT_FILE" ]]; then
    echo -e "${RED}Error: Script file not found: $SCRIPT_FILE${NC}"
    exit 1
fi

# Build optimized runtime
echo -e "${GREEN}Building optimized runtime...${NC}"
cd "$REPO_ROOT/rust"
cargo build --release --quiet
RUNTIME="$REPO_ROOT/rust/target/release/simple"

# Prepare profiling command
if [[ "$MODE" == "benchmark" ]]; then
    # Create benchmark script
    BENCH_SCRIPT="/tmp/bench_profile.spl"
    cat > "$BENCH_SCRIPT" <<'EOF'
fn fibonacci(n):
    if n <= 1:
        n
    else:
        fibonacci(n - 1) + fibonacci(n - 2)

fn factorial(n):
    if n <= 1:
        1
    else:
        n * factorial(n - 1)

fn sum_array(arr):
    var sum = 0
    for x in arr:
        sum = sum + x
    sum

fn main():
    # Compute intensive workload
    for i in 0..100:
        val fib_result = fibonacci(15)
        val fact_result = factorial(10)
        val arr = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]
        val sum = sum_array(arr)
    0

main()
EOF
    SCRIPT_FILE="$BENCH_SCRIPT"
    echo -e "${YELLOW}Using benchmark workload${NC}"
fi

# Run profiling
echo -e "${GREEN}Profiling: $SCRIPT_FILE${NC}"
echo -e "${YELLOW}Frequency: ${PERF_RECORD_FREQ} Hz, Duration: ${PERF_RECORD_TIME}s${NC}"

# Check if we can use perf without sudo
if perf record -o /dev/null -F "$PERF_RECORD_FREQ" -- sleep 0.1 &>/dev/null; then
    SUDO=""
else
    echo -e "${YELLOW}Note: perf requires elevated privileges${NC}"
    SUDO="sudo"
fi

# Record with perf
$SUDO perf record \
    -F "$PERF_RECORD_FREQ" \
    -g \
    --call-graph dwarf \
    -o perf.data \
    -- "$RUNTIME" "$SCRIPT_FILE" \
    || {
        echo -e "${RED}Profiling failed${NC}"
        exit 1
    }

# Generate flamegraph
echo -e "${GREEN}Generating flamegraph: $OUTPUT_FILE${NC}"
$SUDO perf script | flamegraph > "$OUTPUT_FILE"

# Cleanup
if [[ "$KEEP_PERF_DATA" == false ]]; then
    $SUDO rm -f perf.data perf.data.old
    echo -e "${YELLOW}Cleaned up perf.data${NC}"
fi

if [[ "$MODE" == "benchmark" ]]; then
    rm -f "$BENCH_SCRIPT"
fi

# Show results
echo ""
echo -e "${GREEN}✓ Profiling complete!${NC}"
echo -e "  Flamegraph: ${YELLOW}$OUTPUT_FILE${NC}"
echo ""
echo "Open with: firefox $OUTPUT_FILE"
echo "  or:      chromium $OUTPUT_FILE"
