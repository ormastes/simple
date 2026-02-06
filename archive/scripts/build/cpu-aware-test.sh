#!/bin/bash
# CPU-aware test runner
# Automatically throttles test parallelism when system CPU usage is high
#
# Usage: ./scripts/cpu-aware-test.sh [test-args...]
# Example: ./scripts/cpu-aware-test.sh --workspace
#          ./scripts/cpu-aware-test.sh -p simple-driver

set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(dirname "$SCRIPT_DIR")"

# Default configuration (can be overridden by environment variables)
CPU_THROTTLE_THRESHOLD="${CPU_THROTTLE_THRESHOLD:-70}"
CPU_THROTTLE_THREADS="${CPU_THROTTLE_THREADS:-1}"

# Read threshold from simple.test.toml if available
if [[ -f "$PROJECT_ROOT/simple.test.toml" ]]; then
    TOML_THRESHOLD=$(grep -E "^threshold\s*=" "$PROJECT_ROOT/simple.test.toml" 2>/dev/null | head -1 | sed 's/.*=\s*//' | tr -d ' ')
    TOML_THREADS=$(grep -E "^throttled_threads\s*=" "$PROJECT_ROOT/simple.test.toml" 2>/dev/null | head -1 | sed 's/.*=\s*//' | tr -d ' ')

    [[ -n "$TOML_THRESHOLD" ]] && CPU_THROTTLE_THRESHOLD="$TOML_THRESHOLD"
    [[ -n "$TOML_THREADS" ]] && CPU_THROTTLE_THREADS="$TOML_THREADS"
fi

# Get current CPU usage (average across all cores)
get_cpu_usage() {
    # Use /proc/stat for accurate measurement
    local cpu_line1 cpu_line2
    local user1 nice1 system1 idle1 iowait1 irq1 softirq1
    local user2 nice2 system2 idle2 iowait2 irq2 softirq2

    read cpu_line1 < /proc/stat
    sleep 0.5
    read cpu_line2 < /proc/stat

    # Parse first sample
    read -r _ user1 nice1 system1 idle1 iowait1 irq1 softirq1 _ <<< "$cpu_line1"
    # Parse second sample
    read -r _ user2 nice2 system2 idle2 iowait2 irq2 softirq2 _ <<< "$cpu_line2"

    local total1=$((user1 + nice1 + system1 + idle1 + iowait1 + irq1 + softirq1))
    local total2=$((user2 + nice2 + system2 + idle2 + iowait2 + irq2 + softirq2))
    local idle_diff=$((idle2 - idle1))
    local total_diff=$((total2 - total1))

    if [[ $total_diff -eq 0 ]]; then
        echo 0
        return
    fi

    local usage=$(( (total_diff - idle_diff) * 100 / total_diff ))
    echo "$usage"
}

# Check CPU and set thread environment variables
configure_threads() {
    local cpu_usage
    cpu_usage=$(get_cpu_usage)

    echo "Current CPU usage: ${cpu_usage}% (threshold: ${CPU_THROTTLE_THRESHOLD}%)"

    if [[ "$cpu_usage" -ge "$CPU_THROTTLE_THRESHOLD" ]]; then
        echo "CPU usage exceeds threshold. Throttling to ${CPU_THROTTLE_THREADS} thread(s)."
        export RUST_TEST_THREADS="$CPU_THROTTLE_THREADS"
        export RAYON_NUM_THREADS="$CPU_THROTTLE_THREADS"
    else
        echo "CPU usage OK. Running with full parallelism."
        # Unset to allow default behavior (use all cores)
        unset RUST_TEST_THREADS
        unset RAYON_NUM_THREADS
    fi
}

# Main
configure_threads

echo "Running: cargo test $*"
echo "---"
exec cargo test "$@"
