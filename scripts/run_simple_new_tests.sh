#!/bin/bash
#
# Simple Test Runner with Crash Detection
# Runs Simple/SSpec test files with 5-minute timeout per file
# Logs start/end timestamps to detect crashes
#

set -e

# Configuration
BINARY="${1:-./target/debug/simple_old}"
LOG_DIR="log"
LOG_FILE="$LOG_DIR/simple_new_test.log"
TIMEOUT_SECONDS=300  # 5 minutes
MAX_PARALLEL=1       # Run tests sequentially for accurate crash detection

# Initialize counters
TOTAL_FILES=0
PASSED_FILES=0
FAILED_FILES=0
CRASHED_FILES=0
TIMED_OUT_FILES=0

# Create log directory
mkdir -p "$LOG_DIR"

# Clear log file
echo "# Simple Test Runner Log" > "$LOG_FILE"
echo "# Started: $(date '+%Y-%m-%d %H:%M:%S')" >> "$LOG_FILE"
echo "# Binary: $BINARY" >> "$LOG_FILE"
echo "# Timeout: ${TIMEOUT_SECONDS}s per file" >> "$LOG_FILE"
echo "" >> "$LOG_FILE"

log() {
    local timestamp=$(date '+%Y-%m-%d %H:%M:%S')
    echo "[$timestamp] $1" >> "$LOG_FILE"
    echo "[$timestamp] $1"
}

# Function to run a single test file with timeout
run_test_file() {
    local test_file="$1"

    TOTAL_FILES=$((TOTAL_FILES + 1))

    log "START TEST: $test_file"

    # Run test file with timeout
    local start_time=$(date +%s)
    local exit_code=0

    # Create a temporary file for output
    local tmp_output=$(mktemp)

    # Run with timeout
    timeout --kill-after=10 "$TIMEOUT_SECONDS" \
        "$BINARY" test "$test_file" > "$tmp_output" 2>&1 || exit_code=$?

    local end_time=$(date +%s)
    local duration=$((end_time - start_time))

    # Determine result
    local result=""
    if [ $exit_code -eq 0 ]; then
        result="PASS"
        PASSED_FILES=$((PASSED_FILES + 1))
    elif [ $exit_code -eq 124 ] || [ $exit_code -eq 137 ]; then
        result="TIMEOUT"
        TIMED_OUT_FILES=$((TIMED_OUT_FILES + 1))
    elif [ $exit_code -ge 128 ]; then
        # Killed by signal (crash)
        local signal=$((exit_code - 128))
        result="CRASH (signal $signal)"
        CRASHED_FILES=$((CRASHED_FILES + 1))
    else
        result="FAIL"
        FAILED_FILES=$((FAILED_FILES + 1))
    fi

    log "END TEST: $test_file ($result, ${duration}s)"

    # If crash, timeout, or failure, log last 30 lines of output
    if [ "$result" != "PASS" ]; then
        echo "--- Output for $test_file ---" >> "$LOG_FILE"
        tail -30 "$tmp_output" >> "$LOG_FILE" 2>/dev/null || true
        echo "--- End output ---" >> "$LOG_FILE"
        echo "" >> "$LOG_FILE"
    fi

    rm -f "$tmp_output"
}

# Main execution
log "Starting test run..."
log "Binary: $BINARY"

# Check if binary exists
if [ ! -x "$BINARY" ]; then
    log "ERROR: Binary not found or not executable: $BINARY"
    exit 1
fi

# Get unique test files
log "Collecting test files..."
TEST_FILES=$("$BINARY" test --list 2>&1 | grep "^/" | cut -d':' -f1 | sort -u || true)

if [ -z "$TEST_FILES" ]; then
    log "ERROR: No test files found"
    exit 1
fi

TOTAL_TEST_FILES=$(echo "$TEST_FILES" | wc -l)
log "Found $TOTAL_TEST_FILES unique test files"

# Run each test file
CURRENT=0
while IFS= read -r test_file; do
    CURRENT=$((CURRENT + 1))

    # Progress indicator
    echo ""
    echo "========================================"
    echo "[$CURRENT/$TOTAL_TEST_FILES] $test_file"
    echo "========================================"

    run_test_file "$test_file"

done <<< "$TEST_FILES"

# Generate summary
log ""
log "=========================================="
log "TEST RUN COMPLETE"
log "=========================================="
log "Total files:     $TOTAL_FILES"
log "Passed files:    $PASSED_FILES"
log "Failed files:    $FAILED_FILES"
log "Crashed files:   $CRASHED_FILES"
log "Timed out files: $TIMED_OUT_FILES"
log "=========================================="

# List crashed/timed-out tests
if [ $CRASHED_FILES -gt 0 ] || [ $TIMED_OUT_FILES -gt 0 ]; then
    log ""
    log "PROBLEM TEST FILES:"
    grep -E "(CRASH|TIMEOUT)" "$LOG_FILE" | grep "END TEST" >> "$LOG_FILE.summary" 2>/dev/null || true
    if [ -f "$LOG_FILE.summary" ]; then
        cat "$LOG_FILE.summary"
        rm -f "$LOG_FILE.summary"
    fi
fi

log ""
log "Finished: $(date '+%Y-%m-%d %H:%M:%S')"
log "Log file: $LOG_FILE"

# Exit with appropriate code
if [ $CRASHED_FILES -gt 0 ] || [ $TIMED_OUT_FILES -gt 0 ]; then
    exit 2
elif [ $FAILED_FILES -gt 0 ]; then
    exit 1
else
    exit 0
fi
