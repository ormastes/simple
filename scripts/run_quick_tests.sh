#!/bin/bash
#
# Quick Test Runner - runs first N test files to verify everything works
#

set -e

BINARY="./target/debug/simple_old"
LOG_DIR="log"
LOG_FILE="$LOG_DIR/quick_test.log"
TIMEOUT_SECONDS=120  # 2 minutes per file for quick tests
NUM_FILES=${1:-20}   # Default to 20 files

# Initialize counters
TOTAL_FILES=0
PASSED_FILES=0
FAILED_FILES=0
CRASHED_FILES=0
TIMED_OUT_FILES=0

mkdir -p "$LOG_DIR"

echo "# Quick Test Run - $NUM_FILES files" > "$LOG_FILE"
echo "# Started: $(date '+%Y-%m-%d %H:%M:%S')" >> "$LOG_FILE"
echo "" >> "$LOG_FILE"

log() {
    local timestamp=$(date '+%Y-%m-%d %H:%M:%S')
    echo "[$timestamp] $1" >> "$LOG_FILE"
    echo "[$timestamp] $1"
}

run_test_file() {
    local test_file="$1"
    TOTAL_FILES=$((TOTAL_FILES + 1))

    log "START TEST: $test_file"

    local start_time=$(date +%s)
    local exit_code=0
    local tmp_output=$(mktemp)

    timeout --kill-after=10 "$TIMEOUT_SECONDS" \
        "$BINARY" test "$test_file" > "$tmp_output" 2>&1 || exit_code=$?

    local end_time=$(date +%s)
    local duration=$((end_time - start_time))

    local result=""
    if [ $exit_code -eq 0 ]; then
        result="PASS"
        PASSED_FILES=$((PASSED_FILES + 1))
    elif [ $exit_code -eq 124 ] || [ $exit_code -eq 137 ]; then
        result="TIMEOUT"
        TIMED_OUT_FILES=$((TIMED_OUT_FILES + 1))
    elif [ $exit_code -ge 128 ]; then
        local signal=$((exit_code - 128))
        result="CRASH (signal $signal)"
        CRASHED_FILES=$((CRASHED_FILES + 1))
    else
        result="FAIL"
        FAILED_FILES=$((FAILED_FILES + 1))
    fi

    log "END TEST: $test_file ($result, ${duration}s)"

    if [ "$result" != "PASS" ]; then
        echo "--- Output for $test_file ---" >> "$LOG_FILE"
        tail -20 "$tmp_output" >> "$LOG_FILE" 2>/dev/null || true
        echo "--- End output ---" >> "$LOG_FILE"
    fi

    rm -f "$tmp_output"
}

log "Starting quick test run ($NUM_FILES files)..."

TEST_FILES=$("$BINARY" test --list 2>&1 | grep "^/" | cut -d':' -f1 | sort -u | head -n "$NUM_FILES")

if [ -z "$TEST_FILES" ]; then
    log "ERROR: No test files found"
    exit 1
fi

CURRENT=0
while IFS= read -r test_file; do
    CURRENT=$((CURRENT + 1))
    echo "[$CURRENT/$NUM_FILES] $(basename "$test_file")"
    run_test_file "$test_file"
done <<< "$TEST_FILES"

log ""
log "=========================================="
log "QUICK TEST RUN COMPLETE"
log "=========================================="
log "Total files:     $TOTAL_FILES"
log "Passed files:    $PASSED_FILES"
log "Failed files:    $FAILED_FILES"
log "Crashed files:   $CRASHED_FILES"
log "Timed out files: $TIMED_OUT_FILES"
log "=========================================="

if [ $CRASHED_FILES -gt 0 ] || [ $TIMED_OUT_FILES -gt 0 ]; then
    log ""
    log "PROBLEM TEST FILES:"
    grep -E "(CRASH|TIMEOUT)" "$LOG_FILE" | grep "END TEST"
fi

log ""
log "Finished: $(date '+%Y-%m-%d %H:%M:%S')"
log "Log file: $LOG_FILE"
