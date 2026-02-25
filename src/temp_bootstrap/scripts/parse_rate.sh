#!/bin/bash
# Parse rate checker for Simple compiler .spl files
# Usage: ./scripts/parse_rate.sh [--verbose] [--failing]
#
# Uses the parse_check binary (from simple-driver crate) which reads
# file paths from stdin and reports parse success/failure for each.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
BOOTSTRAP_DIR="$(dirname "$SCRIPT_DIR")"
COMPILER_DIR="$BOOTSTRAP_DIR/../../src/compiler"

# Build if needed
if [ ! -f "$BOOTSTRAP_DIR/target/release/parse_check" ]; then
    echo "Building bootstrap compiler..."
    (cd "$BOOTSTRAP_DIR" && cargo build --release -p simple-driver)
fi

DRIVER="$BOOTSTRAP_DIR/target/release/parse_check"
VERBOSE=false
SHOW_FAILING=false

for arg in "$@"; do
    case "$arg" in
        --verbose|-v) VERBOSE=true ;;
        --failing|-f) SHOW_FAILING=true ;;
    esac
done

SUCCESS=0
FAIL=0
FAILING_FILES=()

for f in $(find "$COMPILER_DIR" -name "*.spl" | sort); do
    REL=$(realpath --relative-to="$COMPILER_DIR" "$f")
    if echo "$f" | timeout 10 "$DRIVER" > /dev/null 2>&1; then
        SUCCESS=$((SUCCESS+1))
        if $VERBOSE; then echo "  OK: $REL"; fi
    else
        FAIL=$((FAIL+1))
        FAILING_FILES+=("$REL")
        if $VERBOSE; then echo "FAIL: $REL"; fi
    fi
done

TOTAL=$((SUCCESS+FAIL))
if [ "$TOTAL" -gt 0 ]; then
    RATE=$((SUCCESS * 100 / TOTAL))
else
    RATE=0
fi

echo ""
echo "========================================="
echo "Parse Rate: $SUCCESS/$TOTAL ($RATE%)"
echo "  Passing: $SUCCESS"
echo "  Failing: $FAIL"
echo "========================================="

if $SHOW_FAILING && [ ${#FAILING_FILES[@]} -gt 0 ]; then
    echo ""
    echo "Failing files:"
    for f in "${FAILING_FILES[@]}"; do
        echo "  $f"
    done
fi

if [ "$RATE" -lt 90 ]; then
    echo ""
    echo "WARNING: Parse rate below 90% threshold"
    exit 1
fi
