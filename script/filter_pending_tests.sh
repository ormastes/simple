#!/bin/bash
# Filter Pending Tests
#
# Identifies tests marked @pending or @skip and excludes them from test runs

set -e

TARGET_DIR="${1:-test/lib}"

echo "=== Pending Test Filter ==="
echo "Scanning: $TARGET_DIR"
echo ""

# Find all spec files
ALL_SPECS=$(find "$TARGET_DIR" -name "*_spec.spl" -type f | wc -l)

# Find pending/skip files
PENDING=$(grep -l "^# @pending\|^# @skip" "$TARGET_DIR" -r --include="*_spec.spl" 2>/dev/null | wc -l)

# Calculate non-pending
NON_PENDING=$((ALL_SPECS - PENDING))

echo "Summary:"
echo "  Total spec files: $ALL_SPECS"
echo "  Pending/Skip: $PENDING ($((PENDING * 100 / ALL_SPECS))%)"
echo "  Active (non-pending): $NON_PENDING ($((NON_PENDING * 100 / ALL_SPECS))%)"
echo ""

# List pending files
echo "Pending/Skip files:"
grep -l "^# @pending\|^# @skip" "$TARGET_DIR" -r --include="*_spec.spl" 2>/dev/null | head -20
echo "..."
echo ""

# Create exclusion list
EXCLUDE_FILE="build/pending_tests.txt"
mkdir -p build
grep -l "^# @pending\|^# @skip" "$TARGET_DIR" -r --include="*_spec.spl" 2>/dev/null > "$EXCLUDE_FILE"

echo "Exclusion list saved to: $EXCLUDE_FILE"
echo ""

# Create active test list
ACTIVE_FILE="build/active_tests.txt"
find "$TARGET_DIR" -name "*_spec.spl" -type f > /tmp/all_tests.txt
grep -l "^# @pending\|^# @skip" "$TARGET_DIR" -r --include="*_spec.spl" 2>/dev/null > /tmp/pending_tests.txt || touch /tmp/pending_tests.txt
comm -23 <(sort /tmp/all_tests.txt) <(sort /tmp/pending_tests.txt) > "$ACTIVE_FILE"

ACTIVE_COUNT=$(wc -l < "$ACTIVE_FILE")
echo "Active test list saved to: $ACTIVE_FILE ($ACTIVE_COUNT files)"
