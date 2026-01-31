#!/bin/bash
# Capture bootstrap debug output for analysis

set -e

OUTPUT_FILE="target/bootstrap_debug_$(date +%Y%m%d_%H%M%S).log"

echo "Capturing bootstrap debug output to: $OUTPUT_FILE"
echo "This will take a while..."
echo ""

# Clean bootstrap directory
rm -rf target/bootstrap
mkdir -p target/bootstrap

# Run stage 1 only
echo "=== Running Bootstrap Stage 1 ===" | tee "$OUTPUT_FILE"
./target/debug/simple_old compile simple/compiler/main.spl -o target/bootstrap/simple_new1 --native 2>&1 | tee -a "$OUTPUT_FILE"

echo ""
echo "=== Extracting Debug Messages ===" | tee -a "$OUTPUT_FILE"

# Extract relevant debug messages
echo ""
echo "Phase 3 Debug:" | tee -a "$OUTPUT_FILE"
grep -E "\[phase3\]" "$OUTPUT_FILE" | tail -20

echo ""
echo "Compile Debug:" | tee -a "$OUTPUT_FILE"
grep -E "\[compile\].*phase 3" "$OUTPUT_FILE" | tail -10

echo ""
echo "AOT Debug:" | tee -a "$OUTPUT_FILE"
grep -E "\[aot\]" "$OUTPUT_FILE" | tail -10

echo ""
echo "Full log saved to: $OUTPUT_FILE"
