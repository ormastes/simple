# Phase 2 Execution Script
# High Priority Files (1500-2000 lines)

set -e

echo "======================================="
echo "Phase 2: High Priority Refactoring"
echo "Target: 10 files (1500-2000 lines each)"
echo "======================================="
echo ""

# Phase 2 targets
declare -a TARGETS=(
    "red_black_tree_utils:1764"
    "rsa_utils:1759"
    "regex_engine_utils:1686"
    "optimization_utils:1664"
    "linear_algebra_utils:1648"
    "cert_utils:1621"
    "compression_utils:1606"
    "xml_utils:1592"
    "markdown_utils:1566"
    "statistical_utils:1554"
)

# Function: Analyze file structure
analyze_file() {
    local utils_file=$1
    local expected_lines=$2
    
    if [ ! -f "src/std/${utils_file}.spl" ]; then
        echo "  ❌ File not found"
        return 1
    fi
    
    local actual_lines=$(wc -l < "src/std/${utils_file}.spl")
    echo "  📊 Actual: $actual_lines lines (expected: $expected_lines)"
    
    # Check if already a facade
    if [ $actual_lines -lt 100 ]; then
        echo "  ✅ Already a facade"
        return 0
    fi
    
    # Count function definitions
    local fn_count=$(grep -c "^fn " "src/std/${utils_file}.spl" 2>/dev/null || echo 0)
    echo "  📝 Functions: $fn_count"
    
    # Look for category comments
    local categories=$(grep -c "^# ---" "src/std/${utils_file}.spl" 2>/dev/null || echo 0)
    echo "  📂 Categories: $categories"
    
    return 0
}

# Main loop
SUCCESS=0
FAILED=0
ALREADY_DONE=0

for target in "${TARGETS[@]}"; do
    IFS=':' read -r utils_name expected_lines <<< "$target"
    
    echo "[$utils_name]"
    if analyze_file "$utils_name" "$expected_lines"; then
        ((SUCCESS++))
    else
        ((FAILED++))
    fi
    echo ""
done

# Summary
echo "======================================="
echo "Phase 2 Analysis Summary"
echo "======================================="
echo "Total targets: ${#TARGETS[@]}"
echo "Analyzed: $SUCCESS"
echo "Failed: $FAILED"
echo ""
echo "✅ Analysis complete. Ready for refactoring."
